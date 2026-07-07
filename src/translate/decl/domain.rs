//! Lower a Silver `domain` declaration to its `vmir::Domain` stub, each of
//! its (bodyless) domain functions to a `vmir::Function`, and each of its
//! axioms to a `vmir::Axiom`. One `DomainTranslator` owns the domain
//! stub *and* every function/axiom slot the domain declares.

use std::collections::HashMap;
use std::marker::PhantomData;

use lasso::Spur;

use crate::translate::GenericSig;
use crate::translate::lower_type;
use crate::translate::{DeclSlot, Declarator, Definer};
use crate::translate::{Declared, Metaed, TranslationContext, TranslationError, pure_exp};
use crate::viper::typed;
use crate::vmir;

pub(crate) struct DomainTranslator<'a, P = Declared> {
    src: &'a typed::Domain,
    silver_name: Spur,
    generics: Vec<Spur>,
    slot: DeclSlot<vmir::Domain>,
    /// One entry per domain function, parallel to `src.functions`: its reserved
    /// `Function` slot and the subset of the domain's type parameters the
    /// function actually mentions in its signature (order of first appearance).
    /// A parameter the function never uses is dropped — it is irrelevant to the
    /// function's meaning and cannot be inferred at a call site — so the lowered
    /// function's `ty_params` and `Generic(i)` indices count only the used ones.
    fn_slots: Vec<(DeclSlot<vmir::Function>, Vec<Spur>)>,
    /// One slot per axiom, parallel to `src.axioms`. An anonymous axiom's slot
    /// is registered under the generated name `{domain}#axiom{i}` (`#` marks a
    /// generated member); axioms are not callable, so no `name_map` entry.
    axiom_slots: Vec<DeclSlot<vmir::Axiom>>,
    /// One inner `Vec` per axiom (parallel to `src.axioms`), holding the
    /// pre-allocated occurrence slots for that axiom's top-level `forall`s, in
    /// preorder. Each is registered as `{axiom}#quant{j}`; not callable, so no
    /// `name_map` entry — the occurrence call carries the `MemberId` directly.
    quant_slots: Vec<Vec<(vmir::MemberId, DeclSlot<vmir::Quantifier>)>>,
    _p: PhantomData<P>,
}

/// Record in `out` (order of first appearance, deduped) every member of
/// `generics` occurring in `ty`, recursing into type arguments.
fn collect_generics(ty: &typed::Type, generics: &[Spur], out: &mut Vec<Spur>) {
    use typed::BuiltinCollection as C;
    match ty {
        typed::Type::Generic(id) => {
            if generics.contains(&id.0) && !out.contains(&id.0) {
                out.push(id.0);
            }
        }
        typed::Type::Domain(_, args) => {
            for a in args {
                collect_generics(a, generics, out);
            }
        }
        typed::Type::Collection(c) => match c {
            C::Seq(t) | C::Set(t) | C::MultiSet(t) => collect_generics(t, generics, out),
            C::Map(k, v) => {
                collect_generics(k, generics, out);
                collect_generics(v, generics, out);
            }
        },
        typed::Type::Bool | typed::Type::Int | typed::Type::Real | typed::Type::Ref => {}
    }
}

/// The subset of `generics` that occur anywhere in `params`/`ret`, in order of
/// first appearance. A domain function is implicitly parameterized by all of
/// its domain's type parameters, but one it never mentions is dropped so the
/// lowered function is (correctly) monomorphic in that parameter.
fn used_generics(generics: &[Spur], params: &[typed::TypedIdent], ret: &typed::Type) -> Vec<Spur> {
    let mut out = Vec::new();
    for p in params {
        collect_generics(&p.ty, generics, &mut out);
    }
    collect_generics(ret, generics, &mut out);
    out
}

/// The subset of `generics` an axiom expression mentions, in order of first
/// appearance — the axiom's own type parameters. Every instantiated type at a
/// call inside the expression is recoverable from some node's synthesized
/// type (arguments carry the params, the call node the result), so walking the
/// `ty` of every node covers all type-argument positions.
fn used_generics_in_exp(
    exp: &typed::TypedPureExp<typed::AxiomExt>,
    generics: &[Spur],
    out: &mut Vec<Spur>,
) {
    use typed::PureExpKind as P;
    collect_generics(&exp.ty, generics, out);
    let mut walk_call = |call: &typed::Call<typed::AxiomExt>| {
        for a in &call.args {
            used_generics_in_exp(a, generics, out);
        }
    };
    match exp.exp.as_ref() {
        P::Ident(_) | P::Const(_) => {}
        P::Unary(_, e) | P::AdtDestructor(e, _) | P::AdtDiscriminator(e, _) => {
            used_generics_in_exp(e, generics, out)
        }
        P::Binary(_, l, r) => {
            used_generics_in_exp(l, generics, out);
            used_generics_in_exp(r, generics, out);
        }
        P::Ternary { if_, then, else_ } => {
            used_generics_in_exp(if_, generics, out);
            used_generics_in_exp(then, generics, out);
            used_generics_in_exp(else_, generics, out);
        }
        P::LetIn { value, exp, .. } => {
            used_generics_in_exp(value, generics, out);
            used_generics_in_exp(exp, generics, out);
        }
        P::DomainFunctionCall(call) | P::AdtConstructor(call) => walk_call(call),
        P::Ext(typed::AxiomExt::FunctionCall(call)) => walk_call(call),
        P::Ext(typed::AxiomExt::Forall(q)) => {
            for group in &q.triggers {
                for t in group {
                    used_generics_in_exp(t, generics, out);
                }
            }
            used_generics_in_exp(&q.body, generics, out);
        }
    }
}

/// The number of `forall`s in an axiom expression, **including** those nested
/// inside another `forall`'s body. Each contributes one occurrence slot; the
/// preorder here matches the order lowering consumes ids (a `forall`'s own id
/// precedes its body's). Triggers are not descended — they are validated, never
/// lowered, so they consume no ids.
fn count_foralls(exp: &typed::TypedPureExp<typed::AxiomExt>) -> usize {
    use typed::PureExpKind as P;
    match exp.exp.as_ref() {
        P::Ident(_) | P::Const(_) => 0,
        P::Unary(_, e) | P::AdtDestructor(e, _) | P::AdtDiscriminator(e, _) => count_foralls(e),
        P::Binary(_, l, r) => count_foralls(l) + count_foralls(r),
        P::Ternary { if_, then, else_ } => {
            count_foralls(if_) + count_foralls(then) + count_foralls(else_)
        }
        P::LetIn { value, exp, .. } => count_foralls(value) + count_foralls(exp),
        P::DomainFunctionCall(call) | P::AdtConstructor(call) => {
            call.args.iter().map(count_foralls).sum()
        }
        P::Ext(typed::AxiomExt::FunctionCall(call)) => call.args.iter().map(count_foralls).sum(),
        P::Ext(typed::AxiomExt::Forall(q)) => 1 + count_foralls(&q.body),
    }
}

impl<'a> DomainTranslator<'a, Declared> {
    /// Reserve the domain stub + a `Function` slot per domain function, and
    /// publish every `name_map` entry (and each generic function's declared
    /// signature). A domain function's param/ret types are *not* lowered here —
    /// they may reference any ADT/domain by id, so lowering waits for `define`.
    pub(crate) fn declare(
        d: &'a typed::Domain,
        ctx: &mut TranslationContext<'_>,
        decl: &mut impl Declarator,
    ) -> Self {
        let name_str = ctx.interner.resolve(&d.name.0).to_string();
        let (id, slot) = decl.alloc_slot::<vmir::Domain>(&name_str);
        ctx.name_map.insert(d.name.0, id);

        let generics: Vec<Spur> = d.type_params.iter().map(|i| i.0).collect();
        let mut fn_slots = Vec::with_capacity(d.functions.len());
        for df in &d.functions {
            let fn_name = ctx.interner.resolve(&df.name.0).to_string();
            let (fid, fslot) = decl.alloc_slot::<vmir::Function>(&fn_name);
            ctx.name_map.insert(df.name.0, fid);
            // Only the type parameters the function actually mentions survive;
            // an unused one is irrelevant to the function and cannot be inferred
            // at a call site.
            let used = used_generics(&generics, &df.params, &df.ret);
            // Record the declared generic signature so a call site can recover
            // its type-argument instantiation (in this function's *used*
            // type-parameter order). A function using no type parameter needs
            // none — leaving it out of `fn_generic_sigs` also keeps
            // `call_type_args` from trying (and failing) to resolve a parameter
            // that never occurs in its signature.
            if !used.is_empty() {
                let typed_params: Vec<typed::Type> =
                    df.params.iter().map(|p| p.ty.clone()).collect();
                ctx.fn_generic_sigs.insert(
                    df.name.0,
                    GenericSig {
                        ty_params: used.clone(),
                        params: typed_params,
                        ret: df.ret.clone(),
                    },
                );
            }
            fn_slots.push((fslot, used));
        }

        let mut axiom_slots = Vec::with_capacity(d.axioms.len());
        let mut quant_slots = Vec::with_capacity(d.axioms.len());
        for (i, ax) in d.axioms.iter().enumerate() {
            let ax_name = match &ax.name {
                Some(n) => ctx.interner.resolve(&n.0).to_string(),
                None => format!("{name_str}#axiom{i}"),
            };
            let (_, aslot) = decl.alloc_slot::<vmir::Axiom>(&ax_name);
            axiom_slots.push(aslot);
            // Pre-allocate one occurrence slot per `forall` (nested included),
            // in the preorder the body lowering will encounter them.
            let n_foralls = count_foralls(&ax.exp);
            let mut slots = Vec::with_capacity(n_foralls);
            for j in 0..n_foralls {
                let (id, qslot) =
                    decl.alloc_slot::<vmir::Quantifier>(&format!("{ax_name}#quant{j}"));
                slots.push((id, qslot));
            }
            quant_slots.push(slots);
        }

        DomainTranslator {
            src: d,
            silver_name: d.name.0,
            generics,
            slot,
            fn_slots,
            axiom_slots,
            quant_slots,
            _p: PhantomData,
        }
    }

    /// No `name_map`-dependent metadata to publish.
    pub(crate) fn meta(self, _ctx: &mut TranslationContext<'_>) -> DomainTranslator<'a, Metaed> {
        DomainTranslator {
            src: self.src,
            silver_name: self.silver_name,
            generics: self.generics,
            slot: self.slot,
            fn_slots: self.fn_slots,
            axiom_slots: self.axiom_slots,
            quant_slots: self.quant_slots,
            _p: PhantomData,
        }
    }
}

impl DomainTranslator<'_, Metaed> {
    pub(crate) fn define(
        self,
        ctx: &mut TranslationContext<'_>,
        definer: &mut impl Definer,
    ) -> Result<(), TranslationError> {
        let name = definer.intern_name(ctx.interner.resolve(&self.silver_name));
        definer.define_domain(
            self.slot,
            vmir::Domain {
                name,
                ty_params: self.generics.len().into(),
            },
        );
        for (df, (fslot, used)) in self.src.functions.iter().zip(self.fn_slots) {
            // Lower against the function's *used* type parameters, so each
            // `Generic(i)` indexes into `used` (0..used.len()) and unused domain
            // parameters neither appear nor inflate `ty_params`.
            let params: Vec<vmir::Type> = df
                .params
                .iter()
                .map(|p| lower_type(&ctx.name_map, &used, &p.ty))
                .collect();
            let ret = lower_type(&ctx.name_map, &used, &df.ret);
            let fn_name = definer.intern_name(ctx.interner.resolve(&df.name.0));
            definer.define_function(
                fslot,
                vmir::Function {
                    name: fn_name,
                    ty_params: used.len().into(),
                    params: params.into(),
                    ret,
                    body: None,
                },
            );
        }
        // Axioms: lower each body against its own used generics (scoped into
        // `ctx.decl_generics` so `Type::Generic` lowers positionally). The
        // body is pure and heap-free — a callee is at most a precondition-free
        // Silver function (typecheck-enforced), so the inert `Empty` heap is
        // never read. Axiom bodies are never verified, only assumed.
        let env = HashMap::new();
        for (i, ((ax, aslot), qslots)) in self
            .src
            .axioms
            .iter()
            .zip(self.axiom_slots)
            .zip(self.quant_slots)
            .enumerate()
        {
            let mut used = Vec::new();
            used_generics_in_exp(&ax.exp, &self.generics, &mut used);
            ctx.decl_generics = used.clone();
            // Seed the occurrence ids for this axiom's `forall`s (preorder), so
            // each lowers to its nullary occurrence call and yields a built
            // quantifier back in `quant_built`.
            let quant_ids: std::collections::VecDeque<vmir::MemberId> =
                qslots.iter().map(|(id, _)| *id).collect();
            let lowered = pure_exp::lower_axiom_body(ctx, &env, &ax.exp, quant_ids);
            ctx.decl_generics = Vec::new();
            let (body, quant_built) = lowered?;
            // The axiom's carried name matches its slot registration: the
            // Silver name when given, the generated `{domain}#axiom{i}` slot
            // name otherwise.
            let ax_name = match &ax.name {
                Some(n) => ctx.interner.resolve(&n.0).to_string(),
                None => format!("{}#axiom{i}", ctx.interner.resolve(&self.silver_name)),
            };
            // Fill each quantifier slot with its built declaration. Built order
            // is innermost-first (an inner `forall` finishes lowering before its
            // encloser pushes), so slots are matched by id, not position. Set
            // the name to match the slot registration `{axiom}#quant{j}`.
            debug_assert_eq!(qslots.len(), quant_built.len());
            let mut by_id: HashMap<vmir::MemberId, vmir::Quantifier> =
                quant_built.into_iter().collect();
            for (j, (slot_id, qslot)) in qslots.into_iter().enumerate() {
                let mut quant = by_id.remove(&slot_id).expect("forall slot never filled");
                quant.name = definer.intern_name(&format!("{ax_name}#quant{j}"));
                definer.define_quantifier(qslot, quant);
            }
            let name = definer.intern_name(&ax_name);
            let axiom = vmir::Axiom {
                name: Some(name),
                ty_params: used.len().into(),
                body,
            };
            // A generic axiom must contain a trigger: one function application
            // instantiating all its type parameters, from which the verifier
            // reads each ground instantiation.
            if !used.is_empty() && axiom.covering_trigger().is_none() {
                return Err(TranslationError::AxiomGenericsNotInferable(ax_name));
            }
            definer.define_axiom(aslot, axiom);
        }
        Ok(())
    }
}
