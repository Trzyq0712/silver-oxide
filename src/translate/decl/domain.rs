//! Lower a Silver `domain` declaration to its `vmir::Domain` stub, and each of
//! its (bodyless) domain functions to a `vmir::Function`. One `DomainTranslator`
//! owns the domain stub *and* every function slot the domain declares.

use std::marker::PhantomData;

use lasso::Spur;

use crate::translate::GenericSig;
use crate::translate::lower_type;
use crate::translate::{DeclSlot, Declarator, Definer};
use crate::translate::{Declared, Metaed, TranslationContext, TranslationError};
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
    _p: PhantomData<P>,
}

/// The subset of `generics` that occur anywhere in `params`/`ret`, in order of
/// first appearance. A domain function is implicitly parameterized by all of
/// its domain's type parameters, but one it never mentions is dropped so the
/// lowered function is (correctly) monomorphic in that parameter.
fn used_generics(generics: &[Spur], params: &[typed::TypedIdent], ret: &typed::Type) -> Vec<Spur> {
    fn collect(ty: &typed::Type, generics: &[Spur], out: &mut Vec<Spur>) {
        use typed::BuiltinCollection as C;
        match ty {
            typed::Type::Generic(id) => {
                if generics.contains(&id.0) && !out.contains(&id.0) {
                    out.push(id.0);
                }
            }
            typed::Type::Domain(_, args) => {
                for a in args {
                    collect(a, generics, out);
                }
            }
            typed::Type::Collection(c) => match c {
                C::Seq(t) | C::Set(t) | C::MultiSet(t) => collect(t, generics, out),
                C::Map(k, v) => {
                    collect(k, generics, out);
                    collect(v, generics, out);
                }
            },
            typed::Type::Bool | typed::Type::Int | typed::Type::Real | typed::Type::Ref => {}
        }
    }
    let mut out = Vec::new();
    for p in params {
        collect(&p.ty, generics, &mut out);
    }
    collect(ret, generics, &mut out);
    out
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

        DomainTranslator {
            src: d,
            silver_name: d.name.0,
            generics,
            slot,
            fn_slots,
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
            _p: PhantomData,
        }
    }
}

impl DomainTranslator<'_, Metaed> {
    pub(crate) fn define(
        self,
        ctx: &TranslationContext<'_>,
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
        // TODO: axioms are not yet translated
        Ok(())
    }
}
