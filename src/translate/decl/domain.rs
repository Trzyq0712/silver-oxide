//! Lower a Silver `domain` declaration to its `vmir::Domain` stub, each of
//! its (bodyless) domain functions to a `vmir::Function`, and each of its
//! axioms to a `vmir::Axiom`. One `DomainTranslator` owns the domain
//! stub *and* every function/axiom slot the domain declares.
//!
//! Domains are **monomorphic**: a domain declaring type parameters is rejected
//! (`GenericDomainUnsupported`). A generic domain's axioms could only be
//! instantiated off a *type* trigger, which Silver has no syntax to write —
//! rather than infer one, we refuse. Generics live on ADTs.

use std::collections::HashMap;
use std::marker::PhantomData;

use lasso::Spur;

use crate::translate::lower_type;
use crate::translate::{DeclSlot, Declarator, Definer};
use crate::translate::{Declared, Metaed, TranslationContext, TranslationError, pure_exp};
use crate::viper::typed;
use crate::vmir;

pub(crate) struct DomainTranslator<'a, P = Declared> {
    src: &'a typed::Domain,
    silver_name: Spur,
    slot: DeclSlot<vmir::Domain>,
    /// One `Function` slot per domain function, parallel to `src.functions`.
    fn_slots: Vec<DeclSlot<vmir::Function>>,
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

impl<'a> DomainTranslator<'a, Declared> {
    /// Reserve the domain stub + a `Function` slot per domain function, and
    /// publish every `name_map` entry. A domain function's param/ret types are
    /// *not* lowered here — they may reference any ADT/domain by id, so lowering
    /// waits for `define`.
    pub(crate) fn declare(
        d: &'a typed::Domain,
        ctx: &mut TranslationContext<'_>,
        decl: &mut impl Declarator,
    ) -> Self {
        let name_str = ctx.interner.resolve(&d.name.0).to_string();
        let (id, slot) = decl.alloc_slot::<vmir::Domain>(&name_str);
        ctx.name_map.insert(d.name.0, id);

        let mut fn_slots = Vec::with_capacity(d.functions.len());
        for df in &d.functions {
            let fn_name = ctx.interner.resolve(&df.name.0).to_string();
            let (fid, fslot) = decl.alloc_slot::<vmir::Function>(&fn_name);
            ctx.name_map.insert(df.name.0, fid);
            fn_slots.push(fslot);
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
            let n_foralls = pure_exp::count_foralls(&ax.exp);
            quant_slots.push(crate::translate::alloc_quant_slots(
                decl, &ax_name, n_foralls,
            ));
        }

        DomainTranslator {
            src: d,
            silver_name: d.name.0,
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
        let name_str = ctx.interner.resolve(&self.silver_name).to_string();
        if !self.src.type_params.is_empty() {
            return Err(TranslationError::GenericDomainUnsupported(name_str));
        }
        let name = definer.intern_name(&name_str);
        definer.define_domain(self.slot, vmir::Domain { name });
        for (df, fslot) in self.src.functions.iter().zip(self.fn_slots) {
            let params: Vec<vmir::Type> = df
                .params
                .iter()
                .map(|p| lower_type(&ctx.name_map, &[], &p.ty))
                .collect();
            let ret = lower_type(&ctx.name_map, &[], &df.ret);
            let fn_name = definer.intern_name(ctx.interner.resolve(&df.name.0));
            definer.define_function(
                fslot,
                vmir::Function {
                    name: fn_name,
                    params: params.into(),
                    ret,
                    body: None,
                    requires: None,
                    ensures: None,
                },
            );
        }
        // Axioms: the body is pure and heap-free — a callee is at most a
        // precondition-free Silver function (typecheck-enforced), so the inert
        // `Empty` heap is never read. Axiom bodies are never verified, only
        // assumed.
        let env = HashMap::new();
        for (i, ((ax, aslot), qslots)) in self
            .src
            .axioms
            .iter()
            .zip(self.axiom_slots)
            .zip(self.quant_slots)
            .enumerate()
        {
            // Seed the occurrence ids for this axiom's `forall`s (preorder), so
            // each lowers to its nullary occurrence call and yields a built
            // quantifier back in `quant_built`.
            let quant_ids: std::collections::VecDeque<vmir::MemberId> =
                qslots.iter().map(|(id, _)| *id).collect();
            let (body, quant_built) = pure_exp::lower_axiom_body(ctx, &env, &ax.exp, quant_ids)?;
            // The axiom's carried name matches its slot registration: the
            // Silver name when given, the generated `{domain}#axiom{i}` slot
            // name otherwise.
            let ax_name = match &ax.name {
                Some(n) => ctx.interner.resolve(&n.0).to_string(),
                None => format!("{name_str}#axiom{i}"),
            };
            crate::translate::fill_quant_slots(definer, &ax_name, qslots, quant_built);
            let name = definer.intern_name(&ax_name);
            definer.define_axiom(
                aslot,
                vmir::Axiom {
                    name: Some(name),
                    body,
                },
            );
        }
        Ok(())
    }
}
