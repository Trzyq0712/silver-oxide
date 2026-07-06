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
    /// One slot per domain function, parallel to `src.functions`.
    fn_slots: Vec<DeclSlot<vmir::Function>>,
    _p: PhantomData<P>,
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
            // Record the declared generic signature so a call site can recover
            // its full type-argument instantiation (in this domain's
            // type-parameter order). Only generic functions need it; a
            // monomorphic one carries no type args.
            if !generics.is_empty() {
                let typed_params: Vec<typed::Type> =
                    df.params.iter().map(|p| p.ty.clone()).collect();
                ctx.fn_generic_sigs.insert(
                    df.name.0,
                    GenericSig {
                        ty_params: generics.clone(),
                        params: typed_params,
                        ret: df.ret.clone(),
                    },
                );
            }
            fn_slots.push(fslot);
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
        for (df, fslot) in self.src.functions.iter().zip(self.fn_slots) {
            let params: Vec<vmir::Type> = df
                .params
                .iter()
                .map(|p| lower_type(&ctx.name_map, &self.generics, &p.ty))
                .collect();
            let ret = lower_type(&ctx.name_map, &self.generics, &df.ret);
            let fn_name = definer.intern_name(ctx.interner.resolve(&df.name.0));
            definer.define_function(
                fslot,
                vmir::Function {
                    name: fn_name,
                    ty_params: self.generics.len().into(),
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
