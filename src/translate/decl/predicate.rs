//! Lower a Silver `predicate` to its `vmir::Resource` (always self-framed).

use std::collections::HashMap;
use std::marker::PhantomData;

use lasso::Spur;

use crate::translate::{DeclSlot, Declarator, Definer};
use crate::translate::{Declared, Metaed, TranslationContext, TranslationError, spatial};
use crate::viper::typed;
use crate::vmir;

pub(crate) struct PredicateTranslator<'a, P = Declared> {
    src: &'a typed::Predicate,
    silver_name: Spur,
    slot: DeclSlot<vmir::Resource>,
    _p: PhantomData<P>,
}

impl<'a> PredicateTranslator<'a, Declared> {
    /// Reserve the predicate's `Resource` slot (filled by `define`) so its id
    /// can serve as snapshot head, address `LocId`, and footprint reference.
    /// Its address is grouped by the predicate name, not by the reserved id.
    pub(crate) fn declare(
        p: &'a typed::Predicate,
        ctx: &mut TranslationContext<'_>,
        d: &mut impl Declarator,
    ) -> Self {
        let name_str = ctx.interner.resolve(&p.name.0).to_owned();
        d.intern_group(&name_str);
        let (id, slot) = d.alloc_slot::<vmir::Resource>(&name_str);
        ctx.name_map.insert(p.name.0, id);
        PredicateTranslator {
            src: p,
            silver_name: p.name.0,
            slot,
            _p: PhantomData,
        }
    }

    /// No `name_map`-dependent metadata to publish.
    pub(crate) fn meta(self, _ctx: &mut TranslationContext<'_>) -> PredicateTranslator<'a, Metaed> {
        PredicateTranslator {
            src: self.src,
            silver_name: self.silver_name,
            slot: self.slot,
            _p: PhantomData,
        }
    }
}

impl PredicateTranslator<'_, Metaed> {
    pub(crate) fn define(
        self,
        ctx: &TranslationContext<'_>,
        definer: &mut impl Definer,
    ) -> Result<(), TranslationError> {
        let p = self.src;
        let params: Vec<vmir::Type> = p.params.iter().map(|pp| ctx.lower_type(&pp.ty)).collect();
        // Self-framed: params occupy `Val::Temp(0..n)`, heaps accumulate from
        // `Empty` starting at `HeapVal::Temp(0)`.
        let body = match &p.body {
            None => None,
            Some(body_exp) => {
                let mut env: HashMap<Spur, vmir::Val> = HashMap::new();
                for (i, param) in p.params.iter().enumerate() {
                    env.insert(param.name.0, vmir::Val::Temp(i));
                }
                // On error the unfilled `self.slot` is simply dropped (no cleanup
                // needed) and the whole `Builder` discarded up the stack.
                Some(spatial::lower_spatial_never(
                    ctx,
                    &env,
                    body_exp,
                    params.len(),
                    vmir::HeapVal::Empty,
                    0,
                    // Predicate body: real permissions, not wildcards.
                    false,
                )?)
            }
        };
        let name = definer.intern_name(ctx.interner.resolve(&self.silver_name));
        definer.define_resource(
            self.slot,
            vmir::Resource {
                name,
                params,
                precond: vmir::Precond::SelfFramed,
                body,
            },
        );
        Ok(())
    }
}
