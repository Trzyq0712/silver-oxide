//! Lower a Silver `predicate` to its `vmir::Resource` (always self-framed).

use std::collections::HashMap;

use lasso::Spur;

use crate::translate::hole::{Declarator, Definer, Hole};
use crate::translate::{TranslationContext, TranslationError, spatial};
use crate::viper::{Interner, typed};
use crate::vmir;

/// Metadata the coordinator folds into `TranslationContext` (`name_map`) once
/// a predicate is declared.
pub(crate) struct PredicateMeta {
    pub silver_name: Spur,
    pub id: vmir::MemberId,
}

pub(crate) struct PredicateTranslator {
    hole: Hole<vmir::Resource>,
    meta: PredicateMeta,
}

impl PredicateTranslator {
    /// Reserve the predicate's `Resource` slot (filled by `define`) so its id
    /// can serve as snapshot head, address `LocId`, and footprint reference.
    /// Its address is grouped by the predicate name, not by the reserved id.
    pub(crate) fn declare(
        p: &typed::Predicate,
        interner: &Interner,
        declarator: &mut impl Declarator,
    ) -> Self {
        let name_str = interner.resolve(&p.name.0).to_owned();
        declarator.intern_group(&name_str);
        let (id, hole) = declarator.allocate_hole::<vmir::Resource>(&name_str);
        PredicateTranslator {
            hole,
            meta: PredicateMeta {
                silver_name: p.name.0,
                id,
            },
        }
    }

    pub(crate) fn meta(&self) -> &PredicateMeta {
        &self.meta
    }

    pub(crate) fn define(
        self,
        ctx: &TranslationContext<'_>,
        p: &typed::Predicate,
        definer: &mut impl Definer,
    ) -> Result<(), TranslationError> {
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
                match spatial::lower_spatial_never(
                    ctx,
                    &env,
                    body_exp,
                    params.len(),
                    vmir::HeapVal::Empty,
                    0,
                ) {
                    Ok(body) => Some(body),
                    Err(e) => {
                        // The Hole is still unfilled on this error path — abandon
                        // it explicitly so the drop bomb doesn't panic on top of
                        // the `TranslationError` we're about to propagate.
                        self.hole.abandon();
                        return Err(e);
                    }
                }
            }
        };
        let name = definer.intern_name(ctx.interner.resolve(&self.meta.silver_name));
        definer.define_resource(
            self.hole,
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
