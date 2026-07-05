//! Lower a Silver `field` to its `@addr` function (`Ref -> Addr<T>`).

use lasso::Spur;

use crate::translate::TranslationContext;
use crate::translate::hole::{Declarator, Definer, Hole};
use crate::viper::{Interner, typed};
use crate::vmir;

/// Metadata the coordinator folds into `TranslationContext` (`name_map`,
/// `field_types`) once a field is declared.
pub(crate) struct FieldMeta {
    pub silver_name: Spur,
    pub id: vmir::MemberId,
    pub value: vmir::Type,
}

/// A field's address is an ordinary function `Ref -> Addr<T>` (group = field
/// name, value = field type, bound = full permission `1/1`). A field has no
/// separate body to lower, so `declare` and `define` are called back to back
/// by the coordinator — the `Hole` still passes through both, for the same
/// affine discipline every other kind gets.
pub(crate) struct FieldTranslator {
    name_str: String,
    group: Spur,
    hole: Hole<vmir::Function>,
    meta: FieldMeta,
}

impl FieldTranslator {
    /// `ctx` reflects `name_map` as built up to this point in `declare` —
    /// predicates/fields are declared before ADTs, so a field type mentioning
    /// an ADT would not resolve here (preserved unchanged from before this
    /// refactor: `types::lower_type` falls back to `Ref` for an unknown
    /// `Domain` head).
    pub(crate) fn declare(
        f: &typed::Field,
        interner: &Interner,
        ctx: &TranslationContext<'_>,
        declarator: &mut impl Declarator,
    ) -> Self {
        let name_str = interner.resolve(&f.0.name.0).to_owned();
        let group = declarator.intern_group(&name_str);
        let (id, hole) = declarator.allocate_hole::<vmir::Function>(&name_str);
        let value = ctx.lower_type(&f.0.ty);
        FieldTranslator {
            name_str,
            group,
            hole,
            meta: FieldMeta {
                silver_name: f.0.name.0,
                id,
                value,
            },
        }
    }

    pub(crate) fn meta(&self) -> &FieldMeta {
        &self.meta
    }

    pub(crate) fn define(self, definer: &mut impl Definer) {
        let bound = vmir::Bound::Bounded(num::BigRational::from(num::BigInt::from(1)));
        let ret = vmir::Type::addr(self.group, self.meta.value.clone(), bound);
        let name = definer.intern_name(&self.name_str);
        definer.define_function(
            self.hole,
            vmir::Function {
                name,
                ty_params: 0.into(),
                params: vec![vmir::Type::Ref].into(),
                ret,
                body: None,
            },
        );
    }
}
