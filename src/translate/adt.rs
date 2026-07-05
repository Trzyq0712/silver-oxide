//! Lower a Silver `adt` (ADT) declaration to its `vmir::Adt` stub + variant
//! shapes, plus per-constructor/destructor metadata.

use std::collections::HashMap;

use lasso::Spur;

use crate::translate::context::AdtInfo;
use crate::translate::hole::{Declarator, Definer, Hole};
use crate::translate::lower_type;
use crate::viper::{Interner, typed};
use crate::vmir;

pub(crate) struct AdtMeta {
    pub silver_name: Spur,
    pub id: vmir::MemberId,
}

/// An ADT's `declare` reserves only the stub id (+ type-param count) — no
/// variant computation, since a variant field type or constructor may
/// reference *any* ADT by id (including one declared later in the source).
/// [`compute_adt_info`] runs once every ADT's stub id is in `name_map`
/// (mirroring the pass-1/pass-3 split of the original `declare_adts_and_functions`),
/// and its result is what `define` fills the `Hole` with.
pub(crate) struct AdtTranslator {
    name_str: String,
    ty_params: usize,
    hole: Hole<vmir::Adt>,
    meta: AdtMeta,
}

impl AdtTranslator {
    pub(crate) fn declare(
        adt: &typed::Adt,
        interner: &Interner,
        declarator: &mut impl Declarator,
    ) -> Self {
        let name_str = interner.resolve(&adt.name.0).to_string();
        let (id, hole) = declarator.allocate_hole::<vmir::Adt>(&name_str);
        AdtTranslator {
            name_str,
            ty_params: adt.type_params.len(),
            hole,
            meta: AdtMeta {
                silver_name: adt.name.0,
                id,
            },
        }
    }

    pub(crate) fn meta(&self) -> &AdtMeta {
        &self.meta
    }

    pub(crate) fn define(self, variants: Vec<vmir::AdtVariant>, definer: &mut impl Definer) {
        let name = definer.intern_name(&self.name_str);
        definer.define_adt(
            self.hole,
            vmir::Adt {
                name,
                ty_params: self.ty_params.into(),
                variants,
            },
        );
    }
}

/// Compute every ADT's variant shape and constructor (`ctor_tag`) /
/// destructor (`dtor_sem`) metadata, given `name_map` populated with every
/// ADT/domain stub id. A constructor/destructor is not itself a declaration:
/// the constructor name is interned for display only, and a destructor maps a
/// field name to its `(adt, variant, field)` projection. Returns each ADT's
/// filled variant shape, keyed by its Silver name, for [`AdtTranslator::define`].
pub(crate) fn compute_adt_info(
    adts: &[&typed::Adt],
    interner: &Interner,
    name_map: &HashMap<Spur, vmir::MemberId>,
    adt_info: &mut AdtInfo,
    definer: &mut impl Definer,
) -> HashMap<Spur, Vec<vmir::AdtVariant>> {
    let mut out = HashMap::new();
    for adt in adts {
        let adt_id = name_map[&adt.name.0];
        // Variant field types may mention the ADT's type parameters (→ `Generic`).
        let type_params: Vec<Spur> = adt.type_params.iter().map(|i| i.0).collect();
        let mut variants: Vec<vmir::AdtVariant> = Vec::new();
        for (tag, v) in adt.variants.iter().enumerate() {
            adt_info.ctor_tag.insert(v.name.0, (adt.name.0, tag));
            let ctor_str = interner.resolve(&v.name.0).to_string();
            let ctor_name = definer.intern_name(&ctor_str);
            let field_types: Vec<vmir::Type> = v
                .params
                .iter()
                .map(|p| lower_type(name_map, &type_params, &p.ty))
                .collect();
            for (field, p) in v.params.iter().enumerate() {
                adt_info.dtor_sem.insert(p.name.0, (adt_id, tag, field));
            }
            if variants.len() <= tag {
                variants.resize(
                    tag + 1,
                    vmir::AdtVariant {
                        name: None,
                        field_types: Vec::new(),
                    },
                );
            }
            variants[tag] = vmir::AdtVariant {
                name: Some(ctor_name),
                field_types,
            };
        }
        out.insert(adt.name.0, variants);
    }
    out
}
