//! Lower a Silver `domain` declaration to its `vmir::Domain` stub, and each of
//! its (bodyless) domain functions to a `vmir::Function`.

use lasso::Spur;

use crate::translate::GenericSig;
use crate::translate::hole::{Declarator, Definer, Hole};
use crate::translate::lower_type;
use crate::viper::{Interner, typed};
use crate::vmir;

pub(crate) struct DomainMeta {
    pub silver_name: Spur,
    pub id: vmir::MemberId,
}

pub(crate) struct DomainTranslator {
    name_str: String,
    ty_params: usize,
    hole: Hole<vmir::Domain>,
    meta: DomainMeta,
}

impl DomainTranslator {
    pub(crate) fn declare(
        d: &typed::Domain,
        interner: &Interner,
        declarator: &mut impl Declarator,
    ) -> Self {
        let name_str = interner.resolve(&d.name.0).to_string();
        let (id, hole) = declarator.allocate_hole::<vmir::Domain>(&name_str);
        DomainTranslator {
            name_str,
            ty_params: d.type_params.len(),
            hole,
            meta: DomainMeta {
                silver_name: d.name.0,
                id,
            },
        }
    }

    pub(crate) fn meta(&self) -> &DomainMeta {
        &self.meta
    }

    pub(crate) fn define(self, definer: &mut impl Definer) {
        let name = definer.intern_name(&self.name_str);
        definer.define_domain(
            self.hole,
            vmir::Domain {
                name,
                ty_params: self.ty_params.into(),
            },
        );
    }
}

/// Metadata the coordinator folds into `TranslationContext` (`name_map`,
/// `fn_generic_sigs`) once a domain function is declared.
pub(crate) struct DomainFunctionMeta {
    pub silver_name: Spur,
    pub id: vmir::MemberId,
    /// `None` for a monomorphic (non-generic-owning-domain) function.
    pub generic_sig: Option<GenericSig>,
}

/// A domain function is bodyless and fully known at declare time — its
/// `Hole` filling still happens in a nominal `define` step for structural
/// uniformity with every other kind (trivial, infallible). `declare` needs
/// `name_map` populated with every ADT/domain stub id (its param/ret types may
/// reference any of them), so it runs only after every [`super::adt::AdtTranslator`]
/// / [`DomainTranslator`] has declared its stub.
pub(crate) struct DomainFunctionTranslator {
    name_str: String,
    generics: Vec<Spur>,
    params: Vec<vmir::Type>,
    ret: vmir::Type,
    hole: Hole<vmir::Function>,
    meta: DomainFunctionMeta,
}

impl DomainFunctionTranslator {
    pub(crate) fn declare(
        df: &typed::DomainFunction,
        interner: &Interner,
        generics: &[Spur],
        name_map: &std::collections::HashMap<Spur, vmir::MemberId>,
        declarator: &mut impl Declarator,
    ) -> Self {
        let typed_params: Vec<typed::Type> = df.params.iter().map(|p| p.ty.clone()).collect();
        let name_str = interner.resolve(&df.name.0).to_string();
        let (id, hole) = declarator.allocate_hole::<vmir::Function>(&name_str);
        let params = typed_params
            .iter()
            .map(|t| lower_type(name_map, generics, t))
            .collect();
        let ret = lower_type(name_map, generics, &df.ret);
        let generic_sig = (!generics.is_empty()).then(|| GenericSig {
            ty_params: generics.to_vec(),
            params: typed_params,
            ret: df.ret.clone(),
        });
        DomainFunctionTranslator {
            name_str,
            generics: generics.to_vec(),
            params,
            ret,
            hole,
            meta: DomainFunctionMeta {
                silver_name: df.name.0,
                id,
                generic_sig,
            },
        }
    }

    pub(crate) fn meta(&self) -> &DomainFunctionMeta {
        &self.meta
    }

    pub(crate) fn define(self, definer: &mut impl Definer) {
        let name = definer.intern_name(&self.name_str);
        definer.define_function(
            self.hole,
            vmir::Function {
                name,
                ty_params: self.generics.len().into(),
                params: self.params.into(),
                ret: self.ret,
                body: None,
            },
        );
    }
}
