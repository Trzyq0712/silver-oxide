//! Lower a typed Silver `Type` to a VMIR `Type`.

use std::collections::HashMap;

use lasso::Spur;

use crate::viper::typed;
use crate::vmir;

/// Lower a typed Silver type to a VMIR type.
///
/// `names` resolves a domain/ADT name `Spur` to its VMIR declaration id;
/// `generics` is the enclosing generic declaration's type-parameter list (used
/// to map a `Type::Generic` to its 0-based index). Both are empty in fully
/// concrete contexts (most call sites go through [`super::Builder::lower_type`]).
pub(crate) fn lower_type(
    names: &HashMap<Spur, vmir::MemberId>,
    generics: &[Spur],
    ty: &typed::Type,
) -> vmir::Type {
    match ty {
        typed::Type::Bool => vmir::Type::Bool,
        typed::Type::Int => vmir::Type::Int,
        typed::Type::Real => vmir::Type::Real,
        typed::Type::Ref => vmir::Type::Ref,
        typed::Type::Generic(id) => {
            let idx = generics
                .iter()
                .position(|p| *p == id.0)
                .expect("generic type parameter not in the enclosing declaration's scope");
            vmir::Type::Generic(idx)
        }
        typed::Type::Domain(id, args) => match names.get(&id.0) {
            // An ADT (or a modeled domain): keep the head + recurse on args so
            // the monomorphization key `(head, args)` is faithful.
            Some(&head) => {
                let args = args
                    .iter()
                    .map(|a| lower_type(names, generics, a))
                    .collect();
                vmir::Type::Domain(head, args)
            }
            // A domain with no VMIR declaration (not yet modeled). Fall back to
            // Ref, as before; ADTs are always present (declared in pass 1).
            None => vmir::Type::Ref,
        },
        // TODO: Seq/Set — modeled as builtin parametric types like Option.
        typed::Type::Collection(_) => vmir::Type::Ref,
    }
}

/// Structurally match a declared type (which may mention `Type::Generic`
/// parameters) against a concrete type, recording each parameter's binding in
/// `out`. Used to recover a generic call's type-argument instantiation from its
/// concrete argument/result types. First binding wins (bindings are consistent
/// for a well-typed call).
pub(crate) fn match_generic(
    decl: &typed::Type,
    actual: &typed::Type,
    out: &mut HashMap<Spur, typed::Type>,
) {
    use crate::viper::typed::BuiltinCollection as C;
    use typed::Type as T;
    match (decl, actual) {
        (T::Generic(n), _) => {
            out.entry(n.0).or_insert_with(|| actual.clone());
        }
        (T::Domain(_, ds), T::Domain(_, as_)) => {
            for (d, a) in ds.iter().zip(as_) {
                match_generic(d, a, out);
            }
        }
        (T::Collection(dc), T::Collection(ac)) => match (dc, ac) {
            (C::Seq(d), C::Seq(a)) | (C::Set(d), C::Set(a)) | (C::MultiSet(d), C::MultiSet(a)) => {
                match_generic(d, a, out)
            }
            (C::Map(dk, dv), C::Map(ak, av)) => {
                match_generic(dk, ak, out);
                match_generic(dv, av, out);
            }
            _ => {}
        },
        _ => {}
    }
}
