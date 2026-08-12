use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TranslationError {
    Unsupported(&'static str),
    UnknownIdent(String),
    /// A `domain` declaring type parameters. Generics live on ADTs only: a
    /// generic domain would need a *type* trigger to instantiate its axioms, and
    /// Silver has no syntax to write one.
    GenericDomainUnsupported(String),
    /// A heap-dependent function called inside a `forall` body. Its snapshot
    /// (a frame-only `exhale`) would have to be taken *per instance*, over a footprint
    /// that may mention the binders — quantified permissions, which are not
    /// supported. Even a binder-independent footprint is rejected for now: the
    /// quantifier's compiled body must stay pure and heap-free, since the
    /// verifier rebuilds it inside a rewrite rule, where the symbolic heap is out
    /// of reach and no obligation can be discharged.
    HeapDepFunctionInQuantifier(String),
}

impl fmt::Display for TranslationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TranslationError::Unsupported(what) => write!(f, "unsupported: {what}"),
            TranslationError::UnknownIdent(name) => write!(f, "unknown identifier: {name}"),
            TranslationError::GenericDomainUnsupported(name) => write!(
                f,
                "domain `{name}` declares type parameters: generic domains are not supported, declare an `adt` instead"
            ),
            TranslationError::HeapDepFunctionInQuantifier(name) => write!(
                f,
                "heap-dependent function `{name}` called inside a `forall`: a quantifier body must be heap-free (this needs quantified permissions)"
            ),
        }
    }
}

impl std::error::Error for TranslationError {}
