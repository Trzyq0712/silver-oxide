use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TranslationError {
    Unsupported(&'static str),
    UnknownIdent(String),
    /// A `domain` declaring type parameters. Generics live on ADTs only: a
    /// generic domain would need a *type* trigger to instantiate its axioms, and
    /// Silver has no syntax to write one.
    GenericDomainUnsupported(String),
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
        }
    }
}

impl std::error::Error for TranslationError {}
