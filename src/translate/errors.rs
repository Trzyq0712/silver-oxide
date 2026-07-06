use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TranslationError {
    Unsupported(&'static str),
    UnknownIdent(String),
    /// A generic axiom has no single function application whose type arguments
    /// cover all of the axiom's type parameters — the verifier would have no
    /// trigger from which to read a ground instantiation.
    AxiomGenericsNotInferable(String),
}

impl fmt::Display for TranslationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TranslationError::Unsupported(what) => write!(f, "unsupported: {what}"),
            TranslationError::UnknownIdent(name) => write!(f, "unknown identifier: {name}"),
            TranslationError::AxiomGenericsNotInferable(name) => write!(
                f,
                "axiom `{name}`: no function application instantiates all of the axiom's type parameters"
            ),
        }
    }
}

impl std::error::Error for TranslationError {}
