use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TranslationError {
    Unsupported(&'static str),
    UnknownIdent(String),
    /// A generic axiom has no single function application whose type arguments
    /// cover all of the axiom's type parameters — the verifier would have no
    /// trigger from which to read a ground instantiation.
    AxiomGenericsNotInferable(String),
    /// A `forall` with no trigger group that is a single function application
    /// whose arguments are each a bound variable or a captured enclosing
    /// variable, with the bound positions covering all binders.
    TriggerNotCovering,
    /// A `forall` inside a generic axiom — not supported (no type-σ + value-σ
    /// mix).
    GenericForallUnsupported,
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
            TranslationError::TriggerNotCovering => write!(
                f,
                "`forall` trigger must be a single application of bound or captured variables, with the bound ones covering all binders"
            ),
            TranslationError::GenericForallUnsupported => {
                write!(f, "`forall` inside a generic axiom is not supported")
            }
        }
    }
}

impl std::error::Error for TranslationError {}
