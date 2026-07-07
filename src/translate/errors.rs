use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TranslationError {
    Unsupported(&'static str),
    UnknownIdent(String),
    /// A generic axiom has no single function application whose type arguments
    /// cover all of the axiom's type parameters — the verifier would have no
    /// trigger from which to read a ground instantiation.
    AxiomGenericsNotInferable(String),
    /// A `forall` nested inside another `forall` — not supported in v1 (the
    /// inner quantifier would capture the outer's bound variables).
    NestedForallUnsupported,
    /// A `forall` whose trigger is not a single function application whose
    /// arguments are exactly the bound variables, jointly covering all of them.
    TriggerNotCovering,
    /// A `forall` inside a generic axiom — not supported in v1.
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
            TranslationError::NestedForallUnsupported => {
                write!(f, "nested `forall` is not supported")
            }
            TranslationError::TriggerNotCovering => write!(
                f,
                "`forall` trigger must be a single application of the bound variables covering all of them"
            ),
            TranslationError::GenericForallUnsupported => {
                write!(f, "`forall` inside a generic axiom is not supported")
            }
        }
    }
}

impl std::error::Error for TranslationError {}
