//! The verifier's error type.

#[derive(Debug)]
pub enum VerifyError {
    AssertionFailed,
    /// A `refute` whose expression turned out to be provable (so the refutation
    /// fails).
    RefuteFailed,
    InsufficientPermission,
    /// An instruction's side condition (e.g. `acc` permission ≥ 0, division
    /// divisor ≠ 0) could not be discharged. Carries a human-readable
    /// description. See [`inst_obligations`](crate::verify::declaration).
    SideCondition(&'static str),
    /// Encountered a method-only heap extension (e.g. `Assign`) in a body
    /// the verifier doesn't yet handle structurally. Reserved for
    /// not-yet-implemented variants.
    Unimplemented(&'static str),
    /// A call/fold/unfold targets a resource that produced no certificate —
    /// i.e. the resource itself failed its well-formedness verification.
    DependencyFailed,
    /// Verification failed while executing a specific instruction.
    AtInst {
        inst: String,
        source: Box<VerifyError>,
    },
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AssertionFailed => write!(f, "assertion failed"),
            Self::RefuteFailed => write!(f, "refuted expression is actually provable"),
            Self::InsufficientPermission => write!(f, "insufficient permission"),
            Self::SideCondition(what) => write!(f, "side condition may not hold: {what}"),
            Self::Unimplemented(what) => write!(f, "unimplemented: {what}"),
            Self::DependencyFailed => {
                write!(f, "depends on a resource that failed to verify")
            }
            Self::AtInst { inst, source } => write!(f, "{source}\n    instruction: {inst}"),
        }
    }
}

impl VerifyError {
    /// Wrap this error with the instruction text it occurred at (idempotent — an
    /// already-wrapped error keeps its innermost source).
    pub(crate) fn with_inst(self, inst: String) -> Self {
        match self {
            Self::AtInst { .. } => self,
            _ => Self::AtInst {
                inst,
                source: Box::new(self),
            },
        }
    }

    /// The innermost error, peeling any `AtInst` wrapping. Used by tests to
    /// assert on the underlying cause.
    #[cfg(test)]
    pub(crate) fn root_cause(&self) -> &VerifyError {
        match self {
            Self::AtInst { source, .. } => source.root_cause(),
            _ => self,
        }
    }
}
