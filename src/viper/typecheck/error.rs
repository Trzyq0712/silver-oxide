use rusttyc::TcErr;

use super::lattice::ViperTcType;

#[derive(Debug, Clone)]
pub enum TypeError {
    TypeMismatch {
        expected: ViperTcType,
        found: ViperTcType,
        context: &'static str,
    },
    UndefinedVariable(String),
    PredicateInPureContext(String),
    PermissionInPureContext,
    WrongArgCount {
        name: String,
        expected: usize,
        found: usize,
    },
    FieldBaseNotRef,
    IllegalOldUsage,
    IllegalLabeledOldUsage,
    IllegalResultUsage,
    UndefinedLabel(String),
    ShadowedName(String),
    WrongReturnCount {
        expected: usize,
        found: usize,
    },
    /// A `Generic` type parameter occurred outside a scope that binds it.
    UnboundTypeParam(String),
    Tc(TcErr<ViperTcType>),
    Other(String),
}

impl From<TcErr<ViperTcType>> for TypeError {
    fn from(e: TcErr<ViperTcType>) -> Self {
        TypeError::Tc(e)
    }
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::TypeMismatch {
                expected,
                found,
                context,
            } => {
                write!(
                    f,
                    "Type mismatch in {context}: expected {expected:?}, found {found:?}"
                )
            }
            TypeError::UndefinedVariable(name) => write!(f, "Undefined variable: {name}"),
            TypeError::PredicateInPureContext(name) => {
                write!(f, "Predicate `{name}` used in pure expression context")
            }
            TypeError::PermissionInPureContext => write!(f, "`perm` not allowed here"),
            TypeError::WrongArgCount {
                name,
                expected,
                found,
            } => {
                write!(f, "`{name}` expects {expected} args, got {found}")
            }
            TypeError::FieldBaseNotRef => write!(f, "Field access base must have type Ref"),
            TypeError::IllegalOldUsage => write!(f, "`old` not allowed in this context"),
            TypeError::IllegalLabeledOldUsage => {
                write!(f, "labeled `old` not allowed in this context")
            }
            TypeError::IllegalResultUsage => write!(f, "`result` not allowed in this context"),
            TypeError::UndefinedLabel(name) => {
                write!(f, "label `{name}` is not defined in this method")
            }
            TypeError::ShadowedName(name) => {
                write!(f, "name `{name}` already declared in this scope")
            }
            TypeError::WrongReturnCount { expected, found } => {
                write!(
                    f,
                    "assignment expects {expected} target(s) on LHS, found {found}"
                )
            }
            TypeError::UnboundTypeParam(name) => {
                write!(f, "unbound type parameter `{name}`")
            }
            TypeError::Tc(e) => write!(f, "Constraint error: {e:?}"),
            TypeError::Other(msg) => write!(f, "{msg}"),
        }
    }
}
