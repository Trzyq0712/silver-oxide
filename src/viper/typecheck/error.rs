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
    /// A heap-reading construct (`e.f`, a `function` call, `unfolding`) used in a
    /// pure context (e.g. a domain axiom).
    HeapInPureContext,
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
    /// A quantifier in a domain axiom (only ground axioms are supported).
    QuantifierInAxiom,
    /// A field dereference in a domain axiom.
    FieldAccessInAxiom,
    /// An `unfolding` expression in a domain axiom.
    UnfoldingInAxiom,
    /// An axiom calls a Silver `function` that has a precondition.
    PreconditionedFunctionInAxiom(String),
    /// A call in an axiom left a type parameter of a *foreign* domain's
    /// function unconstrained (an enclosing-domain parameter would default to
    /// itself, Silver's `ground()` rule).
    UnconstrainedTypeParamInAxiom(String),
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
            TypeError::HeapInPureContext => {
                write!(f, "heap-dependent expression not allowed in a pure context")
            }
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
            TypeError::QuantifierInAxiom => {
                write!(f, "quantifiers are not supported in domain axioms")
            }
            TypeError::FieldAccessInAxiom => {
                write!(f, "field access not allowed in a domain axiom")
            }
            TypeError::UnfoldingInAxiom => {
                write!(f, "`unfolding` not allowed in a domain axiom")
            }
            TypeError::PreconditionedFunctionInAxiom(name) => {
                write!(
                    f,
                    "cannot use function `{name}`, which has preconditions, inside a domain axiom"
                )
            }
            TypeError::UnconstrainedTypeParamInAxiom(name) => {
                write!(
                    f,
                    "unconstrained type parameter `{name}` in a domain axiom; annotate the call"
                )
            }
            TypeError::Tc(e) => write!(f, "Constraint error: {e:?}"),
            TypeError::Other(msg) => write!(f, "{msg}"),
        }
    }
}
