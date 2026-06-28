use crate::vmir::display::VmirDisplay;
use crate::vmir::{MemberId, Type, Val};
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    pub params: Vec<Type>,
    pub ret: Type,
    pub body: Option<()>,
}

/// A pure-function invocation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionCall {
    pub function: MemberId,
    /// Ground type instantiation of the callee's used type parameters. Empty for
    /// a non-generic Silver `function`; for a domain function it records the
    /// result-type vars (the mandatory part for e-graph distinctness — arg-only
    /// vars ride their argument enodes). Rides the `FuncApp` payload, not the id.
    pub type_args: Vec<Type>,
    pub args: Vec<Val>,
}

impl<'a> Display for VmirDisplay<'a, &'a Function> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, param) in self.item.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            // Label params `e0`, `e1`, … (they occupy `Val::Temp(0..n)`).
            write!(f, "e{i}: {}", self.with(param))?;
        }
        write!(f, ") -> {}", self.with(&self.item.ret))
    }
}
