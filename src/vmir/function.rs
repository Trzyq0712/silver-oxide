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
    pub args: Vec<Val>,
}

impl<'a> Display for VmirDisplay<'a, &'a Function> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, param) in self.item.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.with(param))?;
        }
        write!(f, ") -> {}", self.with(&self.item.ret))
    }
}
