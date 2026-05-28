use crate::vmir::MemberId;
use crate::vmir::display::VmirDisplay;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Bool,
    Real,
    Ref,

    Domain(MemberId),
    Addr(Box<Type>),
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Bool => write!(f, "Bool"),
            Type::Int => write!(f, "Int"),
            Type::Real => write!(f, "Real"),
            Type::Ref => write!(f, "Ref"),
            Type::Domain(id) => write!(f, "d{}", id.0),
            Type::Addr(ty) => write!(f, "&{ty}"),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Type> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            Type::Domain(id) => write!(f, "{}", self.interner.resolve(id)),
            Type::Addr(ty) => write!(f, "&{}", self.with(ty.as_ref())),
            ty => write!(f, "{ty}"),
        }
    }
}
