use crate::vmir::MemberId;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Bool,
    Real,
    Ref,

    Domain(MemberId),
    Addr(Box<Type>),

    Heap,
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
            Type::Heap => write!(f, "Heap"),
        }
    }
}
