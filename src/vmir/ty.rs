use crate::vmir::MemberId;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Bool,
    Real,
    Ref,

    Domain(MemberId),
    Addr(Box<Type>),
}
