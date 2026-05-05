use crate::vmir::Type;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    pub params: Vec<Type>,
    pub ret: Type,
}
