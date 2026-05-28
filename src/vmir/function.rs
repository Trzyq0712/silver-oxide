use crate::vmir::{HeapVal, MemberId, Type, Val};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    pub params: Vec<Type>,
    pub ret: Type,
    pub body: Option<()>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionCall {
    pub function: MemberId,
    /// The heap in which the function should be evaluated.
    pub ctx_heap: HeapVal,
    pub args: Vec<Val>,
}
