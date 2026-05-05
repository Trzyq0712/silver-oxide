use crate::vmir::{HeapInst, HeapVal, MemberId, PureInst, Type, Val};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Inst {
    Assume(Val),
    Assert(Val),
    ResourceCall(ResourceCall),
    Heap(HeapInst),
    Pure(Type, PureInst),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceCall {
    pub resource: MemberId,
    pub heap_ctx: HeapVal,
    pub args: Vec<Val>,
}
