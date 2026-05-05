use crate::vmir::{HeapInst, HeapVal, Inst, MemberId, Type, Val};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Resource {
    /// Parameters to the resource.
    pub params: Vec<Type>,
    /// An optional resource that serves as a precondition for this resource.
    pub requires: Option<(MemberId, Vec<Val>)>,

    /// Sequence of instructions to construct the resource.
    pub insts: Vec<Inst>,

    /// The resulting heap delta and the boolean condition.
    pub res: (HeapVal, Val),
}
