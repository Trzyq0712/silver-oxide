use crate::vmir::{ty::Type, PureInst, Value};

/// A typed SSA instruction
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HeapInst {
    pub kind: HeapInstKind,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapInstKind {
    Pure(PureInst),
    Acc(AccInst),
}

/// Modify the heap by changing the amount of permission we have for an address
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AccInst {
    pub heap: Value,
    pub addr: Value,
    pub perm: Value,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HeapExp {
    /// Types of inputs this heap expression expects
    /// For requires: [heap, ...method_args]
    /// For ensures: [heap, old_heap, ...method_args, ...returns]
    pub input_types: Vec<Type>,
    pub insts: Vec<HeapInst>,
    /// The pure result - a boolean
    pub res_pure: Value,
    /// The impure part - a heap
    pub res_impure: Value,
}
