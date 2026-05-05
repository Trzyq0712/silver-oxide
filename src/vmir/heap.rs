use crate::vmir::Val;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HeapVal {
    Empty,
    Implicit,
    Temp(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapInst {
    Acc(Acc),
    Add(HeapVal, HeapVal),
    Sub(HeapVal, HeapVal),
    Ternary(Val, HeapVal, HeapVal),
    Assign(HeapVal, Val),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Acc {
    /// Location to gain access to
    pub loc: Val,
    /// Permission amount to the location
    pub perm: Val,
}
