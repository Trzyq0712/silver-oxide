use crate::vmir::{HeapVal, Inst, InstContext, ResourceCall, Val};

pub struct MethodCtx;

impl InstContext for MethodCtx {
    type InstExt = InstExt;
    type HeapExt = HeapExt;
}

/// Method-specific instruction extensions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstExt {
    Assume(Val),
    Assert(Val),
    ResourceCall(ResourceCall),
}

/// Method-specific heap-instruction extensions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapExt {
    /// Assign a value to a heap location in a given heap.
    /// SIDECOND: The heap location must have at least `write` amount of
    /// permission.
    Assign(HeapVal, Assign),
}

/// Assign a value to a heap location.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assign {
    /// Location to assign to.
    pub loc: Val,
    /// Value to assign.
    pub val: Val,
}

/// Concrete `Inst` for method bodies.
pub type MethodInst = Inst<MethodCtx>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub insts: Vec<MethodInst>,
}
