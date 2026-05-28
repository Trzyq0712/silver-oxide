use crate::vmir::Val;

/// Heap-typed value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HeapVal {
    /// The empty heap.
    Empty,
    /// A heap-typed temporary produced by an earlier heap instruction.
    Temp(usize),
}

/// Heap instructions. All heap instructions produce new heaps. `H` is the
/// context's heap-instruction extension slot.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapInst<H> {
    /// Single-chunk heap holding `perm` permission to `loc`.
    /// Initially, the location holds a fresh symbolic value.
    Acc(Acc),
    /// Heap addition (union).
    Add(HeapVal, HeapVal),
    /// Heap subtraction (difference). Subtracts the permission amounts of
    /// the second heap from the first.
    Sub(HeapVal, HeapVal),
    /// Conditional heap: `cond ? then : else`. All heap values and permission
    /// amounts get conditionally selected based on the value of `cond`.
    Ternary(Val, HeapVal, HeapVal),
    /// Context-specific heap-instruction extensions.
    Ext(H),
}

/// Access to a location with a certain permission amount.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Acc {
    /// Location to gain access to.
    pub loc: Val,
    /// Permission amount to the location.
    pub perm: Val,
}
