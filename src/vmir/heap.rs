use crate::vmir::Val;
use std::fmt::{self, Display, Formatter};

/// Heap-typed value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HeapVal {
    Empty,
    Temp(usize),
}

/// Heap instructions. All heap instructions produce new heaps.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapInst {
    /// Single-chunk heap holding `perm` permission to `loc`.
    Acc(Acc),
    /// Heap addition (union).
    Add(HeapVal, HeapVal),
    /// Heap subtraction (difference).
    Sub(HeapVal, HeapVal),
    /// Conditional heap: `cond ? then : else`.
    Ternary(Val, HeapVal, HeapVal),
    /// Assign a value to a heap location in a given heap.
    /// SIDECOND: the location must have at least `write` permission.
    Assign(HeapVal, Assign),
}

/// Access to a location with a certain permission amount.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Acc {
    pub loc: Val,
    pub perm: Val,
}

/// Assign a value to a heap location.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assign {
    pub loc: Val,
    pub val: Val,
}

impl HeapInst {
    pub fn uses_pc(&self) -> bool {
        match self {
            // Acc: perm ≥ 0. Add: chunk-merge equalities are conditional
            // on the chunks' perm being positive. Sub: enough perm.
            // Assign: location must have write permission.
            HeapInst::Acc(_) | HeapInst::Add(..) | HeapInst::Sub(..) | HeapInst::Assign(..) => true,
            HeapInst::Ternary(..) => false,
        }
    }
}

// ======================
// DISPLAY INFRASTRUCTURE
// ======================

impl Display for HeapVal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HeapVal::Empty => write!(f, "empty"),
            HeapVal::Temp(i) => write!(f, "h{i}"),
        }
    }
}

impl Display for HeapInst {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HeapInst::Acc(Acc { loc, perm }) => write!(f, "acc({loc}, {perm})"),
            HeapInst::Add(lhs, rhs) => write!(f, "{lhs} + {rhs}"),
            HeapInst::Sub(lhs, rhs) => write!(f, "{lhs} - {rhs}"),
            HeapInst::Ternary(cond, lhs, rhs) => write!(f, "{cond} ? {lhs} : {rhs}"),
            HeapInst::Assign(heap, Assign { loc, val }) => {
                write!(f, "assign[{heap}] {loc} := {val}")
            }
        }
    }
}
