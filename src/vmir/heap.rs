use crate::vmir::Val;
use std::fmt::{self, Display, Formatter};

/// Heap-typed value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HeapVal {
    Empty,
    Temp(usize),
}

/// Heap instructions. All heap instructions produce new heaps. `H` is the
/// context's heap-instruction extension slot.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapInst<H> {
    /// Single-chunk heap holding `perm` permission to `loc`.
    Acc(Acc),
    /// Heap addition (union).
    Add(HeapVal, HeapVal),
    /// Heap subtraction (difference).
    Sub(HeapVal, HeapVal),
    /// Conditional heap: `cond ? then : else`.
    Ternary(Val, HeapVal, HeapVal),
    /// Context-specific heap-instruction extensions.
    Ext(H),
}

/// Access to a location with a certain permission amount.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Acc {
    pub loc: Val,
    pub perm: Val,
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

/// Rendering hook for the `HeapInst::Ext` payload. Symmetric to
/// `PureExtRender` — sidesteps the `Display for !` orphan-rule problem
/// and lets `Display for HeapInst<H>` live as a single generic impl.
pub trait HeapExtRender {
    fn render(&self, f: &mut Formatter<'_>) -> fmt::Result;
}

impl HeapExtRender for ! {
    fn render(&self, _: &mut Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}

impl<H: HeapExtRender> Display for HeapInst<H> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HeapInst::Acc(Acc { loc, perm }) => write!(f, "acc({loc}, {perm})"),
            HeapInst::Add(lhs, rhs) => write!(f, "{lhs} + {rhs}"),
            HeapInst::Sub(lhs, rhs) => write!(f, "{lhs} - {rhs}"),
            HeapInst::Ternary(cond, lhs, rhs) => write!(f, "{cond} ? {lhs} : {rhs}"),
            HeapInst::Ext(ext) => ext.render(f),
        }
    }
}
