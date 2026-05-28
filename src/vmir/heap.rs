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

/// Common rendering for the shared `HeapInst` variants. Used by the
/// per-`H` Display impls below.
fn fmt_shared<H>(inst: &HeapInst<H>, f: &mut Formatter<'_>) -> Option<fmt::Result> {
    match inst {
        HeapInst::Acc(Acc { loc, perm }) => Some(write!(f, "acc({loc}, {perm})")),
        HeapInst::Add(lhs, rhs) => Some(write!(f, "{lhs} + {rhs}")),
        HeapInst::Sub(lhs, rhs) => Some(write!(f, "{lhs} - {rhs}")),
        HeapInst::Ternary(cond, lhs, rhs) => Some(write!(f, "{cond} ? {lhs} : {rhs}")),
        HeapInst::Ext(_) => None,
    }
}

/// `Display for HeapInst<!>` — the `Ext` arm is uninhabited.
impl Display for HeapInst<!> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(r) = fmt_shared(self, f) {
            return r;
        }
        match self {
            _ => unreachable!(),
        }
    }
}

/// Body for `Display for HeapInst<H>` when `H: Display` (i.e. an
/// inhabited extension type). The `!` case gets its own impl above to
/// sidestep the missing `Display for !`. Note: this helper exists
/// because a blanket `impl<H: Display>` would collide with the
/// `HeapInst<!>` impl.
pub(crate) fn write_heap_inst_with<H: Display>(
    inst: &HeapInst<H>,
    f: &mut Formatter<'_>,
) -> fmt::Result {
    if let Some(r) = fmt_shared(inst, f) {
        return r;
    }
    match inst {
        HeapInst::Ext(ext) => write!(f, "{ext}"),
        _ => unreachable!(),
    }
}
