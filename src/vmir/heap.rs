use crate::vmir::display::VmirDisplay;
use crate::vmir::{ResourceCall, Val};
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
    /// `h := base <sign> acc <target> <perm>`. Adds (or subtracts) the access
    /// to `target` with permission `perm` to/from `base`. When `target` is a
    /// `Resource`, the resource's boolean is implicitly assumed (`Add`) or
    /// asserted (`Sub`).
    Combine {
        base: HeapVal,
        sign: Sign,
        target: Target,
        perm: Val,
    },
    /// Assign a value to a heap location in a given heap.
    /// SIDECOND: the location must have at least `write` permission.
    Assign(HeapVal, Assign),
}

/// Whether a [`HeapInst::Combine`] adds or subtracts its operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sign {
    Add,
    Sub,
}

/// What a [`HeapInst::Combine`] accesses.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Target {
    /// A single location (field/predicate `@addr`): one chunk at `loc`.
    Loc(Val),
    /// A whole resource delta (scaled by the combine's `perm`); its boolean is
    /// implicitly assumed/asserted depending on the combine's `sign`.
    Resource(ResourceCall),
}

/// Assign a value to a heap location.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assign {
    pub loc: Val,
    pub val: Val,
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

impl Display for Sign {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Sign::Add => write!(f, "+"),
            Sign::Sub => write!(f, "-"),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a HeapInst> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            HeapInst::Combine {
                base,
                sign,
                target,
                perm,
            } => match target {
                Target::Loc(loc) => write!(f, "{base} {sign} acc {loc} {perm}"),
                Target::Resource(call) => {
                    write!(f, "{base} {sign} acc {}(", self.interner.resolve(&call.resource))?;
                    for (i, arg) in call.args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{arg}")?;
                    }
                    write!(f, ")[{}] {perm}", call.ctx_heap)
                }
            },
            HeapInst::Assign(heap, Assign { loc, val }) => {
                write!(f, "assign[{heap}] {loc} := {val}")
            }
        }
    }
}
