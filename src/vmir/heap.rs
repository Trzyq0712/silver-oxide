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
    /// `h := base <sign> acc <loc> <perm>`. Adds (or subtracts) the single
    /// location chunk at `loc` with permission `perm` to/from `base`. Pure heap
    /// accounting — no boolean is assumed or asserted (cf. `Inhale`/`Exhale`).
    Combine {
        base: HeapVal,
        sign: Sign,
        loc: Val,
        perm: Val,
    },
    /// `h := base inhale <call> <perm>`. Add the resource's delta (scaled by
    /// `perm`) to `base` **and assume** its boolean condition.
    Inhale {
        base: HeapVal,
        call: ResourceCall,
        perm: Val,
    },
    /// `h := base exhale <call> <perm>`. Subtract the resource's delta (scaled by
    /// `perm`) from `base` **and assert** its boolean condition.
    Exhale {
        base: HeapVal,
        call: ResourceCall,
        perm: Val,
    },
    /// Assign a value to a heap location in a given heap.
    /// SIDECOND: the location must have at least `write` permission.
    Assign(HeapVal, Assign),
    /// `h := fold call[base] perm`. Consume the predicate's footprint (scaled by
    /// `perm`) from `base`, assert its body's pure facts, and produce a chunk at
    /// the predicate address holding the snapshot of the consumed fields.
    Fold {
        base: HeapVal,
        call: ResourceCall,
        perm: Val,
    },
    /// `h := unfold call[base] perm`. Inverse of `Fold`: consume the predicate
    /// chunk from `base`, reproduce its footprint (fields recovered from the
    /// snapshot), and assume the body's pure facts.
    Unfold {
        base: HeapVal,
        call: ResourceCall,
        perm: Val,
    },
}

/// Whether a [`HeapInst::Combine`] adds or subtracts its operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sign {
    Add,
    Sub,
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
        // Render `name(arg, ...)` for a resource call.
        let call_head = |f: &mut Formatter<'_>, call: &ResourceCall| -> fmt::Result {
            write!(f, "{}(", self.interner.resolve(&call.resource))?;
            for (i, arg) in call.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{arg}")?;
            }
            write!(f, ")")
        };
        // Render `base <kw> call[ctx] perm` for a resource inhale/exhale.
        let resource_combine =
            |f: &mut Formatter<'_>, base: &HeapVal, kw: &str, call: &ResourceCall, perm: &Val| {
                write!(f, "{base} {kw} ")?;
                call_head(f, call)?;
                if let Some(ctx) = call.ctx_heap {
                    write!(f, "[{ctx}]")?;
                }
                write!(f, " {perm}")
            };
        match self.item {
            HeapInst::Combine {
                base,
                sign,
                loc,
                perm,
            } => write!(f, "{base} {sign} acc {loc} {perm}"),
            HeapInst::Inhale { base, call, perm } => {
                resource_combine(f, base, "inhale", call, perm)
            }
            HeapInst::Exhale { base, call, perm } => {
                resource_combine(f, base, "exhale", call, perm)
            }
            HeapInst::Assign(base, Assign { loc, val }) => {
                write!(f, "{base} assign {loc} {val}")
            }
            HeapInst::Fold { base, call, perm } => {
                write!(f, "{base} fold ")?;
                call_head(f, call)?;
                write!(f, " {perm}")
            }
            HeapInst::Unfold { base, call, perm } => {
                write!(f, "{base} unfold ")?;
                call_head(f, call)?;
                write!(f, " {perm}")
            }
        }
    }
}
