use crate::vmir::display::VmirDisplay;
use crate::vmir::{MemberId, ResourceCall, Val};
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
    /// `h[, s] := base inhale <call> <perm>`. Add the resource's delta (scaled by
    /// `perm`) to `base` **and assume** its boolean condition. When the callee is
    /// **self-framed** the inst additionally yields a pure `Val` `s : Snap(callee)`
    /// — the snapshot of the just-inhaled resource (see [`HeapInst::snap_yield`]),
    /// passed on as the trailing snapshot argument of a two-state resource call.
    Inhale {
        base: HeapVal,
        call: ResourceCall,
        perm: Val,
    },
    /// `h[, s] := base exhale <call> <perm>`. Subtract the resource's delta (scaled by
    /// `perm`) from `base` **and assert** its boolean condition. Yields a snapshot
    /// `Val` exactly like `Inhale` (values = the consumed caller chunk values).
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
    /// `h := heap_of R(args), snap` — widen a snapshot value back into a heap:
    /// one chunk per footprint slot of the self-framed resource `R(args)`, at
    /// `addr_k` with permission `perm_k` (presence-gated) and value
    /// `unwrap(proj_k(snap))`; the resource's boolean condition is **assumed**
    /// implicitly. Inverse of [`PureInst::Snap`](crate::vmir::PureInst::Snap);
    /// value-preserving like `Unfold` (values come from the snapshot), not
    /// opaque like `Inhale`. Used at the entry of a heap-dependent function
    /// body to reconstruct the precondition heap from the snapshot parameter.
    FromSnap {
        resource: MemberId,
        args: Vec<Val>,
        snap: Val,
    },
}

impl HeapInst {
    /// The resource whose snapshot this instruction *additionally* yields as a
    /// pure `Val` (bumping the `Val` counter): an `Inhale`/`Exhale` of a
    /// **self-framed** resource produces `s : Snap(callee)` alongside the new
    /// heap. Two-state callees (and every other heap inst) yield none. Derived
    /// from the callee declaration — not stored on the inst.
    pub fn snap_yield(
        &self,
        decls: &typed_index_collections::TiVec<MemberId, crate::vmir::Declaration>,
    ) -> Option<MemberId> {
        match self {
            HeapInst::Inhale { call, .. } | HeapInst::Exhale { call, .. } => {
                match &decls[call.resource] {
                    crate::vmir::Declaration::Resource(r) if r.is_self_framed() => {
                        Some(call.resource)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
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
            write!(f, "{}(", self.member(call.resource))?;
            for (i, arg) in call.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{arg}")?;
            }
            write!(f, ")")
        };
        // Render `base <kw> call perm` for a resource inhale/exhale.
        let resource_combine =
            |f: &mut Formatter<'_>, base: &HeapVal, kw: &str, call: &ResourceCall, perm: &Val| {
                write!(f, "{base} {kw} ")?;
                call_head(f, call)?;
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
            HeapInst::FromSnap {
                resource,
                args,
                snap,
            } => {
                write!(f, "heap_of {}(", self.member(*resource))?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, "), {snap}")
            }
        }
    }
}
