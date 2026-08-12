use crate::vmir::display::VmirDisplay;
use crate::vmir::{MemberId, ResourceCall, Type, Val};
use std::fmt::{self, Display, Formatter};

/// Heap-typed value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HeapVal {
    Empty,
    Temp(usize),
}

/// A permission amount attached to a heap operation.
///
/// A `wildcard` is a symbolic positive-but-unspecified share; it is legal
/// **only** here (never as a first-class [`Val`]), matching Viper. `Ite` gates a
/// permission by a boolean `Val` — this carries both `Sink::gate_perm`'s branch
/// gating and the `p > 0 ? wildcard : 0` lowering of function-context
/// permissions (so a dead branch reduces to `0`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Perm {
    /// A concrete permission value (`1/1`, `1/2`, a symbolic real, …). This is
    /// the only variant a non-wildcard program ever produces, and it lowers to
    /// exactly the same e-graph term as before the `Perm` split.
    Amount(Val),
    /// Viper's `wildcard`: a fresh positive-but-unspecified share.
    Wildcard,
    /// `cond ? then : else` over permissions.
    Ite(Val, Box<Perm>, Box<Perm>),
}

impl Perm {
    /// The zero permission (`none`).
    pub fn none() -> Self {
        Perm::Amount(crate::vmir::none())
    }
    /// The full permission (`write`, `1/1`).
    pub fn write() -> Self {
        Perm::Amount(crate::vmir::write())
    }
    /// Whether any leaf of this permission is a [`Perm::Wildcard`].
    pub fn has_wildcard(&self) -> bool {
        match self {
            Perm::Amount(_) => false,
            Perm::Wildcard => true,
            Perm::Ite(_, t, e) => t.has_wildcard() || e.has_wildcard(),
        }
    }
}

impl Display for VmirDisplay<'_, &Perm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            Perm::Amount(v) => write!(f, "{v}"),
            Perm::Wildcard => write!(f, "wildcard"),
            Perm::Ite(c, t, e) => {
                write!(f, "{c} ? {} : {}", self.with(&**t), self.with(&**e))
            }
        }
    }
}

/// Heap instructions. All heap instructions produce new heaps.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapInst {
    /// `h := base + acc <loc> <perm> with <bind>`. Adds the single location
    /// chunk at `loc` with permission `perm` to `base`. Pure heap accounting —
    /// no boolean is assumed or asserted (cf. `Inhale`/`Exhale`).
    ///
    /// `bind` says where the chunk's **value** comes from. It is always written
    /// and never defaulted: producing a value is the operation with soundness
    /// consequences, so the dangerous case (`Fresh`) must not be the one a
    /// reader skips.
    Add {
        base: HeapVal,
        loc: Val,
        perm: Perm,
        bind: Bind,
    },
    /// `h := base - acc <loc> <perm>`. Subtracts the single location chunk at
    /// `loc` with permission `perm` from `base`. Pure heap accounting — no
    /// boolean is assumed or asserted (cf. `Inhale`/`Exhale`).
    Sub {
        base: HeapVal,
        loc: Val,
        perm: Perm,
    },
    /// `h[, s] := base inhale <call> <perm>`. Add the resource's delta (scaled by
    /// `perm`) to `base` **and assume** its boolean condition. When the callee is
    /// **self-framed** the inst additionally yields a pure `Val` `s : Snap(callee)`
    /// — the snapshot of the just-inhaled resource (see [`HeapInst::snap_yield`]),
    /// passed on as the trailing snapshot argument of a two-state resource call.
    Inhale {
        base: HeapVal,
        /// Where the produced footprint's values come from. `Fresh` havocs each
        /// slot (a call's post-state); `Bound(s)` recovers them from an in-scope
        /// snapshot as `unwrap(proj_i(s))`, which is what makes a method's entry
        /// heap and the pre-state its `#ensures` reconstructs the *same* terms.
        bind: Bind,
        call: ResourceCall,
        perm: Perm,
    },
    /// `h[, s] := base exhale <call> <perm>`. Subtract the resource's delta (scaled by
    /// `perm`) from `base` **and assert** its boolean condition. Yields a snapshot
    /// `Val` exactly like `Inhale` (values = the consumed caller chunk values).
    Exhale {
        base: HeapVal,
        call: ResourceCall,
        perm: Perm,
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
        perm: Perm,
    },
    /// `h := unfold call[base] perm`. Inverse of `Fold`: consume the predicate
    /// chunk from `base`, reproduce its footprint (fields recovered from the
    /// snapshot), and assume the body's pure facts.
    Unfold {
        base: HeapVal,
        call: ResourceCall,
        perm: Perm,
    },
    /// `h := heap_of R(args), snap` — widen a snapshot value back into a heap:
    /// `h := merge <cond> ? <then_h> : <els_h>` — the block-IR heap join: select
    /// between two predecessor exit heaps under a binary join condition. The
    /// *structural* per-chunk merge (`design/block-vmir/30`) that collapses the
    /// exit permission tower lives in its evaluation. **Not emitted yet** — the
    /// block lowering threads a single linear heap for now; this variant is
    /// declared so the type is stable ahead of the structural-join stage.
    Merge {
        cond: Val,
        then_h: HeapVal,
        els_h: HeapVal,
    },
    /// `h := union <a> <b>` — the **sum** of two heaps held simultaneously, as
    /// opposed to [`HeapInst::Merge`], which *selects* between two alternative
    /// predecessor states. Permissions at a shared location add; values at a
    /// shared location are assumed equal (two chunks of one location cannot
    /// disagree).
    ///
    /// Emitted where a loop is left: the body holds the invariant's footprint and
    /// the head set the rest aside as the frame, so the state after the loop is
    /// their sum. Silicon does the same at a `Kind.Out` edge; our heaps are explicit
    /// values, so the frame is simply named.
    Union { a: HeapVal, b: HeapVal },
}

impl HeapInst {
    /// The resource whose snapshot this instruction *additionally* yields as a
    /// pure `Val` (bumping the `Val` counter): an `Inhale`/`Exhale` of a
    /// **self-framed** resource produces `s : Snap(callee)` alongside the new
    /// heap. Two-state callees (and every other heap inst) yield none. Derived
    /// from the callee declaration — not stored on the inst.
    /// The extra pure `Val` this instruction yields, and its type.
    ///
    ///  - `Inhale`/`Exhale` of a **self-framed** callee → `Snap(callee)`, plain.
    ///  - `Sub` → `Option<T>`, where `T` is the held value type of `loc`: the
    ///    instruction *discovers* whether the location held anything, and `None`
    ///    reports that it did not. This is the one position where optionality
    ///    belongs, because it is the one place presence is discovered rather than
    ///    supplied — `Add`'s `bind` and both resource ops hand a value over.
    ///  - everything else → none.
    ///
    /// Derived, never stored, like [`HeapInst::snap_yield`] which it generalizes.
    /// `val_ty` resolves an operand's VMIR type; both callers already track it
    /// (the translator in its `Sink`, the verifier in `EvalState::val_types`).
    ///
    /// NOTE: the `Sub` arm has no consumer yet — the `Option` is threaded when
    /// `unfold` is desugared into a `Sub` + `Inhale` pair. Until then nothing
    /// pushes this `Val`, so temp numbering is unchanged.
    pub fn val_yield(
        &self,
        decls: &typed_index_collections::TiVec<MemberId, crate::vmir::Declaration>,
        val_ty: impl Fn(&Val) -> Option<Type>,
    ) -> Option<Type> {
        match self {
            HeapInst::Sub { loc, .. } => {
                let held = val_ty(loc)?.addr_value()?.clone();
                Some(Type::Option(Box::new(held)))
            }
            _ => self.snap_yield(decls).map(Type::Snap),
        }
    }

    pub fn snap_yield(
        &self,
        decls: &typed_index_collections::TiVec<MemberId, crate::vmir::Declaration>,
    ) -> Option<MemberId> {
        match self {
            // `Inhale` yields nothing: its value source arrives through `bind`,
            // so there is no snapshot left for it to hand back. A caller that
            // needs the handle mints one and binds the inhale to it.
            HeapInst::Exhale { call, .. } => {
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

/// Where a produced chunk's value comes from — the IR half of the verifier's
/// `ValueSource`. Deliberately *not* the same type: `ValueSource` names e-class
/// ids and recipe terms, which the IR does not have.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Bind {
    /// Havoc — surface `with fresh`. An unconstrained fresh value per slot.
    /// Legal only at an instruction in a **method** body: a resource body that
    /// minted a fresh observable value would not be deterministic.
    Fresh,
    /// Bound to an in-scope term — surface `with <val>`.
    Bound(Val),
    /// The **next** slot of the enclosing resource's own footprint — surface
    /// `with self`. Deliberately **unnumbered**: writing `self.2` would
    /// presuppose the slot layout, and the layout is *derived* from the body, so
    /// the body would reference its own derived structure. Unnumbered, the
    /// ordinal is a consequence of position and the circularity is gone.
    SelfSlot,
}

impl Display for Bind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Bind::Fresh => write!(f, "fresh"),
            Bind::Bound(v) => write!(f, "{v}"),
            Bind::SelfSlot => write!(f, "self"),
        }
    }
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
            |f: &mut Formatter<'_>, base: &HeapVal, kw: &str, call: &ResourceCall, perm: &Perm| {
                write!(f, "{base} {kw} ")?;
                call_head(f, call)?;
                write!(f, " {}", self.with(perm))
            };
        match self.item {
            HeapInst::Add {
                base,
                loc,
                perm,
                bind,
            } => write!(f, "{base} + acc {loc} {} with {bind}", self.with(perm)),
            HeapInst::Sub { base, loc, perm } => {
                write!(f, "{base} - acc {loc} {}", self.with(perm))
            }
            HeapInst::Inhale {
                base,
                bind,
                call,
                perm,
            } => {
                resource_combine(f, base, "inhale", call, perm)?;
                write!(f, " with {bind}")
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
                write!(f, " {}", self.with(perm))
            }
            HeapInst::Unfold { base, call, perm } => {
                write!(f, "{base} unfold ")?;
                call_head(f, call)?;
                write!(f, " {}", self.with(perm))
            }
            HeapInst::Merge {
                cond,
                then_h,
                els_h,
            } => write!(f, "merge {cond} ? {then_h} : {els_h}"),
            HeapInst::Union { a, b } => write!(f, "union {a} {b}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vmir::{Bound, Perm};
    use lasso::Rodeo;
    use typed_index_collections::TiVec;

    fn addr_ty(value: Type) -> Type {
        let mut groups: Rodeo<lasso::Spur> = Rodeo::new();
        Type::Addr {
            group: groups.get_or_intern("f"),
            value: Box::new(value),
            bound: Bound::Bounded(num::BigRational::from(num::BigInt::from(1))),
        }
    }

    /// `Sub` yields `Option<T>` for the *held value* type of its location — the
    /// one place presence is discovered rather than supplied.
    #[test]
    fn sub_yields_option_of_the_held_value_type() {
        let decls: TiVec<MemberId, crate::vmir::Declaration> = TiVec::new();
        let inst = HeapInst::Sub {
            base: HeapVal::Empty,
            loc: Val::Temp(0),
            perm: Perm::write(),
        };
        let got = inst.val_yield(&decls, |_| Some(addr_ty(Type::Int)));
        assert_eq!(got, Some(Type::Option(Box::new(Type::Int))));
    }

    /// A predicate location yields `Option<Snap(P)>`, which is what makes the
    /// desugared `unfold` able to hand the snapshot to its paired `inhale`.
    #[test]
    fn sub_on_a_predicate_location_yields_option_of_its_snapshot() {
        let decls: TiVec<MemberId, crate::vmir::Declaration> = TiVec::new();
        let pred = MemberId(7);
        let inst = HeapInst::Sub {
            base: HeapVal::Empty,
            loc: Val::Temp(0),
            perm: Perm::write(),
        };
        let got = inst.val_yield(&decls, |_| Some(addr_ty(Type::Snap(pred))));
        assert_eq!(got, Some(Type::Option(Box::new(Type::Snap(pred)))));
    }

    /// `Add` supplies its value through `bind`, so it discovers nothing and
    /// yields nothing.
    #[test]
    fn add_yields_nothing() {
        let decls: TiVec<MemberId, crate::vmir::Declaration> = TiVec::new();
        let inst = HeapInst::Add {
            base: HeapVal::Empty,
            loc: Val::Temp(0),
            perm: Perm::write(),
            bind: Bind::Fresh,
        };
        assert_eq!(inst.val_yield(&decls, |_| Some(addr_ty(Type::Int))), None);
    }

    /// A bind renders as `with <source>`, and the `Fresh` case is never silent.
    #[test]
    fn bind_display_is_explicit() {
        assert_eq!(Bind::Fresh.to_string(), "fresh");
        assert_eq!(Bind::SelfSlot.to_string(), "self");
        assert_eq!(Bind::Bound(Val::Temp(4)).to_string(), "e4");
    }
}
