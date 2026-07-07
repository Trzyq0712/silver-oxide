//! The instruction [`Sink`]: a mutable buffer of emitted VMIR `Inst`s plus the
//! running SSA counters and path-condition stack. The instruction set is
//! uniform; how the resulting stream is interpreted is the caller's concern
//! (resource delta+bool, method effects, function result).

use std::collections::VecDeque;

use crate::vmir::{
    self, BinOp, HeapInst, HeapVal, Inst, InstKind, MemberId, PathConds, Polarity, PureInst,
    Quantifier, ResourceCall, Sign, Type, Val, none,
};

/// Why a condition sits on the path-condition stack. Both kinds gate the
/// **side conditions** of the instructions under them (they go on the emitted
/// `pc`), but only a `Branch` gates **permission amounts**:
/// - `Branch` — a case split (`b ==> ..`, `c ? .. : ..`); the dead arm needs 0
///   permission, so the perm is wrapped `b ? p : 0`.
/// - `Fact` — the left operand of a separating conjunction `A && B`; an
///   *assertion* that aborts if false, so `B`'s permissions stay ungated (no
///   spurious `A ? p : 0`).

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PcKind {
    Branch,
    Fact,
}

/// A mutable sink for emitted instructions plus the running counters. The
/// instruction set is uniform; how the resulting stream is interpreted is the
/// caller's concern (resource delta+bool, method effects, function result).
pub(crate) struct Sink {
    pub insts: Vec<Inst>,
    pub val_base: usize,
    pub val_count: usize,
    pub heap_count: usize,
    /// Running path condition of the lowering point. Sidecond instructions
    /// are emitted gated by this; branch arms push/pop guards via `with_cond`.
    pub pc: Vec<(Val, Polarity, PcKind)>,
    /// The current heap an obligation's side condition is checked in. Delivered
    /// like `pc`: set for a lowering region via [`Sink::with_heap`], snapshotted
    /// onto a heapless obligation's `Inst` by the emitters. `None` outside any
    /// heap-bearing region (e.g. before the first heap is threaded).
    pub heap: Option<HeapVal>,
    /// Pre-allocated occurrence ids for the `forall`s in this lowering region,
    /// in encounter (preorder) order. Each `forall` pops the next id to emit its
    /// nullary occurrence call; an empty queue means an unexpected (nested)
    /// `forall`. Empty in every Sink except an axiom body's.
    pub quant_ids: VecDeque<MemberId>,
    /// Quantifier declarations built while lowering this region's `forall`s,
    /// paired with their occurrence id, for the caller to fill their slots.
    pub quant_out: Vec<(MemberId, Quantifier)>,
}

impl Sink {
    pub fn new(val_base: usize, heap_base: usize) -> Self {
        Self {
            insts: Vec::new(),
            val_base,
            val_count: 0,
            heap_count: heap_base,
            pc: Vec::new(),
            heap: None,
            quant_ids: VecDeque::new(),
            quant_out: Vec::new(),
        }
    }

    /// Run `f` with `heap` as the current obligation check-in heap, restoring the
    /// prior heap afterwards (analogous to [`Sink::with_cond`] for `pc`). The
    /// restore runs even when `f` returns `Err`.
    pub(crate) fn with_heap<R>(&mut self, heap: HeapVal, f: impl FnOnce(&mut Self) -> R) -> R {
        let prev = self.heap.replace(heap);
        let r = f(self);
        self.heap = prev;
        r
    }

    /// Build an obligation instruction, attaching the current check-in heap when
    /// one is set (see [`Sink::heap`]).
    fn checked_inst(&self, pc: PathConds, kind: InstKind) -> Inst {
        match self.heap {
            Some(h) => Inst::in_heap(pc, h, kind),
            None => Inst::new(pc, kind),
        }
    }

    pub(crate) fn with_cond<R>(
        &mut self,
        cond: Val,
        pol: Polarity,
        kind: PcKind,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.pc.push((cond, pol, kind));
        let r = f(self);
        self.pc.pop();
        r
    }

    /// Run `f` with every literal of `conds` pushed as a `Branch` guard (the
    /// reaching condition of a CFG block), popping them all afterwards. Used by
    /// the method-body linearizer to lower a basic block under its path
    /// condition. The pops run even when `f` returns `Err`.
    pub(crate) fn with_conds<R>(&mut self, conds: &PathConds, f: impl FnOnce(&mut Self) -> R) -> R {
        for (cond, pol) in &conds.conds {
            self.pc.push((cond.clone(), *pol, PcKind::Branch));
        }
        let r = f(self);
        for _ in &conds.conds {
            self.pc.pop();
        }
        r
    }

    /// The currently-active **branch** path-condition literals (the ones that
    /// gate permissions); `Fact` entries are excluded.
    pub(crate) fn branch_conds(&self) -> Vec<(Val, Polarity)> {
        self.pc
            .iter()
            .filter(|(_, _, k)| *k == PcKind::Branch)
            .map(|(c, p, _)| (c.clone(), *p))
            .collect()
    }

    /// Gate a permission amount by the current branch path condition: each branch
    /// literal wraps `perm` in a ternary, with `none` (0) on the *dead* side. A
    /// positive literal `b` yields `b ? perm : none`; a negative literal (the else
    /// arm) yields `b ? none : perm` — flipped branches instead of a materialized
    /// `!b`. The empty path condition (top level) returns `perm` unchanged. Only
    /// *branch* conditions gate: a separating-conjunction `Fact` is an assertion
    /// (abort if false), so its `acc` keeps the bare permission.
    pub(crate) fn gate_perm(&mut self, perm: Val) -> Val {
        let mut v = perm;
        // Innermost literal first, so the outermost guard ends outermost.
        for (lit, pol) in self.branch_conds().into_iter().rev() {
            let (then_, else_) = match pol {
                Polarity::Positive => (v, none()),
                Polarity::Negative => (none(), v),
            };
            v = self.emit_pure(Type::Real, PureInst::Ternary(lit, then_, else_));
        }
        v
    }

    /// Gate a written *value* by the current branch path condition, keeping the
    /// prior value `old` on the dead side: each branch literal wraps the value in a
    /// `lit ? val : old` (positive) or `lit ? old : val` (negative). Used for a
    /// field assignment inside an `if` arm, where the heap is a single timeline (no
    /// heap ternary) so the *value* must carry the branch instead of the chunk. The
    /// empty top-level pc returns `val` unchanged.
    pub(crate) fn gate_value(&mut self, val: Val, old: Val, ty: Type) -> Val {
        let mut v = val;
        for (lit, pol) in self.branch_conds().into_iter().rev() {
            let (then_, else_) = match pol {
                Polarity::Positive => (v, old.clone()),
                Polarity::Negative => (old.clone(), v),
            };
            v = self.emit_pure(ty.clone(), PureInst::Ternary(lit, then_, else_));
        }
        v
    }

    pub fn next_val_temp(&mut self) -> Val {
        let id = self.val_base + self.val_count;
        self.val_count += 1;
        Val::Temp(id)
    }

    pub fn next_heap_temp(&mut self) -> HeapVal {
        let id = self.heap_count;
        self.heap_count += 1;
        HeapVal::Temp(id)
    }

    /// A snapshot of the running path condition, to attach to a side-condition
    /// instruction. Empty outside any branch.
    fn guard(&self) -> PathConds {
        PathConds {
            conds: self.pc.iter().map(|(c, p, _)| (c.clone(), *p)).collect(),
        }
    }

    /// Emit a **total** pure instruction (no side condition) — flat, no pc.
    pub fn emit_pure(&mut self, ty: vmir::Type, inst: PureInst) -> Val {
        let v = self.next_val_temp();
        self.insts
            .push(Inst::new(PathConds::default(), InstKind::Pure(ty, inst)));
        v
    }

    /// Emit a pure instruction whose side condition (e.g. `Deref` permission,
    /// `Div`/`Mod` divisor) must hold under the running path condition. A
    /// `Div`/`Mod` has no embedded heap, so it snapshots the current check-in heap
    /// (see [`Sink::heap`]); a `Deref`/`Perm` embeds its own heap, so it does not.
    pub fn emit_pure_guarded(&mut self, ty: vmir::Type, inst: PureInst) -> Val {
        let v = self.next_val_temp();
        let pc = self.guard();
        let heapless_obligation = matches!(inst, PureInst::Binary(BinOp::Div | BinOp::Mod, _, _));
        let kind = InstKind::Pure(ty, inst);
        let node = if heapless_obligation {
            self.checked_inst(pc, kind)
        } else {
            Inst::new(pc, kind)
        };
        self.insts.push(node);
        v
    }

    /// Emit a **total** heap instruction (no side condition) — e.g. `Add`.
    pub fn emit_heap(&mut self, inst: HeapInst) -> HeapVal {
        let h = self.next_heap_temp();
        self.insts
            .push(Inst::new(PathConds::default(), InstKind::Heap(inst)));
        h
    }

    /// Emit a heap instruction whose side condition (`Acc` perm ≥ 0, `Sub`
    /// sufficient perm, `Assign` write perm) must hold under the running pc.
    pub fn emit_heap_guarded(&mut self, inst: HeapInst) -> HeapVal {
        let h = self.next_heap_temp();
        let pc = self.guard();
        self.insts.push(Inst::new(pc, InstKind::Heap(inst)));
        h
    }

    pub fn emit_assume(&mut self, v: Val) {
        let pc = self.guard();
        self.insts.push(Inst::new(pc, InstKind::Assume(v)));
    }

    pub fn emit_assert(&mut self, v: Val) {
        let pc = self.guard();
        let node = self.checked_inst(pc, InstKind::Assert(v));
        self.insts.push(node);
    }

    pub fn emit_refute(&mut self, v: Val) {
        let pc = self.guard();
        let node = self.checked_inst(pc, InstKind::Refute(v));
        self.insts.push(node);
    }

    /// Emit a resource inhale (`base inhale call perm`, assumes the bool) or
    /// exhale (`base exhale call perm`, asserts the bool). Inhale is total;
    /// exhale carries the running pc as its side-condition guard.
    ///
    /// When `yields_snap` (the callee is self-framed) the inst additionally
    /// produces a pure `Val` — the snapshot of the in/ex-haled resource — so the
    /// `Val` counter bumps alongside the heap counter.
    pub fn emit_resource_combine(
        &mut self,
        base: HeapVal,
        sign: Sign,
        call: ResourceCall,
        perm: Val,
        yields_snap: bool,
    ) -> (HeapVal, Option<Val>) {
        let h = match sign {
            Sign::Add => self.emit_heap(HeapInst::Inhale { base, call, perm }),
            Sign::Sub => self.emit_heap_guarded(HeapInst::Exhale { base, call, perm }),
        };
        let snap = yields_snap.then(|| self.next_val_temp());
        (h, snap)
    }
}
