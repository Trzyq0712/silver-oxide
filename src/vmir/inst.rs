use crate::vmir::display::VmirDisplay;
use crate::vmir::{HeapInst, HeapVal, PureInst, Type, Val};

use std::fmt::{self, Display, Formatter};

/// An instruction gated by a path condition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst {
    pub pc: PathConds,
    /// The heap this instruction's side condition must be **checked in** — the
    /// heap the verifier will consolidate (materialising aliasing-dependent
    /// facts) before discharging the obligation. Delivered like [`PathConds`]:
    /// snapshotted onto the `Inst` by the guarded emitters. `None` when the
    /// instruction has no obligation, or when the relevant heap is already
    /// embedded in `kind` (a `Deref`/`Perm` heap, an `Exhale`/`Fold`/`Assign`
    /// base, a `FunctionCall` ctx heap). Populated only for the heapless
    /// obligations `Assert`, `Refute`, and `Div`/`Mod`.
    pub heap: Option<HeapVal>,
    pub kind: InstKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstKind {
    /// Produces a temporary of a given type.
    Pure(Type, PureInst),
    /// Produces a heap value.
    Heap(HeapInst),
    /// Assume a boolean fact. Produces no value.
    Assume(Val),
    /// Assert a boolean obligation. Produces no value.
    Assert(Val),
    /// Refute a boolean: verification succeeds iff it is **not** provable.
    /// Produces no value.
    Refute(Val),
}

/// Conjunction of literals over previously-emitted `Val`s.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct PathConds {
    pub conds: Vec<(Val, Polarity)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Polarity {
    Positive,
    Negative,
}

impl From<bool> for Polarity {
    fn from(b: bool) -> Self {
        if b {
            Polarity::Positive
        } else {
            Polarity::Negative
        }
    }
}

impl Inst {
    /// Construct an instruction with no check-in heap. A non-empty `pc` gates the
    /// instruction's side condition; the translation attaches one only where it is
    /// needed (see the `*_guarded` emitters in `translate`).
    pub fn new(pc: PathConds, kind: InstKind) -> Self {
        Self {
            pc,
            heap: None,
            kind,
        }
    }

    /// Construct an obligation instruction carrying the `heap` its side condition
    /// is checked in (see [`Inst::heap`]).
    pub fn in_heap(pc: PathConds, heap: HeapVal, kind: InstKind) -> Self {
        Self {
            pc,
            heap: Some(heap),
            kind,
        }
    }
}

// ======================
// DISPLAY INFRASTRUCTURE
// ======================

/// Walk an instruction stream. Wraps `(val_base, heap_base, &[Inst])` in a
/// `VmirDisplay` so the iteration lives behind a regular `Display` impl.
/// Callers — `Display for VmirDisplay<&Method>`, `&Resource>`, `&ResourceBody>`
/// — invoke via `self.with((val_base, heap_base, &insts[..]))`.
impl<'a> Display for VmirDisplay<'a, (usize, usize, &'a [Inst])> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (val_base, heap_base, insts) = self.item;
        let mut e_idx = val_base;
        let mut h_idx = heap_base;
        for inst in insts {
            // The check-in heap of an obligation, rendered `[h3]` where it belongs
            // (after a `Pure` expression as a suffix, after the `assert`/`refute`
            // keyword). Empty for a `None` heap.
            let heap = HeapSuffix(&inst.heap);
            match &inst.kind {
                InstKind::Pure(ty, pi) => {
                    writeln!(
                        f,
                        "  e{e_idx}: {} := {}{}{heap}",
                        self.with(ty),
                        PcPrefix(&inst.pc),
                        self.with(pi)
                    )?;
                    e_idx += 1;
                }
                InstKind::Heap(hi) => {
                    writeln!(f, "  h{h_idx} := {}{}", PcPrefix(&inst.pc), self.with(hi))?;
                    h_idx += 1;
                }
                InstKind::Assume(v) => writeln!(f, "  {}assume {v}", PcPrefix(&inst.pc))?,
                InstKind::Assert(v) => writeln!(f, "  {}assert {v}{heap}", PcPrefix(&inst.pc))?,
                InstKind::Refute(v) => writeln!(f, "  {}refute {v}{heap}", PcPrefix(&inst.pc))?,
            }
        }
        Ok(())
    }
}

impl Display for PathConds {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.conds.is_empty() {
            return Ok(());
        }
        write!(f, "<")?;
        for (i, (val, pol)) in self.conds.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            if matches!(pol, Polarity::Negative) {
                write!(f, "!")?;
            }
            write!(f, "{val}")?;
        }
        write!(f, ">")
    }
}

/// Helper that renders a `PathConds` followed by a trailing space when
/// the guard is non-empty, and emits nothing at all when the guard is
/// the trivial `<>`. Use it at instruction-rendering sites so empty
/// guards don't waste a token.
pub(crate) struct PcPrefix<'a>(pub &'a PathConds);

impl Display for PcPrefix<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.0.conds.is_empty() {
            Ok(())
        } else {
            write!(f, "{} ", self.0)
        }
    }
}

/// Renders an obligation's check-in heap as a trailing ` [h3]` suffix (a leading
/// space so it detaches from the expression), or nothing when there is none.
pub(crate) struct HeapSuffix<'a>(pub &'a Option<HeapVal>);

impl Display for HeapSuffix<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Some(h) => write!(f, " [{h}]"),
            None => Ok(()),
        }
    }
}
