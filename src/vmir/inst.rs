use crate::vmir::display::VmirDisplay;
use crate::vmir::{HeapInst, HeapVal, PureInst, Type, Val};

use std::clone::Clone;
use std::cmp::{Eq, PartialEq};
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;

use derive_where::derive_where;

/// Whether the variant has a SIDECOND that the path condition guards.
/// Used by [`Inst::new`] to refuse non-trivial `PathConds` on
/// instructions that don't make use of it.
pub trait UsesPc {
    fn uses_pc(&self) -> bool;
}

impl UsesPc for ! {
    fn uses_pc(&self) -> bool {
        match *self {}
    }
}

pub trait Ext = Debug + Clone + PartialEq + Eq + Hash + UsesPc;

/// A context for instructions, through which additional instruction extensions can be added.
pub trait InstContext {
    /// Top-level instruction-kind extensions legal in this context.
    type InstExt: Ext = !;
    /// Pure-instruction extensions legal in this context.
    type PureExt: Ext = !;
    /// Heap-instruction extensions legal in this context.
    type HeapExt: Ext = !;

    /// Build this context's `perm(loc)` pure extension reading `heap`, when the
    /// context permits one. Default `None` (no perm extension is constructible,
    /// e.g. resource bodies whose `PureExt` is the never type).
    fn perm_pure_ext(_heap: HeapVal, _loc: Val) -> Option<Self::PureExt> {
        None
    }
}

/// An instruction gated by a path condition.
#[derive_where(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst<InstCtx: InstContext> {
    pub pc: PathConds,
    pub kind: InstKind<InstCtx>,
}

#[derive_where(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstKind<InstCtx: InstContext> {
    /// Produces a temporary of a given type.
    Pure(Type, PureInst<InstCtx::PureExt>),
    /// Produces a heap value.
    Heap(HeapInst<InstCtx::HeapExt>),
    /// Context-specific top-level extensions.
    Ext(InstCtx::InstExt),
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

// ======================
// DISPLAY INFRASTRUCTURE
// ======================

/// Counter contribution of an `InstKind::Ext` variant. Returns
/// `(val_bump, heap_bump)`.
pub trait Bumps {
    fn bumps(&self) -> (usize, usize);
}

impl Bumps for ! {
    fn bumps(&self) -> (usize, usize) {
        match *self {}
    }
}

impl<C: InstContext> InstKind<C> {
    pub fn uses_pc(&self) -> bool {
        match self {
            InstKind::Pure(_, pi) => pi.uses_pc(),
            InstKind::Heap(hi) => hi.uses_pc(),
            InstKind::Ext(ext) => ext.uses_pc(),
        }
    }
}

impl<C: InstContext> Inst<C> {
    /// Construct an instruction. The path condition must be empty
    /// unless `kind` has a SIDECOND (see `UsesPc`).
    pub fn new(pc: PathConds, kind: InstKind<C>) -> Self {
        debug_assert!(
            pc.conds.is_empty() || kind.uses_pc(),
            "non-empty PathConds on a non-SIDECOND instruction"
        );
        Self { pc, kind }
    }
}

/// Refutable Display impl for an `InstExt = !`
impl<'a> Display for VmirDisplay<'a, (usize, usize, &'a PathConds, &'a !)> {
    fn fmt(&self, _: &mut Formatter<'_>) -> fmt::Result {
        let (_, _, _, never) = self.item;
        match *never {}
    }
}

/// Walk an instruction stream. Wraps `(val_base, heap_base, &[Inst<C>])`
/// in a `VmirDisplay` so the iteration lives behind a regular `Display`
/// impl. Callers — `Display for VmirDisplay<&Method>`, `&Resource>`,
/// `&ResourceBody>` — invoke via `self.with((val_base, heap_base,
/// &insts[..]))`.
impl<'a, C: InstContext> Display for VmirDisplay<'a, (usize, usize, &'a [Inst<C>])>
where
    C::InstExt: Bumps,
    C::PureExt: crate::vmir::pure::PureExtRender,
    C::HeapExt: crate::vmir::heap::HeapExtRender,
    VmirDisplay<'a, (usize, usize, &'a PathConds, &'a C::InstExt)>: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (val_base, heap_base, insts) = self.item;
        let mut e_idx = val_base;
        let mut h_idx = heap_base;
        for inst in insts {
            match &inst.kind {
                InstKind::Pure(ty, pi) => {
                    writeln!(
                        f,
                        "  e{e_idx}: {} := {}{}",
                        self.with(ty),
                        PcPrefix(&inst.pc),
                        self.with(pi)
                    )?;
                    e_idx += 1;
                }
                InstKind::Heap(hi) => {
                    writeln!(f, "  h{h_idx} := {}{}", PcPrefix(&inst.pc), hi)?;
                    h_idx += 1;
                }
                InstKind::Ext(ext) => {
                    write!(f, "{}", self.with((e_idx, h_idx, &inst.pc, ext)))?;
                    let (de, dh) = ext.bumps();
                    e_idx += de;
                    h_idx += dh;
                }
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
