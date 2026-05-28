use crate::vmir::display::VmirDisplay;
use crate::vmir::{HeapInst, PureInst, Type, Val};

use std::clone::Clone;
use std::cmp::{Eq, PartialEq};
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;

use derive_where::derive_where;

pub trait Ext = Debug + Clone + PartialEq + Eq + Hash;

/// A context for instructions, through which additional instruction extensions can be added.
pub trait InstContext {
    /// Top-level instruction-kind extensions legal in this context.
    type InstExt: Ext = !;
    /// Pure-instruction extensions legal in this context.
    type PureExt: Ext = !;
    /// Heap-instruction extensions legal in this context.
    type HeapExt: Ext = !;
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
    pub lits: Vec<(Val, Polarity)>,
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

/// Refutable Display impl for an `InstExt = !`
impl<'a> Display for VmirDisplay<'a, (usize, usize, &'a PathConds, &'a !)> {
    fn fmt(&self, _: &mut Formatter<'_>) -> fmt::Result {
        let (_, _, _, never) = self.item;
        match *never {}
    }
}

/// Walk an instruction stream.
pub(crate) fn write_inst_block<'a, T, C: InstContext>(
    f: &mut Formatter<'_>,
    ctx: &VmirDisplay<'a, T>,
    insts: &'a [Inst<C>],
    val_base: usize,
    heap_base: usize,
) -> fmt::Result
where
    C::InstExt: Bumps,
    VmirDisplay<'a, &'a PureInst<C::PureExt>>: Display,
    HeapInst<C::HeapExt>: Display,
    VmirDisplay<'a, (usize, usize, &'a PathConds, &'a C::InstExt)>: Display,
{
    let mut e_idx = val_base;
    let mut h_idx = heap_base;
    for inst in insts {
        match &inst.kind {
            InstKind::Pure(ty, pi) => {
                writeln!(
                    f,
                    "  e{e_idx}: {} := {} {}",
                    ctx.with(ty),
                    inst.pc,
                    ctx.with(pi)
                )?;
                e_idx += 1;
            }
            InstKind::Heap(hi) => {
                writeln!(f, "  h{h_idx} := {} {}", inst.pc, hi)?;
                h_idx += 1;
            }
            InstKind::Ext(ext) => {
                write!(f, "{}", ctx.with((e_idx, h_idx, &inst.pc, ext)))?;
                let (de, dh) = ext.bumps();
                e_idx += de;
                h_idx += dh;
            }
        }
    }
    Ok(())
}

impl Display for PathConds {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "<")?;
        for (i, (val, pol)) in self.lits.iter().enumerate() {
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
