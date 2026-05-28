use crate::vmir::{HeapInst, PureInst, Type, Val};

use std::clone::Clone;
use std::cmp::{Eq, PartialEq};
use std::fmt::Debug;
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
/// Used for verifying an instruction is safe to execute, or for extending the
/// state with additional facts after executing an instruction.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct PathConds {
    pub lits: Vec<(Val, Polarity)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Polarity {
    /// The value must hold.
    Positive,
    /// The value must not hold.
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
