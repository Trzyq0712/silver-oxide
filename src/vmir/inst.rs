use crate::vmir::{HeapInst, PureInst, Type, Val};

/// A type-level tag that selects which extensions are legal in a body of
/// instructions. Mirrors the `Ext` pattern used in `src/silver/final_ast` —
/// each slot is filled by the context with an enum it owns.
///
/// `ResourceCtx` fills every slot with `!` (uninhabited), which makes any
/// extension variant unconstructible at compile time. `MethodCtx` (in
/// `crate::vmir::method`) fills the slots with `MethodHeapExt` and
/// `MethodInstExt`.
pub trait Context {
    /// Heap-instruction extensions legal in this context.
    type HeapExt;
    /// Top-level instruction-kind extensions legal in this context.
    type InstExt;
}

/// An instruction gated by a path condition. Generic over the two extension
/// types `H` (heap extension) and `K` (kind extension). Use the type aliases
/// `ResourceInst` / `MethodInst` rather than `Inst<H, K>` directly.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst<H, K> {
    pub pc: PathCond,
    pub kind: InstKind<H, K>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstKind<H, K> {
    /// Produces a `Val::Temp` of the given `Type`.
    Pure(Type, PureInst),
    /// Produces a `HeapVal::Temp`.
    Heap(HeapInst<H>),
    /// Context-specific top-level extensions (e.g. method-only `Assume`,
    /// `Assert`, and resource calls).
    Ext(K),
}

/// Conjunction of literals over previously-emitted `Val`s. Rendered
/// `<e1, !e3, e5>`. Empty is the trivial guard `<>`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct PathCond {
    pub lits: Vec<Lit>,
}

/// A literal in a path condition: a `Val` plus its polarity.
/// `polarity = true` means the value must hold; `false` means it must not.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Lit {
    pub val: Val,
    pub polarity: bool,
}
