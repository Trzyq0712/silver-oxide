use crate::vmir::{HeapInst, PureInst, Type, Val};

/// A type-level tag that selects which extensions are legal in a body of
/// instructions. Mirrors the `Ext` pattern used in `src/silver/final_ast` —
/// each slot is filled by the context with an enum it owns.
///
/// `ResourceCtx` (`crate::vmir::resource`) fills `HeapExt`/`InstExt` with `!`
/// (uninhabited), and fills `HeapValExt` with `()` so `HeapVal::CtxHeap(())`
/// is constructible inside a resource body.
///
/// `MethodCtx` (`crate::vmir::method`) fills `HeapExt`=`MethodHeapExt`,
/// `InstExt`=`MethodInstExt`, and `HeapValExt`=`!` (no context-heap
/// concept inside method bodies).
pub trait Context {
    /// Heap-instruction extensions legal in this context.
    type HeapExt;
    /// Top-level instruction-kind extensions legal in this context.
    type InstExt;
    /// Payload of `HeapVal::CtxHeap`. `()` (constructible) for contexts
    /// that have a context heap, `!` (uninhabited) for those that don't.
    type HeapValExt;
}

/// An instruction gated by a path condition. Generic over the three
/// extension slots `H` (heap inst ext), `K` (kind ext), `X` (ctx-heap).
/// Downstream code uses the concrete type aliases `ResourceInst` /
/// `MethodInst` rather than `Inst<H, K, X>` directly.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst<H, K, X> {
    pub pc: PathCond,
    pub kind: InstKind<H, K, X>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstKind<H, K, X> {
    /// Produces a `Val::Temp` of the given `Type`.
    Pure(Type, PureInst<X>),
    /// Produces a `HeapVal::Temp`.
    Heap(HeapInst<H, X>),
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
