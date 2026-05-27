use crate::vmir::Val;

/// Heap-typed value. Generic over `X`, the context's "ctx-heap" slot.
///
/// - `ResourceCtx` fills `X = ()` — `CtxHeap(())` is constructible and
///   represents the resource's precondition heap delta (when the resource
///   has a `requires`).
/// - `MethodCtx` fills `X = !` — `CtxHeap` is uninhabited; method bodies
///   have no context-heap concept.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HeapVal<X> {
    /// The empty heap.
    Empty,
    /// A heap-typed temporary produced by an earlier heap instruction.
    Temp(usize),
    /// Context heap. Resource-only.
    CtxHeap(X),
}

/// Heap instructions. `S` is the context's heap-instruction extension slot;
/// `X` is the ctx-heap slot threaded through `HeapVal<X>` operands.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapInst<S, X> {
    /// Single-chunk heap holding `perm` permission to `loc`. The location is
    /// an `Addr<T>` value produced by a call to the resource's auto-emitted
    /// `@addr` uninterpreted function (works uniformly for fields and
    /// predicates).
    Acc(Acc),
    /// Heap union. May produce equalities between merged chunks under the
    /// instruction's path condition.
    Add(HeapVal<X>, HeapVal<X>),
    /// Conditional heap: `cond ? then : else`.
    Ternary(Val, HeapVal<X>, HeapVal<X>),
    /// Context-specific extensions (e.g. method-only heap subtraction).
    Ext(S),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Acc {
    /// Location to gain access to.
    pub loc: Val,
    /// Permission amount to the location.
    pub perm: Val,
}
