use crate::vmir::Val;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HeapVal {
    /// The empty heap.
    Empty,
    /// The heap delta of the resource's `requires` precondition. Only legal
    /// inside a `Resource` whose `requires.is_some()`.
    Pre,
    /// A heap-typed temporary produced by an earlier heap instruction.
    Temp(usize),
}

/// Heap instructions shared between resource and method bodies.
///
/// `X` is the context extension slot. Operations that are *not* legal inside a
/// resource body (currently only heap subtraction) live in `X` rather than as
/// a top-level variant. A resource body instantiates `X = !`, making `Ext`
/// unconstructible; a method body fills `X` with [`MethodHeapExt`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapInst<X> {
    /// Single-chunk heap holding `perm` permission to `loc`. The location is
    /// an `Addr<T>` value produced by a call to the resource's auto-emitted
    /// `@addr` uninterpreted function (works uniformly for fields and
    /// predicates).
    Acc(Acc),
    /// Heap union. May produce equalities between merged chunks under the
    /// instruction's path condition.
    Add(HeapVal, HeapVal),
    /// Conditional heap: `cond ? then : else`.
    Ternary(Val, HeapVal, HeapVal),
    /// Context-specific extensions (e.g. method-only heap subtraction).
    Ext(X),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Acc {
    /// Location to gain access to.
    pub loc: Val,
    /// Permission amount to the location.
    pub perm: Val,
}
