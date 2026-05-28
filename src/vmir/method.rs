use crate::vmir::{Context, HeapVal, Inst, ResourceCall, Val};

/// Method bodies allow everything resource bodies allow except the
/// `CtxHeap` constructor, plus a fixed set of statement-shaped extensions:
/// `Assume` / `Assert` and `ResourceCall` (via [`MethodInstExt`]).
pub struct MethodCtx;

impl Context for MethodCtx {
    type InstExt = MethodInstExt;
    type HeapValExt = !;
}

/// Concrete `HeapVal` for method bodies. The `CtxHeap` variant is
/// unconstructible (`!`-payload).
pub type MethodHeapVal = HeapVal<!>;

/// Top-level instruction extensions that are only legal in method bodies.
///
/// `Assume` / `Assert` produce no temporary. `ResourceCall` produces a pair
/// `(HeapVal::Temp, Val::Temp)` — the called resource's `(delta, bool)` —
/// and bumps both temp counters. The target resource must have
/// `body.is_some()`; calling an abstract resource is illegal.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MethodInstExt {
    Assume(Val),
    Assert(Val),
    ResourceCall(ResourceCall),
}

/// Concrete `Inst` for method bodies.
pub type MethodInst = Inst<MethodInstExt, !>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub insts: Vec<MethodInst>,
}
