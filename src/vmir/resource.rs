use crate::vmir::{HeapVal, Inst, InstContext, MemberId, Type, Val};

pub struct ResourceCtx;

impl InstContext for ResourceCtx {
    type PureExt = ResourcePureExt;
}

/// Pure-instruction extensions only legal in resource bodies.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ResourcePureExt {
    /// Dereference an address in the resource's context (precondition) heap.
    /// SIDECOND: the context heap must have positive permission amount
    /// fot this location.
    CtxDeref(Val),
}

pub type ResourceInst = Inst<ResourceCtx>;

/// A reusable unit of proof.
///
/// A resource computes a heap delta and a boolean condition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Resource {
    pub params: Vec<Type>,
    pub requires: Option<(MemberId, Vec<Val>)>,
    pub body: Option<ResourceBody>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceBody {
    pub insts: Vec<ResourceInst>,
    pub res: (crate::vmir::HeapVal, Val),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceCall {
    pub resource: MemberId,
    pub ctx_heap: HeapVal,
    pub args: Vec<Val>,
}
