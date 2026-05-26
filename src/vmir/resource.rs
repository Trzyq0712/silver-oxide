use crate::vmir::{Context, HeapVal, Inst, MemberId, Type, Val};

/// Resource bodies admit no statement-shaped extensions: no heap
/// subtraction, no `Assume`/`Assert`, nothing that would be a Viper
/// statement.
pub struct ResourceCtx;

impl Context for ResourceCtx {
    type HeapExt = !;
    type InstExt = !;
}

/// A reusable unit of proof.
///
/// A resource computes a heap delta and a boolean condition. It is consumed at
/// call sites either by *inhale* (add the delta to the ambient heap and assume
/// the boolean) or by *exhale* (subtract the delta and assert the boolean).
/// Inhale and exhale themselves are performed in the method body; they are
/// not instructions inside a resource body.
///
/// `body` is `None` for **abstract** resources (e.g. an abstract predicate
/// declaration). Abstract resources may not be the target of a `ResourceCall`.
///
/// A resource may have a precondition: another resource whose boolean is
/// assumed inside this body and whose heap delta is addressable as
/// [`HeapVal::Pre`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Resource {
    pub params: Vec<Type>,
    pub requires: Option<(MemberId, Vec<Val>)>,
    pub body: Option<ResourceBody>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceBody {
    pub insts: Vec<ResourceInst>,
    pub res: (HeapVal, Val),
}

/// Concrete `Inst` for resource bodies. Extension slots are uninhabited.
pub type ResourceInst = Inst<!, !>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceCall {
    pub resource: MemberId,
    pub args: Vec<Val>,
}
