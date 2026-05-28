use crate::vmir::{MemberId, Type, Val};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    pub params: Vec<Type>,
    pub ret: Type,
    pub body: Option<()>,
}

/// A pure-function invocation. The heap in which the call is evaluated is
/// carried by the surrounding `PureInst` / `ResourcePureExt` variant —
/// this struct stores only the function-identity and value arguments, so
/// the same shape works for both the ambient-heap call (`PureInst::FunctionCall`)
/// and the ctx-heap call (`ResourcePureExt::CtxFunctionCall`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionCall {
    pub function: MemberId,
    pub args: Vec<Val>,
}
