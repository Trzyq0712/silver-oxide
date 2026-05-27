//! A pure instruction produces a value without modifying the heap. It can,
//! however, depend on the heap, e.g. via dereferences or function calls.
use crate::vmir::{HeapVal, MemberId};

/// A value can be either a literal or a temporary variable defined earlier.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Val {
    Literal(Literal),
    Temp(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinOp {
    Plus,
    Minus,
    Mult,
    Div,
    Mod,
    Eq,
    Lt,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Null,
    Bool(bool),
    Int(num::BigInt),
    Real(num::BigRational),
}

pub const NULL: Val = Val::Literal(Literal::Null);
pub const TRUE: Val = Val::Literal(Literal::Bool(true));
pub const FALSE: Val = Val::Literal(Literal::Bool(false));
pub fn none() -> Val {
    Val::Literal(Literal::Real(num::BigInt::from(0).into()))
}
pub fn write() -> Val {
    Val::Literal(Literal::Real(num::BigInt::from(1).into()))
}

/// `X` is the context's ctx-heap slot, threaded through `HeapVal<X>`
/// operands of `Deref`, `Perm`, and `FunctionCall.heap_ctx`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PureInst<X> {
    /// Create a fresh symbolic value.
    Fresh,
    /// A unary operation like negation or logical not.
    Unary(UnOp, Val),
    /// A binary operation like addition or equality.
    Binary(BinOp, Val, Val),
    /// A ternary operation, if-then-else.
    Ternary(Val, Val, Val),
    /// Dereference an address in a heap. Surface notation: `*[heap] addr`.
    /// Combined with a `FunctionCall` returning `Addr<T>` it realises
    /// `resource@snap`.
    Deref(HeapVal<X>, Val),
    /// Query the permission amount of an address in a heap.
    Perm(HeapVal<X>, Val),
    /// Call a pure function. Field/predicate `addr` functions are ordinary
    /// uninterpreted functions and use this variant.
    FunctionCall(FunctionCall<X>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionCall<X> {
    pub func_id: MemberId,
    /// Heap context used to evaluate the call. `None` when the function has
    /// no heap precondition (e.g. the auto-emitted `@addr` functions).
    pub heap_ctx: Option<HeapVal<X>>,
    pub args: Vec<Val>,
}
