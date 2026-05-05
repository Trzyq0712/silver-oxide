///! A pure instruction produces a value without modifying the heap. It can, however,
///! depend on the heap, e.g. via dereferences or function calls.
use crate::vmir::{HeapVal, MemberId, Type};

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PureInst {
    /// Create a fresh symbolic value.
    Fresh,
    /// A unary operation like negation or logical not.
    Unary(UnOp, Val),
    /// A binary operation like addition or equality.
    Binary(BinOp, Val, Val),
    /// A ternary operation, if-then-else.
    Ternary(Val, Val, Val),
    /// Dereference an address in a heap.
    Deref(HeapVal, Val),
    /// Query the permission amount of an address in a heap.
    Perm(HeapVal, Val),
    /// Call a pure function.
    FunctionCall(FunctionCall),
    /// Determine whether the first heap is a permission-subset of the second.
    /// Used to decide whether a heap can be exhaled.
    HeapSubset(HeapVal, HeapVal),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionCall {
    pub func_id: MemberId,
    pub heap_ctx: HeapVal,
    pub args: Vec<Val>,
}
