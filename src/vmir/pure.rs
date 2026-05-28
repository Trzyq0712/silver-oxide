use crate::vmir::{FunctionCall, HeapVal};

/// A value can be either a literal or a temporary variable defined earlier.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Val {
    Literal(Literal),
    Temp(usize),
}

/// A binary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinOp {
    Plus,
    Minus,
    Mult,
    /// SIDECOND: The second operand must be non-zero.
    Div,
    /// SIDECOND: The second operand must be non-zero.
    Mod,
    Eq,
    Lt,
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

/// A pure instruction. Pure instructions do not affect the heap and produce new
/// pure values. Pure instructions can, however, depend on the heap state itself.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PureInst<P> {
    /// Create a fresh symbolic value.
    Fresh,
    /// A binary operation like addition or equality.
    Binary(BinOp, Val, Val),
    /// A ternary operation, if-then-else.
    Ternary(Val, Val, Val),
    /// Dereference an address in a heap.
    /// SIDECOND: The heap must hold non-zero permission to the location
    /// under the given path condition.
    Deref(HeapVal, Val),
    /// Query the permission amount of an address in a heap.
    Perm(HeapVal, Val),
    /// Call a pure function in the given heap.
    /// SIDECOND: The function's precondition must be satisfied.
    FunctionCall(HeapVal, FunctionCall),
    /// Context-specific pure-instruction extensions.
    Ext(P),
}
