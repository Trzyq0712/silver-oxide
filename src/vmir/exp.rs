use crate::vmir::{ty::Type, MemberId};
use nonmax::NonMaxU32;

pub struct TypedExp {
    pub kind: InstKind,
    pub ty: Type,
}

struct Local(NonMaxU32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BinOp {
    Plus,
    Minus,
    Mult,
    Div,
    Mod,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnOp {
    Minus,
    Not,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Int(num::BigInt),
    Bool(bool),
    Null,
    Real(num::BigRational),
}

/// Each value is either a temporary, a local, or a constant literal.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    /// Refers to an earlier instruction result
    Temp(NonMaxU32),
    /// A local from the scope
    Local(NonMaxU32),
    Const(Literal),
}

/// A typed SSA instruction
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst {
    pub kind: InstKind,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstKind {
    Unary(UnOp, Value),
    Binary(BinOp, Value, Value),
    Ternary(Value, Value, Value),

    Call(MemberId, Vec<Value>),

    Deref(Value),
}

/// Represents an access expression `acc(loc, perm)`
/// In VMIR, the access expressions are flattened. This means
/// `v == null ? acc(loc, 1/1) : true` is transformed into
/// `acc(loc, v == null ? 1/1 : 0/1)` (in reality the condition is a separate instruction result
/// itself).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Acc {
    pub loc: Value,
    pub perm: Value,
}

/// Expression is a list of instructions
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Exp {
    pub insts: Vec<Inst>,
    pub res: Value,
    pub impures: Vec<Acc>,
}
