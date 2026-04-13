use std::fmt::Display;

use crate::vmir::MemberId;

/// Instructions that do not modify the heap (still can depend on it)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PureInst {
    Unary(UnOp, Value),
    Binary(BinOp, Value, Value),
    Ternary(Value, Value, Value),
    Call(MemberId, Vec<Value>),
    Heap(HeapDepInst),
}

/// Heap dependent pure instructions
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HeapDepInst {
    pub heap: Value,
    pub kind: HeapDepInstKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapDepInstKind {
    /// Query the amount of permission we have for the address
    Perm(Value),
    /// Dereference the address, to get the value stored
    Deref(Value),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BinOp {
    Plus,
    Minus,
    Mult,
    Div,
    Mod,
    Eq,
    Lt,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Int(num::BigInt),
    Bool(bool),
    Null,
    Real(num::BigRational),
    EmptyHeap,
}

pub type Temp = usize;

/// Each value is either a temporary, or a constant literal.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Temp(Temp),
    Literal(Literal),
}

impl From<Literal> for Value {
    fn from(value: Literal) -> Self {
        Self::Literal(value)
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Not => write!(f, "!"),
            UnOp::Neg => write!(f, "-"),
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Plus => write!(f, "+"),
            BinOp::Minus => write!(f, "-"),
            BinOp::Mult => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Mod => write!(f, "%"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Lt => write!(f, "<"),
        }
    }
}
