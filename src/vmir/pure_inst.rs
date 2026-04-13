use std::fmt::{Display, Formatter};

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

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Int(i) => write!(f, "{i}"),
            Literal::Bool(b) => write!(f, "{b}"),
            Literal::Null => write!(f, "null"),
            Literal::Real(r) => write!(f, "{r}"),
            Literal::EmptyHeap => write!(f, "∅"),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Temp(idx) => write!(f, "e{idx}"),
            Value::Literal(lit) => write!(f, "{lit}"),
        }
    }
}

impl Display for HeapDepInstKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            HeapDepInstKind::Perm(addr) => write!(f, "perm {addr}"),
            HeapDepInstKind::Deref(addr) => write!(f, "deref {addr}"),
        }
    }
}

impl Display for HeapDepInst {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            HeapDepInstKind::Perm(addr) => write!(f, "perm[{}] {addr}", self.heap),
            HeapDepInstKind::Deref(addr) => write!(f, "*[{}] {addr}", self.heap),
        }
    }
}

impl Display for PureInst {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            PureInst::Unary(op, val) => write!(f, "{op}{val}"),
            PureInst::Binary(op, lhs, rhs) => write!(f, "{lhs} {op} {rhs}"),
            PureInst::Ternary(cond, then_val, else_val) => {
                write!(f, "{cond} ? {then_val} : {else_val}")
            }
            PureInst::Call(func_id, args) => {
                write!(f, "f{}(", func_id.0)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            PureInst::Heap(inst) => write!(f, "{inst}"),
        }
    }
}
