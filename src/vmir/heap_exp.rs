use crate::vmir::{ty::Type, MemberId};

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

/// A typed SSA instruction
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst {
    pub kind: InstKind,
    pub ty: Type,
}

type Heap = Value;
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstKind {
    Unary(UnOp, Value),
    Binary(BinOp, Value, Value),
    Ternary(Value, Value, Value),

    /// Call a function
    Call(MemberId, Vec<Value>),

    // Heap operations
    /// Get the amount of permission held to a location in the given heap
    Perm(Heap, Value),
    /// Adjust the amount of permission held to a location in the given heap
    Acc(Heap, Value, Value),
    /// Dereference an address in the given heap
    Deref(Heap, Value),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HeapExp {
    /// Types of inputs this heap expression expects
    /// For requires: [heap, ...method_args]
    /// For ensures: [heap, old_heap, ...method_args, ...returns]
    pub input_types: Vec<Type>,
    pub insts: Vec<Inst>,
    /// The pure result - a boolean
    pub res_pure: Value,
    /// The impure part - a heap
    pub res_impure: Value,
}
