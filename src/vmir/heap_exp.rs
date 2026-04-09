use crate::vmir::{ty::Type, MemberId};
use nonmax::NonMaxU32;

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

/// Each value is either a temporary, or a constant literal.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    /// Refers to an earlier instruction result
    Temp(Temp),
    Literal(Literal),
}

impl From<Literal> for Value {
    fn from(value: Literal) -> Self {
        Self::Literal(value)
    }
}

impl From<Temp> for Value {
    fn from(value: Temp) -> Self {
        Self::Temp(value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Local(pub NonMaxU32);

impl From<usize> for Local {
    fn from(value: usize) -> Self {
        Self(NonMaxU32::new(value as u32).expect("Too many temporaries"))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Temp(pub NonMaxU32);

impl From<usize> for Temp {
    fn from(value: usize) -> Self {
        Self(NonMaxU32::new(value as u32).expect("Too many temporaries"))
    }
}

/// A typed SSA instruction
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst {
    pub kind: InstKind,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PermOp {
    /// Adjust permission to a location: (location, amount_delta)
    /// Positive amount = add permission, Negative = remove permission
    Adjust(Value, Value),
}

type Heap = Value;
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstKind {
    /// Read the current value of a local
    Read(Local),

    Unary(UnOp, Value),
    Binary(BinOp, Value, Value),
    Ternary(Value, Value, Value),

    /// Call a function
    Call(MemberId, Vec<Value>),

    // Heap operations
    /// Get the amount of permission held to a location in the given heap
    Perm(Heap, Value),
    /// Adjust the amount of permission held to a location in the given heap
    PermOp(Heap, PermOp),
    /// Dereference an address in the given heap
    Deref(Heap, Value),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HeapExp {
    /// Types of inputs this heap expression expects
    /// For requires: [heap, ...method_args]
    /// For ensures: [heap, old_heap, ...method_args, ...returns]
    pub input_types: Vec<crate::vmir::Type>,
    pub insts: Vec<Inst>,
    /// The pure result - a boolean
    pub res_pure: Value,
    /// The impure part - a heap
    pub res_impure: Value,
}
