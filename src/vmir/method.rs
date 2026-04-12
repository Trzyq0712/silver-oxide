use crate::vmir::{BinOp, MemberId, Type, UnOp, Value};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst {
    pub kind: InstKind,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstKind {
    /// A fresh symbolic value of some type
    Fresh,
    UnOp(UnOp, Value),
    BinOp(BinOp, Value, Value),

    /// `inhale` or `exhale` a `heap_exp`
    HeapOp(HeapOp, MemberId, Vec<Value>),

    /// Assign to a heap location by transforming the input heap
    HeapAssign(/*heap*/ Value, /*&T*/ Value, /*T*/ Value),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapOp {
    Inhale,
    Exhale,
}

#[derive(Debug, Clone)]
pub struct Method(pub Vec<Inst>);
