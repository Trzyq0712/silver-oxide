use crate::vmir::{MemberId, PureInst, Type, Value};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inst {
    pub kind: InstKind,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstKind {
    /// A fresh symbolic value of some type
    Fresh,
    /// A pure instruction that does not modify the heap
    Pure(PureInst),
    /// `inhale` or `exhale` a `heap_exp`
    HeapOp(HeapOp, MemberId, Vec<Value>),
    /// Assign to a heap location by transforming the input heap
    HeapAssign(HeapAssign),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HeapAssign {
    pub heap: Value,
    pub addr: Value,
    pub val: Value,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapOp {
    Inhale,
    Exhale,
}

#[derive(Debug, Clone)]
pub struct Method(pub Vec<Inst>);
