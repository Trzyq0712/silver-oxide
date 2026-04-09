use crate::vmir::{BinOp, MemberId, Type, UnOp, Value};

pub enum InstKind {
    Fresh(Type),
    UnOp(UnOp, Value),
    BinOp(BinOp, Value),

    HeapOp(HeapOp, MemberId, Vec<Value>),

    HeapAssign(Value, Value),
}

pub enum HeapOp {
    Inhale,
    Exhale,
}
