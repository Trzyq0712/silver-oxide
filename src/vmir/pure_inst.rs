use crate::vmir::{BinOp, MemberId, UnOp, Value};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PureInst {
    Unary(UnOp, Value),
    Binary(BinOp, Value, Value),
    Ternary(Value, Value, Value),
    Call(MemberId, Vec<Value>),
    Perm(Value, Value),
}
