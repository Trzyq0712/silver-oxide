use crate::vmir::{MemberId, PureInst, Type, Value};
use std::fmt::{Display, Formatter};

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method(pub Vec<Inst>);

impl Display for HeapAssign {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "*[{}]{} := {}", self.heap, self.addr, self.val)
    }
}

impl Display for HeapOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            HeapOp::Inhale => write!(f, "inhale"),
            HeapOp::Exhale => write!(f, "exhale"),
        }
    }
}

impl Display for InstKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            InstKind::Fresh => write!(f, "fresh"),
            InstKind::Pure(inst) => write!(f, "{inst}"),
            InstKind::HeapOp(op, member, args) => {
                write!(f, "{} p{}(", op, member.0)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            InstKind::HeapAssign(assign) => write!(f, "{assign}"),
        }
    }
}

impl Display for Method {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (idx, Inst { kind, ty }) in self.0.iter().enumerate() {
            writeln!(f, "e{idx}: {ty} := {kind}")?;
        }
        Ok(())
    }
}
