use crate::vmir::{ty::Type, PureInst, Value};
use std::fmt::{Display, Formatter};

/// A typed SSA instruction
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HeapInst {
    pub kind: HeapInstKind,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapInstKind {
    Pure(PureInst),
    Acc(AccInst),
}

/// Modify the heap by changing the amount of permission we have for an address
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AccInst {
    pub heap: Value,
    pub addr: Value,
    pub perm: Value,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HeapExp {
    /// Types of inputs this heap expression expects
    /// For requires: [heap, ...method_args]
    /// For ensures: [heap, old_heap, ...method_args, ...returns]
    pub input_types: Vec<Type>,
    pub insts: Vec<HeapInst>,
    /// The pure result - a boolean
    pub res_pure: Value,
    /// The impure part - a heap
    pub res_impure: Value,
}

impl Display for AccInst {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ** acc({}, {})", self.heap, self.addr, self.perm)
    }
}

impl Display for HeapInstKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            HeapInstKind::Pure(inst) => write!(f, "{inst}"),
            HeapInstKind::Acc(inst) => write!(f, "{inst}"),
        }
    }
}

impl Display for HeapExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (i, ty) in self.input_types.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{i}: {ty}")?;
        }
        writeln!(f, "]")?;

        for (idx, HeapInst { kind, ty }) in self.insts.iter().enumerate() {
            writeln!(f, "e{}: {} := {}", idx + self.input_types.len(), ty, kind)?;
        }

        writeln!(f, "({}, {})", self.res_impure, self.res_pure)
    }
}
