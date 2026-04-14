use egg::*;
use num::{BigInt, BigRational};

use crate::vmir::MemberId;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum BinOp {
    Plus,
    Minus,
    Mult,
    Div,
    Eq,
    Lt,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum UnOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum Symbolic {
    Fresh(egg::Symbol),
    Int(BigInt),
    Real(BigRational),
    Bool(bool),
    Unary(UnOp, Id),
    Binary(BinOp, [Id; 2]),
    Ternary([Id; 3]),
    FuncApp(MemberId, Box<[Id]>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Discriminant {
    Fresh(egg::Symbol),
    Int(BigInt),
    Real(BigRational),
    Bool(bool),
    Unary(UnOp),
    Binary(BinOp),
    Ternary,
    FuncApp(MemberId),
}

impl Language for Symbolic {
    type Discriminant = Discriminant;

    fn discriminant(&self) -> Self::Discriminant {
        use Discriminant as D;
        use Symbolic as S;
        match self {
            S::Fresh(s) => D::Fresh(*s),
            S::Int(i) => D::Int(i.clone()),
            S::Real(r) => D::Real(r.clone()),
            S::Bool(b) => D::Bool(*b),
            S::Unary(op, _) => D::Unary(*op),
            S::Binary(op, _) => D::Binary(*op),
            S::Ternary(_) => D::Ternary,
            S::FuncApp(id, _) => D::FuncApp(*id),
        }
    }

    fn matches(&self, other: &Self) -> bool {
        use Symbolic::*;
        match (self, other) {
            (Fresh(s1), Fresh(s2)) => s1 == s2,
            (Int(i1), Int(i2)) => i1 == i2,
            (Real(r1), Real(r2)) => r1 == r2,
            (Bool(b1), Bool(b2)) => b1 == b2,
            (Unary(op1, _), Unary(op2, _)) => op1 == op2,
            (Binary(op1, _), Binary(op2, _)) => op1 == op2,
            (Ternary(_), Ternary(_)) => true,
            (FuncApp(id1, args1), FuncApp(id2, args2)) => id1 == id2 && args1.len() == args2.len(),
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        use Symbolic::*;
        match self {
            Fresh(_) | Int(_) | Real(_) | Bool(_) => &[],
            Unary(_, id) => std::slice::from_ref(id),
            Binary(_, ids) => ids,
            Ternary(ids) => ids,
            FuncApp(_, ids) => ids,
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        use Symbolic::*;
        match self {
            Fresh(_) | Int(_) | Real(_) | Bool(_) => &mut [],
            Unary(_, id) => std::slice::from_mut(id),
            Binary(_, ids) => ids,
            Ternary(ids) => ids,
            FuncApp(_, ids) => ids,
        }
    }
}
