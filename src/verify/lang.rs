use egg::*;
use std::fmt::{Display, Formatter};

use crate::vmir::BinOp;
use crate::vmir::Literal;
use crate::vmir::MemberId;
use crate::vmir::Type; // Ensure Type is in scope

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Symbolic {
    Fresh(u32, Type),
    Lit(Literal),
    Binary(BinOp, Type, [Id; 2]),
    Ite(Type, [Id; 3]),
    FuncApp(MemberId, Type, Box<[Id]>),
}

// egg buckets e-classes by `Discriminant` (the `classes_by_op` index) before
// ever calling `matches`, so `discriminant` must be no finer than `matches`:
// two nodes that `matches` accepts must share a discriminant, or the pattern
// search will skip their bucket. `matches` ignores the result `Type` on
// `Binary`/`Ite`, so the discriminant drops it there too.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Discriminant {
    Fresh(u32, Type),
    Lit(Literal),
    Binary(BinOp),
    Ite,
    FuncApp(MemberId, Type),
}

impl Language for Symbolic {
    type Discriminant = Discriminant;

    fn discriminant(&self) -> Self::Discriminant {
        use Discriminant as D;
        use Symbolic as S;
        match self {
            S::Fresh(s, ty) => D::Fresh(*s, ty.clone()),
            S::Lit(l) => D::Lit(l.clone()),
            S::Binary(op, _, _) => D::Binary(*op),
            S::Ite(_, _) => D::Ite,
            S::FuncApp(id, ty, _) => D::FuncApp(id.clone(), ty.clone()),
        }
    }

    fn matches(&self, other: &Self) -> bool {
        use Symbolic::*;
        // `matches` is used only during pattern search (operator-shape
        // comparison), never for hashconsing. The result `Type` on
        // `Binary`/`Ite` is intentionally ignored so a single structural
        // pattern matches every result type (`Ite`'s type is open-ended).
        match (self, other) {
            (Fresh(s1, ty1), Fresh(s2, ty2)) => s1 == s2 && ty1 == ty2,
            (Lit(l1), Lit(l2)) => l1 == l2,
            (Binary(op1, _, _), Binary(op2, _, _)) => op1 == op2,
            (Ite(_, _), Ite(_, _)) => true,
            (FuncApp(id1, ty1, args1), FuncApp(id2, ty2, args2)) => {
                id1 == id2 && ty1 == ty2 && args1.len() == args2.len()
            }
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        use Symbolic::*;
        match self {
            Fresh(..) | Lit(..) => &[],
            Binary(_, _, ids) => ids,
            Ite(_, ids) => ids,
            FuncApp(_, _, ids) => ids,
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        use Symbolic::*;
        match self {
            Fresh(..) | Lit(..) => &mut [],
            Binary(_, _, ids) => ids,
            Ite(_, ids) => ids,
            FuncApp(_, _, ids) => ids,
        }
    }
}

impl Display for Symbolic {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Symbolic::Fresh(id, ty) => write!(f, "{id}#{ty}"),
            Symbolic::Lit(l) => write!(f, "{l}"),
            Symbolic::Binary(op, _, _) => write!(f, "{op}"),
            Symbolic::Ite(_, _) => write!(f, "ITE"),
            Symbolic::FuncApp(id, _, _) => write!(f, "{}(..)", id.0),
        }
    }
}
