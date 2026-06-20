use egg::*;
use std::fmt::{Display, Formatter};

use crate::vmir::BinOp;
use crate::vmir::Literal;

/// A verifier-allocated function-application id in the e-graph. **Disconnected
/// from VMIR `MemberId`**: the verifier assigns these (see `verify::mono`) — a
/// plain function reuses its declaration's index, ADT constructor/projection/tag
/// ops get freshly-minted indices per monomorphic instance.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct FuncId(pub usize);

/// A verifier-allocated heap-location (address) id in the e-graph. Like
/// [`FuncId`] but a distinct sort so function rewrites never touch addresses.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocId(pub usize);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Symbolic {
    Fresh(u32),
    Lit(Literal),
    Binary(BinOp, [Id; 2]),
    Ite([Id; 3]),
    FuncApp(FuncId, Box<[Id]>),
    /// A heap-location application `f(args)` (an address). A distinct sort from
    /// `FuncApp` so function rewrites never touch it; congruence still gives
    /// `f(x) == f(y) ⟺ x == y`.
    Location(LocId, Box<[Id]>),
    RealCast(Id),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Discriminant {
    Fresh(u32),
    Lit(Literal),
    Binary(BinOp),
    Ite,
    FuncApp(FuncId),
    Location(LocId),
    RealCast,
}

impl Language for Symbolic {
    type Discriminant = Discriminant;

    fn discriminant(&self) -> Self::Discriminant {
        use Discriminant as D;
        use Symbolic as S;
        match self {
            S::Fresh(s) => D::Fresh(*s),
            S::Lit(l) => D::Lit(l.clone()),
            S::Binary(op, _) => D::Binary(*op),
            S::Ite(_) => D::Ite,
            S::FuncApp(id, _) => D::FuncApp(*id),
            S::Location(id, _) => D::Location(*id),
            S::RealCast(_) => D::RealCast,
        }
    }

    fn matches(&self, other: &Self) -> bool {
        use Symbolic::*;
        match (self, other) {
            (Fresh(s1), Fresh(s2)) => s1 == s2,
            (Lit(l1), Lit(l2)) => l1 == l2,
            (Binary(op1, _), Binary(op2, _)) => op1 == op2,
            (Ite(_), Ite(_)) => true,
            (RealCast(_), RealCast(_)) => true,
            (FuncApp(id1, args1), FuncApp(id2, args2)) => id1 == id2 && args1.len() == args2.len(),
            (Location(id1, args1), Location(id2, args2)) => {
                id1 == id2 && args1.len() == args2.len()
            }
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        use Symbolic::*;
        match self {
            Fresh(..) | Lit(..) => &[],
            Binary(_, ids) => ids,
            Ite(ids) => ids,
            RealCast(id) => std::slice::from_ref(id),
            FuncApp(_, ids) | Location(_, ids) => ids,
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        use Symbolic::*;
        match self {
            Fresh(..) | Lit(..) => &mut [],
            Binary(_, ids) => ids,
            Ite(ids) => ids,
            RealCast(id) => std::slice::from_mut(id),
            FuncApp(_, ids) | Location(_, ids) => ids,
        }
    }
}

impl Display for Symbolic {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Symbolic::Fresh(id) => write!(f, "fresh{id}"),
            Symbolic::Lit(l) => write!(f, "{l}"),
            Symbolic::Binary(op, _) => write!(f, "{op}"),
            Symbolic::Ite(_) => write!(f, "ITE"),
            Symbolic::RealCast(_) => write!(f, "real"),
            // Id-only label; the viz resolves member ids to source names when it
            // renders the dot (it holds the interner).
            Symbolic::FuncApp(id, _) => write!(f, "fn{}(..)", id.0),
            Symbolic::Location(id, _) => write!(f, "loc{}(..)", id.0),
        }
    }
}

/// Error from [`Symbolic::from_op`] when a rewrite-pattern token is unknown.
#[derive(Debug)]
pub struct FromOpError(String);

impl Display for FromOpError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for FromOpError {}

impl FromOp for Symbolic {
    type Error = FromOpError;

    /// Parse a node from an s-expression operator + already-parsed children.
    /// Enables egg's string `rewrite!` macro (no type tags to encode now).
    /// Pattern variables (`?x`) are handled by egg before this is called.
    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
        use Symbolic::*;
        let bin = |o: BinOp| {
            if children.len() == 2 {
                Ok(Binary(o, [children[0], children[1]]))
            } else {
                Err(FromOpError(format!("`{op}` expects 2 children")))
            }
        };
        match (op, children.len()) {
            ("true", 0) => Ok(Lit(Literal::Bool(true))),
            ("false", 0) => Ok(Lit(Literal::Bool(false))),
            ("null", 0) => Ok(Lit(Literal::Null)),
            ("ite", 3) => Ok(Ite([children[0], children[1], children[2]])),
            ("real", 1) => Ok(RealCast(children[0])),
            ("+", _) => bin(BinOp::Plus),
            ("-", _) => bin(BinOp::Minus),
            ("*", _) => bin(BinOp::Mult),
            ("/", _) => bin(BinOp::Div),
            ("mod", _) => bin(BinOp::Mod),
            ("==", _) => bin(BinOp::Eq),
            ("<", _) => bin(BinOp::Lt),
            // A bare integer is `Lit(Int)`; a fraction (`0/1`, `1/2`) is `Lit(Real)`.
            (lit, 0) => {
                if let Ok(n) = lit.parse::<num::BigInt>() {
                    Ok(Lit(Literal::Int(n)))
                } else if let Ok(r) = lit.parse::<num::BigRational>() {
                    Ok(Lit(Literal::Real(r)))
                } else {
                    Err(FromOpError(format!("unknown leaf `{lit}`")))
                }
            }
            _ => Err(FromOpError(format!("unknown op `{op}`/{}", children.len()))),
        }
    }
}
