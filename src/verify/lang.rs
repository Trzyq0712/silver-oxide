use egg::*;
use std::cell::Cell;
use std::fmt::{Display, Formatter};

use crate::vmir::BinOp;
use crate::vmir::Literal;
use crate::vmir::MemberId;
use lasso::Rodeo;

thread_local! {
    /// Raw pointer to an interner, set only for the duration of a [`with_interner`]
    /// guard so `Display` can resolve `FuncApp` member ids to their source names.
    /// Null when no guard is active.
    static DISPLAY_INTERNER: Cell<*const Rodeo<MemberId>> = const { Cell::new(std::ptr::null()) };
}

/// Install `interner` as the active display interner until the returned guard
/// drops. While alive, `Symbolic`'s `Display` prints resolved function names.
/// The guard borrows `interner`, so the pointer cannot dangle during its scope.
pub(crate) fn with_interner(interner: &Rodeo<MemberId>) -> InternerGuard<'_> {
    DISPLAY_INTERNER.with(|c| c.set(interner as *const _));
    InternerGuard {
        _marker: std::marker::PhantomData,
    }
}

pub(crate) struct InternerGuard<'a> {
    _marker: std::marker::PhantomData<&'a Rodeo<MemberId>>,
}

impl Drop for InternerGuard<'_> {
    fn drop(&mut self) {
        DISPLAY_INTERNER.with(|c| c.set(std::ptr::null()));
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Symbolic {
    Fresh(u32),
    Lit(Literal),
    Binary(BinOp, [Id; 2]),
    Ite([Id; 3]),
    FuncApp(MemberId, Box<[Id]>),
    RealCast(Id),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Discriminant {
    Fresh(u32),
    Lit(Literal),
    Binary(BinOp),
    Ite,
    FuncApp(MemberId),
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
            FuncApp(_, ids) => ids,
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        use Symbolic::*;
        match self {
            Fresh(..) | Lit(..) => &mut [],
            Binary(_, ids) => ids,
            Ite(ids) => ids,
            RealCast(id) => std::slice::from_mut(id),
            FuncApp(_, ids) => ids,
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
            Symbolic::FuncApp(id, _) => DISPLAY_INTERNER.with(|c| {
                let ptr = c.get();
                if ptr.is_null() {
                    write!(f, "fn{}(..)", id.0)
                } else {
                    // SAFETY: a live `InternerGuard` borrows the interner for
                    // the duration the pointer is non-null (see `with_interner`).
                    let interner = unsafe { &*ptr };
                    write!(f, "{}(..)", interner.resolve(id))
                }
            }),
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
