use egg::*;
use std::fmt::{Display, Formatter};

use crate::vmir::BinOp;
use crate::vmir::Literal;
use crate::vmir::Type;

/// A verifier-allocated function-application id in the e-graph. **Disconnected
/// from VMIR `MemberId`**: the verifier assigns these (see `verify::func_registry`) — a
/// plain function reuses its declaration's index, ADT constructor/projection/tag
/// ops get one freshly-minted index per *concept* (polymorphic; the type
/// instantiation rides in the `FuncApp` discriminant, not the id).
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct FuncId(pub usize);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Symbolic {
    Fresh(u32),
    Lit(Literal),
    Binary(BinOp, [Id; 2]),
    Ite([Id; 3]),
    /// A function application `f[type_args](value_args)`. The e-graph is
    /// **polymorphic**: one `FuncId` per concept, with the **ground** type
    /// instantiation carried in the enode payload. It is *not* a child (ground
    /// types never merge, so they want no e-class) and *not* in the discriminant
    /// (which would fragment egg's `classes_by_op` op-index per instantiation).
    /// Distinctness — `mk[Int]` ≠ `mk[Bool]` — comes from the enode's derived
    /// `Eq`/`Hash` via egg's congruence `memo` (a `HashMap<L, Id>` keyed by the
    /// full enode), so two instantiations never dedup/merge. `children()` returns
    /// only the value args; the [`Discriminant`] is the concept `FuncId` alone.
    /// Addresses are ordinary function applications too: a field/predicate's
    /// address function (its own `FuncId`) over its args, with the rich
    /// `Type::Addr{group,value,bound}` as its return type (recorded in
    /// `func_ret_types` and recoverable by `infer_type`). No dedicated location
    /// sort or sentinel id. (No rewrite rule matches an address `FuncId`.)
    FuncApp(FuncId, Box<[Type]>, Box<[Id]>),
    RealCast(Id),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Discriminant {
    Fresh(u32),
    Lit(Literal),
    Binary(BinOp),
    Ite,
    /// The concept id alone (no type instantiation). Keeping the type args out of
    /// the discriminant means egg's `classes_by_op` indexes one bucket per concept
    /// (not per instantiation), and `discriminant()` stays a cheap `Copy`.
    /// Distinctness across instantiations does *not* rely on this — it comes from
    /// the full-enode `Eq`/`Hash` in the congruence memo (see [`Symbolic::FuncApp`]).
    FuncApp(FuncId),
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
            S::FuncApp(id, _, _) => D::FuncApp(*id),
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
            // Operator identity is the concept id + value arity, consistent with
            // the type-blind discriminant. (Distinctness across instantiations is
            // the memo's job via full-enode `Eq`, not `matches`.)
            (FuncApp(id1, _, args1), FuncApp(id2, _, args2)) => {
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
            // Type args are in the payload, not children — only value args.
            FuncApp(_, _, ids) => ids,
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        use Symbolic::*;
        match self {
            Fresh(..) | Lit(..) => &mut [],
            Binary(_, ids) => ids,
            Ite(ids) => ids,
            RealCast(id) => std::slice::from_mut(id),
            FuncApp(_, _, ids) => ids,
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
            // Id-only label, with the ground type instantiation folded in (so each
            // instantiation is a distinct, self-describing node). The viz resolves
            // the `fn{id}` token to the concept's source name when it renders the
            // dot (it holds the interner).
            Symbolic::FuncApp(id, tys, _) => {
                if tys.is_empty() {
                    write!(f, "fn{}", id.0)
                } else {
                    // Type-argument instantiation is rendered in angle brackets
                    // (`fn3<Int>`), matching VMIR Display — `[..]` is reserved for a
                    // generic binder's arity and for heaps.
                    let args: Vec<String> = tys.iter().map(|t| t.to_string()).collect();
                    write!(f, "fn{}<{}>", id.0, args.join(", "))
                }
            }
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
