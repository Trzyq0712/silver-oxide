use egg::{Analysis, DidMerge, EGraph, Id};
use num::BigRational;

use crate::verify::lang::Symbolic;
use crate::vmir::{BinOp, Literal};

/// Const-fold analysis data: a three-state lattice over an e-class's folded
/// value. **Type-free**: only the literal is tracked (types are reconstructed
/// for visualization from the side oracle in `verify::context`).
///
/// - `Unknown`: not (yet) a constant.
/// - `Known(lit)`: folds to `lit`.
/// - `Inconsistent`: two **same-typed** literals of differing value were merged
///   (e.g. `true == false`, `5 == 6`) — the e-class, and thus the whole
///   verification unit, is contradictory. Merging literals of *different* types
///   is instead a verifier panic (a genuine type error).
#[derive(Debug, Clone, PartialEq)]
pub enum Data {
    Unknown,
    Known(Literal),
    Inconsistent,
}

impl Data {
    /// The folded literal, if this e-class is a known constant.
    pub fn known(&self) -> Option<&Literal> {
        match self {
            Data::Known(lit) => Some(lit),
            _ => None,
        }
    }

    /// Whether this e-class merged conflicting same-typed literals.
    pub fn is_inconsistent(&self) -> bool {
        matches!(self, Data::Inconsistent)
    }
}

/// Whether two literals are of the same VMIR type (so a value conflict is an
/// inconsistency rather than a type error).
fn same_type(a: &Literal, b: &Literal) -> bool {
    use Literal::*;
    matches!(
        (a, b),
        (Bool(_), Bool(_)) | (Int(_), Int(_)) | (Real(_), Real(_)) | (Null, Null)
    )
}

#[derive(Default, Debug, Clone)]
pub struct ConstFold;

impl Analysis<Symbolic> for ConstFold {
    type Data = Data;

    fn make(egraph: &mut EGraph<Symbolic, Self>, enode: &Symbolic, _id: Id) -> Self::Data {
        use Data::{Inconsistent, Known, Unknown};
        match enode {
            Symbolic::Lit(lit) => Known(lit.clone()),

            Symbolic::Fresh(_) | Symbolic::FuncApp(..) => Unknown,

            Symbolic::RealCast(c) => match &egraph[*c].data {
                Known(Literal::Int(n)) => Known(Literal::Real(BigRational::from(n.clone()))),
                Known(_) => unreachable!("RealCast operand must be an integer literal"),
                Inconsistent => Inconsistent,
                Unknown => Unknown,
            },

            Symbolic::Binary(op, [l, r]) => match (&egraph[*l].data, &egraph[*r].data) {
                (Inconsistent, _) | (_, Inconsistent) => Inconsistent,
                (Known(lv), Known(rv)) => eval_binary(*op, lv, rv).map_or(Unknown, Known),
                _ => Unknown,
            },

            Symbolic::Ite([c, t, e]) => match &egraph[*c].data {
                Known(Literal::Bool(true)) => egraph[*t].data.clone(),
                Known(Literal::Bool(false)) => egraph[*e].data.clone(),
                Known(_) => unreachable!("Condition of ITE must be a boolean literal"),
                Inconsistent => Inconsistent,
                Unknown => Unknown,
            },
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        use Data::{Inconsistent, Known, Unknown};
        match (&*a, &b) {
            (Inconsistent, Inconsistent) => DidMerge(false, false),
            (Inconsistent, _) => DidMerge(false, true),
            (_, Inconsistent) => {
                *a = Inconsistent;
                DidMerge(true, false)
            }
            (Known(x), Known(y)) => {
                if x == y {
                    DidMerge(false, false)
                } else if same_type(x, y) {
                    // Same-typed conflict ⇒ contradiction (not a panic).
                    *a = Inconsistent;
                    DidMerge(true, true)
                } else {
                    panic!("type error: merged literals of different types: {x:?} vs {y:?}");
                }
            }
            (Unknown, Known(y)) => {
                *a = Known(y.clone());
                DidMerge(true, false)
            }
            (Known(_), Unknown) => DidMerge(false, true),
            (Unknown, Unknown) => DidMerge(false, false),
        }
    }

    fn modify(egraph: &mut EGraph<Symbolic, Self>, id: Id) {
        if let Data::Known(lit) = egraph[id].data.clone() {
            let lit_id = egraph.add(Symbolic::Lit(lit));
            egraph.union(id, lit_id);
        }
    }
}

/// Fold a binary op over two literals. Operands are **homogeneous** (the
/// frontend inserts `real(..)` casts), so each arithmetic op dispatches on the
/// shared literal variant and the division mode follows the operand type.
/// `None` for a literal division by zero: the term is unspecified (an
/// uninterpreted value, matching SMT semantics), not a fold-time panic —
/// well-definedness is a separate obligation, and never checked at all inside
/// an axiom body.
pub fn eval_binary(op: BinOp, l: &Literal, r: &Literal) -> Option<Literal> {
    use Literal::{Int, Real};
    Some(match op {
        BinOp::Plus => match (l, r) {
            (Int(a), Int(b)) => Int(a + b),
            (Real(a), Real(b)) => Real(a + b),
            _ => unreachable!("non-homogeneous operands for Plus: {l:?}, {r:?}"),
        },
        BinOp::Minus => match (l, r) {
            (Int(a), Int(b)) => Int(a - b),
            (Real(a), Real(b)) => Real(a - b),
            _ => unreachable!("non-homogeneous operands for Minus: {l:?}, {r:?}"),
        },
        BinOp::Mult => match (l, r) {
            (Int(a), Int(b)) => Int(a * b),
            (Real(a), Real(b)) => Real(a * b),
            _ => unreachable!("non-homogeneous operands for Mult: {l:?}, {r:?}"),
        },
        BinOp::Div => match (l, r) {
            (Int(a), Int(b)) if *b != num::BigInt::ZERO => Int(a / b),
            (Real(a), Real(b)) if *b != num::BigRational::from(num::BigInt::ZERO) => Real(a / b),
            (Int(_) | Real(_), Int(_) | Real(_)) => return None,
            _ => unreachable!("non-homogeneous operands for Div: {l:?}, {r:?}"),
        },
        BinOp::Eq => Literal::Bool(l == r),
        BinOp::Lt => match (l, r) {
            (Int(a), Int(b)) => Literal::Bool(a < b),
            (Real(a), Real(b)) => Literal::Bool(a < b),
            _ => unreachable!("non-homogeneous operands for Lt: {l:?}, {r:?}"),
        },
        _ => unimplemented!("Operator {op:?} is not implemented yet"),
    })
}
