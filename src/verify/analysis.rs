//! Constant-folding analysis for the `Symbolic` e-graph.
//!
//! Each e-class carries an `Option<ConstVal>`. When all children of an
//! arithmetic / boolean / comparison node have known constants, the
//! analysis computes the result and unions the e-class with the literal
//! node for that constant (via `modify`). This turns sequences like
//! `1 - 1` into `0`, `(1 - 1) - 1` into `-1`, etc., automatically — the
//! heap-permission code can then read the folded value via the usual
//! e-class scan.

use egg::{Analysis, DidMerge, EGraph, Id};
use num::{BigInt, BigRational, Zero};

use crate::verify::lang::Symbolic;
use crate::vmir::{BinOp, UnOp};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstVal {
    Bool(bool),
    Int(BigInt),
    Real(BigRational),
    Null,
}

#[derive(Default, Debug, Clone)]
pub struct ConstFold;

impl Analysis<Symbolic> for ConstFold {
    type Data = Option<ConstVal>;

    fn make(egraph: &mut EGraph<Symbolic, Self>, enode: &Symbolic, _id: Id) -> Self::Data {
        match enode {
            Symbolic::Bool(b) => Some(ConstVal::Bool(*b)),
            Symbolic::Int(i) => Some(ConstVal::Int(i.clone())),
            Symbolic::Real(r) => Some(ConstVal::Real(r.clone())),
            Symbolic::Null => Some(ConstVal::Null),
            Symbolic::Binary(op, [l, r]) => {
                let lc = egraph[*l].data.clone()?;
                let rc = egraph[*r].data.clone()?;
                eval_binary(*op, &lc, &rc)
            }
            Symbolic::Unary(op, x) => {
                let xc = egraph[*x].data.clone()?;
                eval_unary(*op, &xc)
            }
            Symbolic::Ternary([c, t, e]) => match egraph[*c].data.as_ref()? {
                ConstVal::Bool(true) => egraph[*t].data.clone(),
                ConstVal::Bool(false) => egraph[*e].data.clone(),
                _ => None,
            },
            Symbolic::Fresh(_) | Symbolic::FuncApp(_, _) => None,
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        match (a.as_ref(), b.as_ref()) {
            (Some(va), Some(vb)) if va == vb => DidMerge(false, false),
            (None, Some(_)) => {
                *a = b;
                DidMerge(true, false)
            }
            (Some(_), None) => DidMerge(false, true),
            (None, None) => DidMerge(false, false),
            // Conflicting constants. Either an inconsistency in the
            // program or an over-eager union. Keep `a` and report mutation
            // of `b` to satisfy egg's invariant.
            _ => DidMerge(false, true),
        }
    }

    fn modify(egraph: &mut EGraph<Symbolic, Self>, id: Id) {
        let Some(cv) = egraph[id].data.clone() else { return };
        let lit = match cv {
            ConstVal::Bool(b) => Symbolic::Bool(b),
            ConstVal::Int(i) => Symbolic::Int(i),
            ConstVal::Real(r) => Symbolic::Real(r),
            ConstVal::Null => Symbolic::Null,
        };
        let lit_id = egraph.add(lit);
        egraph.union(id, lit_id);
    }
}

fn eval_binary(op: BinOp, l: &ConstVal, r: &ConstVal) -> Option<ConstVal> {
    use ConstVal::*;
    match (op, l, r) {
        (BinOp::Plus, Int(a), Int(b)) => Some(Int(a + b)),
        (BinOp::Plus, Real(a), Real(b)) => Some(Real(a + b)),
        (BinOp::Minus, Int(a), Int(b)) => Some(Int(a - b)),
        (BinOp::Minus, Real(a), Real(b)) => Some(Real(a - b)),
        (BinOp::Mult, Int(a), Int(b)) => Some(Int(a * b)),
        (BinOp::Mult, Real(a), Real(b)) => Some(Real(a * b)),
        (BinOp::Div, Int(a), Int(b)) if !b.is_zero() => Some(Int(a / b)),
        (BinOp::Div, Real(a), Real(b)) if !b.is_zero() => Some(Real(a / b)),
        (BinOp::Mod, Int(a), Int(b)) if !b.is_zero() => Some(Int(a % b)),
        (BinOp::Eq, a, b) => Some(Bool(a == b)),
        (BinOp::Lt, Int(a), Int(b)) => Some(Bool(a < b)),
        (BinOp::Lt, Real(a), Real(b)) => Some(Bool(a < b)),
        _ => None,
    }
}

fn eval_unary(op: UnOp, x: &ConstVal) -> Option<ConstVal> {
    use ConstVal::*;
    match (op, x) {
        (UnOp::Not, Bool(b)) => Some(Bool(!b)),
        (UnOp::Neg, Int(i)) => Some(Int(-i)),
        (UnOp::Neg, Real(r)) => Some(Real(-r)),
        _ => None,
    }
}
