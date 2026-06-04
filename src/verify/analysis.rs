use egg::{Analysis, DidMerge, EGraph, Id};
use num::BigRational;

use crate::verify::lang::Symbolic;
use crate::vmir::{BinOp, Literal};

/// Const-fold analysis. **Type-free**: only the folded literal value is tracked
/// (types are reconstructed for visualization from the side oracle in
/// `verify::context`, not stored here).
#[derive(Debug, Clone, PartialEq)]
pub struct Data {
    pub value: Option<Literal>,
}

#[derive(Default, Debug, Clone)]
pub struct ConstFold;

impl Analysis<Symbolic> for ConstFold {
    type Data = Data;

    fn make(egraph: &mut EGraph<Symbolic, Self>, enode: &Symbolic, _id: Id) -> Self::Data {
        let value = match enode {
            Symbolic::Lit(lit) => Some(lit.clone()),

            Symbolic::Fresh(_) | Symbolic::FuncApp(..) => None,

            Symbolic::RealCast(c) => match &egraph[*c].data.value {
                Some(Literal::Int(n)) => Some(Literal::Real(BigRational::from(n.clone()))),
                Some(_) => unreachable!("RealCast operand must be an integer literal"),
                _ => None,
            },

            Symbolic::Binary(op, [l, r]) => {
                match (&egraph[*l].data.value, &egraph[*r].data.value) {
                    (Some(lv), Some(rv)) => Some(eval_binary(*op, lv, rv)),
                    _ => None,
                }
            }

            Symbolic::Ite([c, t, e]) => match &egraph[*c].data.value {
                Some(Literal::Bool(true)) => egraph[*t].data.value.clone(),
                Some(Literal::Bool(false)) => egraph[*e].data.value.clone(),
                Some(_) => unreachable!("Condition of ITE must be a boolean literal"),
                _ => None,
            },
        };
        Data { value }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let mut did_merge = DidMerge(false, false);

        match (&a.value, &b.value) {
            (Some(va), Some(vb)) if va == vb => {} // Already equal
            (None, Some(_)) => {
                a.value = b.value.clone();
                did_merge.0 = true;
            }
            (Some(_), None) => {
                did_merge.1 = true;
            }
            (None, None) => {}
            _ => unreachable!(
                "Conflicting values during merge: {:?} vs {:?}",
                a.value, b.value
            ),
        }

        did_merge
    }

    fn modify(egraph: &mut EGraph<Symbolic, Self>, id: Id) {
        let data = egraph[id].data.clone();

        if let Some(lit) = data.value {
            let lit_node = Symbolic::Lit(lit);
            let lit_id = egraph.add(lit_node);
            egraph.union(id, lit_id);
        }
    }
}

/// Fold a binary op over two literals. Operands are **homogeneous** (the
/// frontend inserts `real(..)` casts), so each arithmetic op dispatches on the
/// shared literal variant and the division mode follows the operand type.
pub fn eval_binary(op: BinOp, l: &Literal, r: &Literal) -> Literal {
    use Literal::{Int, Real};
    match op {
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
            (Int(a), Int(b)) => Int(a / b),
            (Real(a), Real(b)) => Real(a / b),
            _ => unreachable!("non-homogeneous operands for Div: {l:?}, {r:?}"),
        },
        BinOp::Eq => Literal::Bool(l == r),
        BinOp::Lt => match (l, r) {
            (Int(a), Int(b)) => Literal::Bool(a < b),
            (Real(a), Real(b)) => Literal::Bool(a < b),
            _ => unreachable!("non-homogeneous operands for Lt: {l:?}, {r:?}"),
        },
        _ => unimplemented!("Operator {op:?} is not implemented yet"),
    }
}
