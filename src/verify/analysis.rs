use egg::{Analysis, DidMerge, EGraph, Id};
use num::BigRational;

use crate::verify::lang::Symbolic;
use crate::vmir::{BinOp, Literal, Type};

#[derive(Debug, Clone, PartialEq)]
pub struct Data {
    pub ty: Type,
    pub value: Option<Literal>,
}

#[derive(Default, Debug, Clone)]
pub struct ConstFold;

impl Analysis<Symbolic> for ConstFold {
    type Data = Data;

    fn make(egraph: &mut EGraph<Symbolic, Self>, enode: &Symbolic, _id: Id) -> Self::Data {
        match enode {
            Symbolic::Lit(lit) => Data {
                ty: match lit {
                    Literal::Null => Type::Ref,
                    Literal::Bool(_) => Type::Bool,
                    Literal::Int(_) => Type::Int,
                    Literal::Real(_) => Type::Real,
                },
                value: Some(lit.clone()),
            },

            Symbolic::Fresh(_, ty) | Symbolic::FuncApp(_, ty, _) => Data {
                ty: ty.clone(),
                value: None,
            },

            Symbolic::Binary(op, ty, [l, r]) => {
                let lv = &egraph[*l].data.value;
                let rv = &egraph[*r].data.value;

                let value = match (lv, rv) {
                    (Some(lv), Some(rv)) => Some(eval_binary(*op, ty, lv, rv)),
                    _ => None,
                };

                Data {
                    ty: ty.clone(),
                    value,
                }
            }

            Symbolic::Ite(ty, [c, t, e]) => {
                let c_val = &egraph[*c].data.value;

                let value = match c_val {
                    Some(Literal::Bool(true)) => egraph[*t].data.value.clone(),
                    Some(Literal::Bool(false)) => egraph[*e].data.value.clone(),
                    Some(_) => unreachable!("Condition of ITE must be a boolean literal"),
                    _ => None,
                };

                Data {
                    ty: ty.clone(),
                    value,
                }
            }
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let mut did_merge = DidMerge(false, false);

        if a.ty != b.ty {
            unreachable!("Type mismatch during merge");
        }

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

pub fn eval_binary(op: BinOp, ty: &Type, l: &Literal, r: &Literal) -> Literal {
    match op {
        BinOp::Plus => match (l, r) {
            (Literal::Int(a), Literal::Int(b)) => Literal::Int(a + b),
            (Literal::Real(a), Literal::Real(b)) => Literal::Real(a + b),
            _ => unreachable!("Mixed types or invalid operands for Plus"),
        },

        BinOp::Minus => match (l, r) {
            (Literal::Int(a), Literal::Int(b)) => Literal::Int(a - b),
            (Literal::Real(a), Literal::Real(b)) => Literal::Real(a - b),
            _ => unreachable!("Mixed types or invalid operands for Minus"),
        },

        BinOp::Mult => match (l, r) {
            (Literal::Int(a), Literal::Int(b)) => Literal::Int(a * b),
            (Literal::Real(a), Literal::Real(b)) => Literal::Real(a * b),
            // Promotion is allowed for Mult
            (Literal::Int(b), Literal::Real(a)) => Literal::Real(BigRational::from(a.clone()) * b),
            (Literal::Real(a), Literal::Int(b)) => Literal::Real(a * BigRational::from(b.clone())),
            _ => unreachable!("Invalid operands for Mult"),
        },

        BinOp::Div => match ty {
            // Target type dictates the division mode
            Type::Real => {
                let a = match l {
                    Literal::Int(i) => BigRational::from(i.clone()),
                    Literal::Real(r) => r.clone(),
                    _ => unreachable!("Invalid left operand for Real division"),
                };
                let b = match r {
                    Literal::Int(i) => BigRational::from(i.clone()),
                    Literal::Real(r) => r.clone(),
                    _ => unreachable!("Invalid right operand for Real division"),
                };
                Literal::Real(a / b)
            }

            Type::Int => match (l, r) {
                (Literal::Int(a), Literal::Int(b)) => Literal::Int(a / b),
                _ => unreachable!("Int division requires Int operands"),
            },

            _ => unreachable!("Division result must be of type Int or Real"),
        },

        _ => unimplemented!("Operator {:?} is not implemented yet", op),
    }
}
