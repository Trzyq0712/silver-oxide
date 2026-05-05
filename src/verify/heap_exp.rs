use crate::{
    verify::{
        context::VerifyContext,
        heap::{Chunk, Heap},
        lang::Symbolic,
    },
    vmir,
};

#[derive(Debug, Clone)]
pub(crate) enum EvalValue {
    Heap(Heap),
    Id(egg::Id),
}

impl EvalValue {
    pub(crate) fn expect_heap(&self) -> &Heap {
        match self {
            Self::Heap(heap) => heap,
            Self::Id(_) => panic!("Expected a Heap value, found an Id"),
        }
    }

    pub(crate) fn expect_id(&self) -> egg::Id {
        match self {
            Self::Heap(_) => panic!("Expected an Id value, found a Heap"),
            Self::Id(id) => *id,
        }
    }
}

fn zero_real(ctx: &mut VerifyContext<'_>) -> egg::Id {
    ctx.add(Symbolic::Real(num::BigInt::from(0).into()))
}

fn eval_id_value(
    ctx: &mut VerifyContext<'_>,
    values: &[EvalValue],
    value: &vmir::Value,
) -> egg::Id {
    match value {
        vmir::Value::Temp(i) => values[*i].expect_id(),
        vmir::Value::Literal(lit) => ctx.add(match lit {
            vmir::Literal::Int(i) => Symbolic::Int(i.clone()),
            vmir::Literal::Real(r) => Symbolic::Real(r.clone()),
            vmir::Literal::Bool(b) => Symbolic::Bool(*b),
            vmir::Literal::Null => Symbolic::Null,
        }),
    }
}

fn eval_heap_value<'a>(values: &'a [EvalValue], value: &vmir::Value) -> &'a Heap {
    match value {
        vmir::Value::Temp(i) => values[*i].expect_heap(),
        vmir::Value::Literal(other) => panic!("Expected a heap value, found literal {other:?}"),
    }
}

fn value_type_in_heap_exp(heap_exp: &vmir::HeapExp, value: &vmir::Value) -> Option<vmir::Type> {
    match value {
        vmir::Value::Temp(i) => {
            if *i < heap_exp.input_types.len() {
                heap_exp.input_types.get(*i).cloned()
            } else {
                heap_exp
                    .insts
                    .get(*i - heap_exp.input_types.len())
                    .map(|inst| inst.ty.clone())
            }
        }
        vmir::Value::Literal(vmir::Literal::Bool(_)) => Some(vmir::Type::Bool),
        vmir::Value::Literal(vmir::Literal::Int(_)) => Some(vmir::Type::Int),
        vmir::Value::Literal(vmir::Literal::Real(_)) => Some(vmir::Type::Real),
        vmir::Value::Literal(vmir::Literal::Null) => Some(vmir::Type::Ref),
    }
}

fn value_prefix_from_addr_type(
    ctx: &VerifyContext<'_>,
    heap_exp: &vmir::HeapExp,
    addr: &vmir::Value,
) -> String {
    let Some(ty) = value_type_in_heap_exp(heap_exp, addr) else {
        return "unknown_ty".to_owned();
    };
    let vmir::Type::Addr(inner) = ty else {
        return "unknown_ty".to_owned();
    };
    match &*inner {
        vmir::Type::Domain(id) => ctx.interner.resolve(id).to_string(),
        _ => inner.to_string(),
    }
}

fn eval_pure_inst(
    ctx: &mut VerifyContext<'_>,
    values: &[EvalValue],
    pure_inst: &vmir::PureInst,
) -> egg::Id {
    match pure_inst {
        vmir::PureInst::Unary(op, val) => {
            let arg = eval_id_value(ctx, values, val);
            ctx.add(Symbolic::Unary(*op, arg))
        }
        vmir::PureInst::Binary(bin_op, lhs, rhs) => {
            let lhs = eval_id_value(ctx, values, lhs);
            let rhs = eval_id_value(ctx, values, rhs);
            ctx.add(Symbolic::Binary(*bin_op, [lhs, rhs]))
        }
        vmir::PureInst::Ternary(cond, then_v, else_v) => {
            let cond = eval_id_value(ctx, values, cond);
            let then_v = eval_id_value(ctx, values, then_v);
            let else_v = eval_id_value(ctx, values, else_v);
            ctx.add(Symbolic::Ternary([cond, then_v, else_v]))
        }
        vmir::PureInst::Call(member_id, args) => {
            let args = args
                .iter()
                .map(|arg| eval_id_value(ctx, values, arg))
                .collect::<Vec<_>>();
            ctx.add(Symbolic::FuncApp(*member_id, args.into()))
        }
        vmir::PureInst::Heap(heap_dep_inst) => {
            let heap = eval_heap_value(values, &heap_dep_inst.heap);
            match &heap_dep_inst.kind {
                vmir::HeapDepInstKind::Perm(addr) => {
                    let addr = eval_id_value(ctx, values, addr);
                    heap.perm_at(addr).unwrap_or_else(|| zero_real(ctx))
                }
                vmir::HeapDepInstKind::Deref(addr) => {
                    let addr = eval_id_value(ctx, values, addr);
                    heap.value_at(addr)
                        .unwrap_or_else(|| ctx.fresh_symbolic_value("deref"))
                }
            }
        }
    }
}

pub(crate) fn inhale_heap_exp(
    ctx: &mut VerifyContext<'_>,
    heap_exp: &vmir::HeapExp,
    inputs: &[EvalValue],
) -> Heap {
    let mut values = inputs.to_vec();

    for inst in &heap_exp.insts {
        let result = match &inst.kind {
            vmir::HeapInstKind::Pure(pure_inst) => {
                EvalValue::Id(eval_pure_inst(ctx, &values, pure_inst))
            }
            vmir::HeapInstKind::Acc(acc) => {
                let prev_heap = eval_heap_value(&values, &acc.heap);
                let addr = eval_id_value(ctx, &values, &acc.addr);
                let delta_perm = eval_id_value(ctx, &values, &acc.perm);
                let new_perm = prev_heap.perm_at(addr).map_or(delta_perm, |old_perm| {
                    ctx.add(Symbolic::Binary(vmir::BinOp::Plus, [old_perm, delta_perm]))
                });

                let chunk_value = prev_heap.value_at(addr).unwrap_or_else(|| {
                    let type_prefix = value_prefix_from_addr_type(ctx, heap_exp, &acc.addr);
                    ctx.fresh_symbolic_value(&type_prefix)
                });
                let next_heap = prev_heap.with_chunk(addr, Chunk::new(new_perm, chunk_value));
                EvalValue::Heap(next_heap)
            }
        };
        values.push(result);
    }

    let res_pure = eval_id_value(ctx, &values, &heap_exp.res_pure);
    let true_ = ctx.add(Symbolic::Bool(true));
    ctx.egraph.union(res_pure, true_);

    eval_heap_value(&values, &heap_exp.res_impure).clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vmir::{HeapInst, HeapInstKind, Literal, Type, Value};

    fn real(n: i64) -> Value {
        Literal::Real(num::BigInt::from(n).into()).into()
    }

    fn int(n: i64) -> Value {
        Literal::Int(num::BigInt::from(n)).into()
    }

    #[test]
    fn inhale_accumulates_permissions_for_repeated_address() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = VerifyContext::new(&interner);
        let heap_exp = vmir::HeapExp {
            input_types: vec![Type::Heap],
            insts: vec![
                HeapInst {
                    kind: HeapInstKind::Acc(vmir::AccInst {
                        heap: Value::Temp(0),
                        addr: int(7),
                        perm: real(1),
                    }),
                    ty: Type::Heap,
                },
                HeapInst {
                    kind: HeapInstKind::Acc(vmir::AccInst {
                        heap: Value::Temp(1),
                        addr: int(7),
                        perm: real(2),
                    }),
                    ty: Type::Heap,
                },
            ],
            res_pure: Literal::Bool(true).into(),
            res_impure: Value::Temp(2),
        };

        let out_heap = inhale_heap_exp(&mut ctx, &heap_exp, &[EvalValue::Heap(Heap::empty())]);

        let addr = ctx.egraph.add(Symbolic::Int(num::BigInt::from(7)));
        let perm = out_heap.perm_at(addr).expect("missing chunk for address");

        let zero = ctx.egraph.add(Symbolic::Real(num::BigInt::from(0).into()));
        let p1 = ctx.egraph.add(Symbolic::Real(num::BigInt::from(1).into()));
        let p2 = ctx.egraph.add(Symbolic::Real(num::BigInt::from(2).into()));
        let sum1 = ctx
            .egraph
            .add(Symbolic::Binary(vmir::BinOp::Plus, [zero, p1]));
        let sum2 = ctx
            .egraph
            .add(Symbolic::Binary(vmir::BinOp::Plus, [sum1, p2]));

        assert_eq!(ctx.egraph.find(perm), ctx.egraph.find(sum2));
    }

    #[test]
    fn inhale_assumes_final_pure_result_true() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = VerifyContext::new(&interner);
        let heap_exp = vmir::HeapExp {
            input_types: vec![Type::Heap],
            insts: vec![],
            res_pure: Literal::Bool(false).into(),
            res_impure: Value::Temp(0),
        };

        let _ = inhale_heap_exp(&mut ctx, &heap_exp, &[EvalValue::Heap(Heap::empty())]);

        let false_ = ctx.egraph.add(Symbolic::Bool(false));
        let true_ = ctx.egraph.add(Symbolic::Bool(true));
        assert_eq!(ctx.egraph.find(false_), ctx.egraph.find(true_));
    }

    #[test]
    fn inhale_keeps_existing_value_for_existing_address() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = VerifyContext::new(&interner);
        let addr = ctx.egraph.add(Symbolic::Int(num::BigInt::from(3)));
        let seed = ctx.egraph.add(Symbolic::Fresh(egg::Symbol::from("seed")));
        let zero = ctx.egraph.add(Symbolic::Real(num::BigInt::from(0).into()));
        let input_heap = Heap::empty().with_chunk(addr, Chunk::new(zero, seed));

        let heap_exp = vmir::HeapExp {
            input_types: vec![Type::Heap],
            insts: vec![HeapInst {
                kind: HeapInstKind::Acc(vmir::AccInst {
                    heap: Value::Temp(0),
                    addr: int(3),
                    perm: real(1),
                }),
                ty: Type::Heap,
            }],
            res_pure: Literal::Bool(true).into(),
            res_impure: Value::Temp(1),
        };

        let out_heap = inhale_heap_exp(&mut ctx, &heap_exp, &[EvalValue::Heap(input_heap)]);
        let value = out_heap.value_at(addr).expect("missing chunk value");
        assert_eq!(ctx.egraph.find(value), ctx.egraph.find(seed));
    }
}
