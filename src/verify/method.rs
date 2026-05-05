use crate::{
    verify::{
        context::VerifyContext,
        heap::{Chunk, Heap},
        lang::Symbolic,
    },
    vmir::{self, inst::InstKind, HeapInstKind},
};

pub fn verify_method(program: &vmir::Program, method_name: &str, method: &vmir::inst::Method) {
    let mut ctx = VerifyContext::new(&program.interner);

    let mut inst_res: Vec<EvalValue> = Vec::new();

    for (idx, vmir::inst::Inst { kind, ty }) in method.0.iter().enumerate() {
        let res = match kind {
            InstKind::Fresh => match ty {
                vmir::Type::Heap => EvalValue::Heap(Heap::empty()),
                _ => EvalValue::Id(ctx.fresh_for_type(ty)),
            },
            InstKind::Unary(op, value) => {
                EvalValue::Id(process_unary(&mut ctx, &inst_res, *op, value))
            }
            InstKind::Binary(op, lhs, rhs) => {
                EvalValue::Id(process_binary(&mut ctx, &inst_res, *op, lhs, rhs))
            }
            InstKind::Ternary(cond, then_, else_) => {
                EvalValue::Id(process_ternary(&mut ctx, &inst_res, cond, then_, else_))
            }
            InstKind::Call(member_id, values) => {
                process_call(&mut ctx, program, &inst_res, *member_id, values)
            }
            InstKind::Heap(heap, loc, heap_inst) => {
                process_heap_inst(&mut ctx, &inst_res, heap, loc, heap_inst)
            }
            InstKind::Assert(cond) => {
                let cond = process_value(&mut ctx, &inst_res, cond);
                let true_ = ctx.add(Symbolic::Bool(true));
                ctx.egraph.union(cond, true_);
                EvalValue::Id(cond)
            }
            InstKind::Assume(cond) => {
                let cond = process_value(&mut ctx, &inst_res, cond);
                let true_ = ctx.add(Symbolic::Bool(true));
                ctx.egraph.union(cond, true_);
                EvalValue::Id(cond)
            }
        };
        inst_res.push(res);
        println!(
            "\n=== EGraph dump ({method_name}) after instruction {idx} ===\n{:#?}",
            ctx.egraph.dump()
        );
    }
}

#[derive(Debug, Clone)]
pub(crate) enum EvalValue {
    Heap(Heap),
    Id(egg::Id),
}

impl EvalValue {
    fn expect_heap(&self) -> &Heap {
        match self {
            Self::Heap(heap) => heap,
            Self::Id(_) => panic!("Expected a Heap value, found an Id"),
        }
    }

    fn expect_id(&self) -> egg::Id {
        match self {
            Self::Heap(_) => panic!("Expected an Id value, found a Heap"),
            Self::Id(id) => *id,
        }
    }
}

fn process_call(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    inst_res: &[EvalValue],
    member_id: vmir::MemberId,
    values: &[vmir::Value],
) -> EvalValue {
    let member_name = program.interner.resolve(&member_id);
    match &program.decls[member_id] {
        vmir::Declaration::Function(_) => {
            let args = values
                .iter()
                .map(|val| process_value(ctx, inst_res, val))
                .collect::<Vec<_>>();
            EvalValue::Id(ctx.add(Symbolic::FuncApp(member_id, args.into())))
        }
        vmir::Declaration::Callable(callable) => {
            if values.len() != callable.signature.args.len() {
                panic!(
                    "Call argument count mismatch for {member_name}: expected {}, got {}",
                    callable.signature.args.len(),
                    values.len()
                );
            }
            if callable.signature.args.as_slice() != callable.body.input_types.as_slice() {
                panic!(
                    "Contract callable input mismatch: signature {:?} != body {:?}",
                    &callable.signature.args, &callable.body.input_types
                );
            }
            EvalValue::Heap(eval_contract_callable(
                ctx,
                callable.semantics,
                &callable.body,
                inst_res,
                values,
            ))
        }
        _ => panic!("Call expected function/contract callable member, got {member_name}"),
    }
}

fn process_unary(
    ctx: &mut VerifyContext<'_>,
    inst_res: &[EvalValue],
    op: vmir::UnOp,
    value: &vmir::Value,
) -> egg::Id {
    let arg = process_value(ctx, inst_res, value);
    ctx.add(Symbolic::Unary(op, arg))
}

fn process_binary(
    ctx: &mut VerifyContext<'_>,
    inst_res: &[EvalValue],
    op: vmir::BinOp,
    lhs: &vmir::Value,
    rhs: &vmir::Value,
) -> egg::Id {
    let lhs = process_value(ctx, inst_res, lhs);
    let rhs = process_value(ctx, inst_res, rhs);
    ctx.add(Symbolic::Binary(op, [lhs, rhs]))
}

fn process_ternary(
    ctx: &mut VerifyContext<'_>,
    inst_res: &[EvalValue],
    cond: &vmir::Value,
    then_: &vmir::Value,
    else_: &vmir::Value,
) -> egg::Id {
    let cond = process_value(ctx, inst_res, cond);
    let then_ = process_value(ctx, inst_res, then_);
    let else_ = process_value(ctx, inst_res, else_);
    ctx.add(Symbolic::Ternary([cond, then_, else_]))
}

fn process_heap_inst(
    ctx: &mut VerifyContext<'_>,
    inst_res: &[EvalValue],
    heap: &vmir::Value,
    loc: &vmir::Value,
    inst: &vmir::inst::HeapInst,
) -> EvalValue {
    let heap_val = process_heap_value(inst_res, heap);
    let addr = process_value(ctx, inst_res, loc);
    match inst {
        vmir::inst::HeapInst::Deref => EvalValue::Id(
            heap_val
                .value_at(addr)
                .unwrap_or_else(|| ctx.fresh_symbolic_value("deref")),
        ),
        vmir::inst::HeapInst::Perm => EvalValue::Id(
            heap_val
                .perm_at(addr)
                .unwrap_or_else(|| ctx.add(Symbolic::Real(num::BigInt::from(0).into()))),
        ),
        vmir::inst::HeapInst::Assign(value) => {
            let value = process_value(ctx, inst_res, value);
            let perm = heap_val
                .perm_at(addr)
                .unwrap_or_else(|| ctx.fresh_symbolic_value("perm"));
            EvalValue::Heap(heap_val.with_chunk(addr, Chunk::new(perm, value)))
        }
        vmir::inst::HeapInst::PermMod(delta) => {
            let delta = process_value(ctx, inst_res, delta);
            let old_perm = heap_val
                .perm_at(addr)
                .unwrap_or_else(|| ctx.add(Symbolic::Real(num::BigInt::from(0).into())));
            let new_perm = ctx.add(Symbolic::Binary(vmir::BinOp::Plus, [old_perm, delta]));
            let old_value = heap_val
                .value_at(addr)
                .unwrap_or_else(|| ctx.fresh_symbolic_value("heap_effect"));
            EvalValue::Heap(heap_val.with_chunk(addr, Chunk::new(new_perm, old_value)))
        }
    }
}

fn eval_contract_callable(
    ctx: &mut VerifyContext<'_>,
    semantics: vmir::ContractCallableSemantics,
    body: &vmir::ContractCallableBody,
    outer_values: &[EvalValue],
    args: &[vmir::Value],
) -> Heap {
    let mut values = args
        .iter()
        .zip(body.input_types.iter())
        .map(|(arg, ty)| match ty {
            vmir::Type::Heap => EvalValue::Heap(process_heap_value(outer_values, arg)),
            _ => EvalValue::Id(process_value(ctx, outer_values, arg)),
        })
        .collect::<Vec<_>>();

    for inst in &body.insts {
        let res = match &inst.kind {
            HeapInstKind::Pure(pure_inst) => {
                EvalValue::Id(process_pure_inst(ctx, &values, pure_inst))
            }
            HeapInstKind::Acc(acc) => {
                let prev_heap = process_heap_value(&values, &acc.heap);
                let addr = process_value(ctx, &values, &acc.addr);
                let delta_perm = process_value(ctx, &values, &acc.perm);
                let next_perm = match semantics {
                    vmir::ContractCallableSemantics::EnsuresInhale => {
                        prev_heap.perm_at(addr).map_or(delta_perm, |p| {
                            ctx.add(Symbolic::Binary(vmir::BinOp::Plus, [p, delta_perm]))
                        })
                    }
                    vmir::ContractCallableSemantics::RequiresExhale => {
                        prev_heap.perm_at(addr).map_or(delta_perm, |p| {
                            ctx.add(Symbolic::Binary(vmir::BinOp::Minus, [p, delta_perm]))
                        })
                    }
                };
                let chunk_value = prev_heap
                    .value_at(addr)
                    .unwrap_or_else(|| ctx.fresh_symbolic_value("heap_effect"));
                EvalValue::Heap(prev_heap.with_chunk(addr, Chunk::new(next_perm, chunk_value)))
            }
        };
        values.push(res);
    }

    let cond = process_value(ctx, &values, &body.res_pure);
    let true_ = ctx.add(Symbolic::Bool(true));
    match semantics {
        vmir::ContractCallableSemantics::RequiresExhale => {
            // TODO: distinguish assert checking from assume when prover plumbing exists.
            ctx.egraph.union(cond, true_);
        }
        vmir::ContractCallableSemantics::EnsuresInhale => {
            ctx.egraph.union(cond, true_);
        }
    }

    process_heap_value(&values, &body.res_heap)
}

fn process_heap_value(inst_res: &[EvalValue], value: &vmir::Value) -> Heap {
    match value {
        vmir::Value::Temp(i) => inst_res[*i].expect_heap().clone(),
        vmir::Value::Literal(other) => panic!("Expected a heap value, found literal {other:?}"),
    }
}

pub fn process_pure_inst(
    ctx: &mut VerifyContext<'_>,
    inst_res: &[EvalValue],
    pure_inst: &vmir::PureInst,
) -> egg::Id {
    match pure_inst {
        vmir::PureInst::Unary(op, val) => {
            let arg = process_value(ctx, inst_res, val);
            ctx.add(Symbolic::Unary(*op, arg))
        }
        vmir::PureInst::Binary(bin_op, value, value1) => {
            let arg1 = process_value(ctx, inst_res, value);
            let arg2 = process_value(ctx, inst_res, value1);
            ctx.add(Symbolic::Binary(*bin_op, [arg1, arg2]))
        }
        vmir::PureInst::Ternary(cond, then, else_) => {
            let cond = process_value(ctx, inst_res, cond);
            let then = process_value(ctx, inst_res, then);
            let else_ = process_value(ctx, inst_res, else_);
            ctx.add(Symbolic::Ternary([cond, then, else_]))
        }
        vmir::PureInst::Call(member_id, values) => {
            let args = values
                .iter()
                .map(|val| process_value(ctx, inst_res, val))
                .collect::<Vec<_>>();
            ctx.add(Symbolic::FuncApp(*member_id, args.into()))
        }
        vmir::PureInst::Heap(heap_dep_inst) => {
            let heap = process_heap_value(inst_res, &heap_dep_inst.heap);
            match &heap_dep_inst.kind {
                vmir::HeapDepInstKind::Perm(addr) => {
                    let addr = process_value(ctx, inst_res, addr);
                    heap.perm_at(addr)
                        .unwrap_or_else(|| ctx.add(Symbolic::Real(num::BigInt::from(0).into())))
                }
                vmir::HeapDepInstKind::Deref(addr) => {
                    let addr = process_value(ctx, inst_res, addr);
                    heap.value_at(addr)
                        .unwrap_or_else(|| ctx.fresh_symbolic_value("deref"))
                }
            }
        }
    }
}

pub fn process_value(
    ctx: &mut VerifyContext<'_>,
    inst_res: &[EvalValue],
    value: &vmir::Value,
) -> egg::Id {
    match value {
        vmir::Value::Temp(i) => inst_res[*i].expect_id(),
        vmir::Value::Literal(lit) => ctx.add(match lit {
            vmir::Literal::Int(i) => Symbolic::Int(i.clone()),
            vmir::Literal::Real(r) => Symbolic::Real(r.clone()),
            vmir::Literal::Bool(b) => Symbolic::Bool(*b),
            vmir::Literal::Null => Symbolic::Null,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use typed_index_collections::TiVec;

    fn int(n: i64) -> vmir::Value {
        vmir::Literal::Int(num::BigInt::from(n)).into()
    }

    fn real(n: i64) -> vmir::Value {
        vmir::Literal::Real(num::BigInt::from(n).into()).into()
    }

    fn make_single_contract_callable_program(
        interner: &mut lasso::Rodeo<vmir::MemberId>,
        name: &str,
        semantics: vmir::ContractCallableSemantics,
    ) -> (vmir::Program, vmir::MemberId) {
        let member_id = interner.get_or_intern(name);
        assert_eq!(member_id.0, 0, "test expects first declaration slot");
        let body = vmir::ContractCallableBody {
            input_types: vec![vmir::Type::Heap],
            insts: vec![vmir::HeapInst {
                kind: vmir::HeapInstKind::Acc(vmir::AccInst {
                    heap: vmir::Value::Temp(0),
                    addr: int(7),
                    perm: real(1),
                }),
                ty: vmir::Type::Heap,
            }],
            res_pure: vmir::Literal::Bool(true).into(),
            res_heap: vmir::Value::Temp(1),
        };
        let mut decls = TiVec::new();
        decls.push(vmir::Declaration::Callable(vmir::Callable {
            name: member_id,
            signature: vmir::ContractCallableSig {
                args: body.input_types.clone(),
            },
            semantics,
            body,
        }));
        (
            vmir::Program {
                decls,
                interner: interner.clone(),
            },
            member_id,
        )
    }

    #[test]
    fn contract_callable_requires_uses_exhale_semantics() {
        let mut interner = lasso::Rodeo::<vmir::MemberId>::new();
        let (program, member_id) = make_single_contract_callable_program(
            &mut interner,
            "callee@requires",
            vmir::ContractCallableSemantics::RequiresExhale,
        );
        let mut ctx = VerifyContext::new(&program.interner);

        let addr = ctx.add(Symbolic::Int(num::BigInt::from(7)));
        let old_perm = ctx.add(Symbolic::Real(num::BigInt::from(2).into()));
        let old_value = ctx.fresh_symbolic_value("v");
        let seed_heap = Heap::empty().with_chunk(addr, Chunk::new(old_perm, old_value));
        let inst_res = vec![EvalValue::Heap(seed_heap)];

        let EvalValue::Heap(next_heap) = process_call(
            &mut ctx,
            &program,
            &inst_res,
            member_id,
            &[vmir::Value::Temp(0)],
        ) else {
            panic!("expected heap result");
        };
        let perm = next_heap.perm_at(addr).expect("missing updated permission");
        let one = ctx.add(Symbolic::Real(num::BigInt::from(1).into()));
        let expected = ctx.add(Symbolic::Binary(vmir::BinOp::Minus, [old_perm, one]));
        assert_eq!(ctx.egraph.find(perm), ctx.egraph.find(expected));
    }

    #[test]
    fn contract_callable_ensures_uses_inhale_semantics() {
        let mut interner = lasso::Rodeo::<vmir::MemberId>::new();
        let (program, member_id) = make_single_contract_callable_program(
            &mut interner,
            "callee@ensures",
            vmir::ContractCallableSemantics::EnsuresInhale,
        );
        let mut ctx = VerifyContext::new(&program.interner);

        let addr = ctx.add(Symbolic::Int(num::BigInt::from(7)));
        let old_perm = ctx.add(Symbolic::Real(num::BigInt::from(2).into()));
        let old_value = ctx.fresh_symbolic_value("v");
        let seed_heap = Heap::empty().with_chunk(addr, Chunk::new(old_perm, old_value));
        let inst_res = vec![EvalValue::Heap(seed_heap)];

        let EvalValue::Heap(next_heap) = process_call(
            &mut ctx,
            &program,
            &inst_res,
            member_id,
            &[vmir::Value::Temp(0)],
        ) else {
            panic!("expected heap result");
        };
        let perm = next_heap.perm_at(addr).expect("missing updated permission");
        let one = ctx.add(Symbolic::Real(num::BigInt::from(1).into()));
        let expected = ctx.add(Symbolic::Binary(vmir::BinOp::Plus, [old_perm, one]));
        assert_eq!(ctx.egraph.find(perm), ctx.egraph.find(expected));
    }
}
