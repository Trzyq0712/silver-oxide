use crate::{
    verify::{
        context::VerifyContext,
        heap::{Chunk, Heap},
        lang::Symbolic,
    },
    vmir::{self, inst::InstKind},
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
        _ => panic!("Call expected function member, got {member_name}"),
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
