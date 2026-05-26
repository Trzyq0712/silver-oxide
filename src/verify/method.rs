use crate::{
    verify::{
        context::VerifyContext,
        heap::{Chunk, Heap},
        lang::Symbolic,
    },
    vmir::{
        self, Acc, BinOp, Declaration, HeapInst, HeapVal, InstKind, Literal, Method,
        MethodHeapExt, MethodInstExt, PureInst, ResourceCall, ResourceInst, Val,
    },
};

#[derive(Debug)]
pub enum VerifyError {
    AssertionFailed,
    InsufficientPermission,
    AbstractResourceCall,
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AssertionFailed => write!(f, "assertion failed"),
            Self::InsufficientPermission => write!(f, "insufficient permission"),
            Self::AbstractResourceCall => write!(f, "call to abstract resource"),
        }
    }
}

struct EvalState {
    vals: Vec<egg::Id>,
    heaps: Vec<Heap>,
    pre_heap: Option<Heap>,
}

impl EvalState {
    fn new() -> Self {
        Self { vals: Vec::new(), heaps: Vec::new(), pre_heap: None }
    }

    fn with_args(args: Vec<egg::Id>) -> Self {
        Self { vals: args, heaps: Vec::new(), pre_heap: None }
    }

    fn get_val(&self, ctx: &mut VerifyContext<'_>, val: &Val) -> egg::Id {
        match val {
            Val::Temp(n) => self.vals[*n],
            Val::Literal(lit) => ctx.add(lit_to_sym(lit)),
        }
    }

    fn get_heap(&self, hv: &HeapVal) -> Heap {
        match hv {
            HeapVal::Empty => Heap::empty(),
            HeapVal::Pre => {
                self.pre_heap.clone().expect("HeapVal::Pre outside resource with requires")
            }
            HeapVal::Temp(n) => self.heaps[*n].clone(),
        }
    }

    fn push_val(&mut self, id: egg::Id) { self.vals.push(id); }
    fn push_heap(&mut self, heap: Heap) { self.heaps.push(heap); }
}

fn lit_to_sym(lit: &Literal) -> Symbolic {
    match lit {
        Literal::Bool(b) => Symbolic::Bool(*b),
        Literal::Int(i) => Symbolic::Int(i.clone()),
        Literal::Real(r) => Symbolic::Real(r.clone()),
        Literal::Null => Symbolic::Null,
    }
}

fn zero_real(ctx: &mut VerifyContext<'_>) -> egg::Id {
    ctx.add(Symbolic::Real(num::BigInt::from(0).into()))
}

fn eval_pure_inst(ctx: &mut VerifyContext<'_>, state: &EvalState, pi: &PureInst) -> egg::Id {
    match pi {
        PureInst::Fresh => ctx.fresh_symbolic_value("fresh"),
        PureInst::Unary(op, v) => {
            let arg = state.get_val(ctx, v);
            ctx.add(Symbolic::Unary(*op, arg))
        }
        PureInst::Binary(op, l, r) => {
            let lhs = state.get_val(ctx, l);
            let rhs = state.get_val(ctx, r);
            ctx.add(Symbolic::Binary(*op, [lhs, rhs]))
        }
        PureInst::Ternary(c, t, e) => {
            let cond = state.get_val(ctx, c);
            let then_ = state.get_val(ctx, t);
            let else_ = state.get_val(ctx, e);
            ctx.add(Symbolic::Ternary([cond, then_, else_]))
        }
        PureInst::Deref(hv, loc) => {
            let heap = state.get_heap(hv);
            let addr = state.get_val(ctx, loc);
            heap.value_at(addr).unwrap_or_else(|| ctx.fresh_symbolic_value("deref"))
        }
        PureInst::Perm(hv, loc) => {
            let heap = state.get_heap(hv);
            let addr = state.get_val(ctx, loc);
            heap.perm_at(addr).unwrap_or_else(|| zero_real(ctx))
        }
        PureInst::FunctionCall(fc) => {
            let args: Vec<egg::Id> =
                fc.args.iter().map(|v| state.get_val(ctx, v)).collect();
            ctx.add(Symbolic::FuncApp(fc.func_id, args.into()))
        }
    }
}

fn heap_acc(ctx: &mut VerifyContext<'_>, acc: &Acc, state: &EvalState) -> Heap {
    let addr = state.get_val(ctx, &acc.loc);
    let perm = state.get_val(ctx, &acc.perm);
    let value = ctx.fresh_symbolic_value("snap");
    Heap::empty().with_chunk(addr, Chunk::new(perm, value))
}

fn heap_union(ctx: &mut VerifyContext<'_>, h1: &Heap, h2: &Heap) -> Heap {
    let mut result = h1.clone();
    for (addr, chunk2) in h2.entries() {
        if let Some(old_perm) = result.perm_at(addr) {
            let new_perm = ctx.add(Symbolic::Binary(BinOp::Plus, [old_perm, chunk2.perm]));
            let value = result.value_at(addr).unwrap();
            result = result.with_chunk(addr, Chunk::new(new_perm, value));
        } else {
            result = result.with_chunk(addr, chunk2.clone());
        }
    }
    result
}

fn heap_subtract(
    ctx: &mut VerifyContext<'_>,
    h1: &Heap,
    h2: &Heap,
) -> Result<Heap, VerifyError> {
    let mut result = h1.clone();
    for (addr, chunk2) in h2.entries() {
        let Some(old_perm) = result.perm_at(addr) else {
            return Err(VerifyError::InsufficientPermission);
        };
        let new_perm = ctx.add(Symbolic::Binary(BinOp::Minus, [old_perm, chunk2.perm]));
        let value = result.value_at(addr).unwrap();
        result = result.with_chunk(addr, Chunk::new(new_perm, value));
    }
    Ok(result)
}

fn eval_resource_heap_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    inst: &HeapInst<!>,
) -> Heap {
    match inst {
        HeapInst::Acc(acc) => heap_acc(ctx, acc, state),
        HeapInst::Add(h1, h2) => heap_union(ctx, &state.get_heap(h1), &state.get_heap(h2)),
        HeapInst::Ternary(_cond, h1, _h2) => state.get_heap(h1),
        HeapInst::Ext(never) => match *never {},
    }
}

fn eval_resource_body_inst(
    ctx: &mut VerifyContext<'_>,
    state: &mut EvalState,
    inst: &ResourceInst,
) {
    match &inst.kind {
        InstKind::Pure(_ty, pi) => {
            let id = eval_pure_inst(ctx, state, pi);
            state.push_val(id);
        }
        InstKind::Heap(hi) => {
            let heap = eval_resource_heap_inst(ctx, state, hi);
            state.push_heap(heap);
        }
        InstKind::Ext(never) => match *never {},
    }
}

fn eval_resource_call(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    caller_state: &EvalState,
    call: &ResourceCall,
) -> Result<(Heap, egg::Id), VerifyError> {
    let Declaration::Resource(r) = &program.decls[call.resource] else {
        panic!("ResourceCall targets non-Resource declaration");
    };
    let body = r.body.as_ref().ok_or(VerifyError::AbstractResourceCall)?;

    let args: Vec<egg::Id> =
        call.args.iter().map(|v| caller_state.get_val(ctx, v)).collect();

    let mut res_state = EvalState::with_args(args);

    if let Some((pre_id, pre_args)) = &r.requires {
        let pre_call = ResourceCall { resource: *pre_id, args: pre_args.clone() };
        let (pre_heap, pre_bool) = eval_resource_call(ctx, program, &res_state, &pre_call)?;
        let true_ = ctx.add(Symbolic::Bool(true));
        ctx.egraph.union(pre_bool, true_);
        res_state.pre_heap = Some(pre_heap);
    }

    for inst in &body.insts {
        eval_resource_body_inst(ctx, &mut res_state, inst);
    }

    let result_heap = res_state.get_heap(&body.res.0);
    let result_bool = res_state.get_val(ctx, &body.res.1);
    Ok((result_heap, result_bool))
}

fn eval_method_heap_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    inst: &HeapInst<MethodHeapExt>,
) -> Result<Heap, VerifyError> {
    match inst {
        HeapInst::Acc(acc) => Ok(heap_acc(ctx, acc, state)),
        HeapInst::Add(h1, h2) => Ok(heap_union(ctx, &state.get_heap(h1), &state.get_heap(h2))),
        HeapInst::Ternary(_cond, h1, _h2) => Ok(state.get_heap(h1)),
        HeapInst::Ext(MethodHeapExt::Sub(h1, h2)) => {
            heap_subtract(ctx, &state.get_heap(h1), &state.get_heap(h2))
        }
    }
}

fn eval_method_inst(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    inst: &vmir::MethodInst,
) -> Result<(), VerifyError> {
    match &inst.kind {
        InstKind::Pure(_ty, pi) => {
            let id = eval_pure_inst(ctx, state, pi);
            state.push_val(id);
        }
        InstKind::Heap(hi) => {
            let heap = eval_method_heap_inst(ctx, state, hi)?;
            state.push_heap(heap);
        }
        InstKind::Ext(ext) => match ext {
            MethodInstExt::Assume(val) => {
                let id = state.get_val(ctx, val);
                let true_ = ctx.add(Symbolic::Bool(true));
                ctx.egraph.union(id, true_);
            }
            MethodInstExt::Assert(val) => {
                let id = state.get_val(ctx, val);
                ctx.egraph.rebuild();
                let true_ = ctx.add(Symbolic::Bool(true));
                if ctx.egraph.find(id) != ctx.egraph.find(true_) {
                    return Err(VerifyError::AssertionFailed);
                }
            }
            MethodInstExt::ResourceCall(call) => {
                let (delta, bool_id) = eval_resource_call(ctx, program, state, call)?;
                state.push_heap(delta);
                state.push_val(bool_id);
            }
        },
    }
    Ok(())
}

pub fn verify_method(
    program: &vmir::Program,
    method_name: &str,
    method: &Method,
) -> Result<(), VerifyError> {
    let mut ctx = VerifyContext::new(&program.interner);
    let mut state = EvalState::new();

    for inst in &method.insts {
        eval_method_inst(&mut ctx, program, &mut state, inst)?;
    }

    Ok(())
}
