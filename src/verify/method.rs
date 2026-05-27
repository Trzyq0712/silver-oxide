use crate::{
    verify::{
        context::VerifyContext,
        heap::{Chunk, Heap},
        lang::Symbolic,
    },
    vmir::{
        self, Acc, BinOp, Declaration, HeapInst, HeapVal, InstKind, Literal, Method, MethodHeapExt,
        MethodHeapVal, MethodInstExt, PureInst, ResourceCall, ResourceHeapVal, ResourceInst, Val,
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
    /// Set only inside a resource body whose owning `Resource` has a
    /// `requires`. Referenced by `HeapVal::CtxHeap(())` operands inside
    /// that body.
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

    fn push_val(&mut self, id: egg::Id) { self.vals.push(id); }
    fn push_heap(&mut self, heap: Heap) { self.heaps.push(heap); }
}

/// Heap-fetch for method bodies. `CtxHeap` carries `!` here — uninhabited.
fn get_heap_method(state: &EvalState, hv: &MethodHeapVal) -> Heap {
    match hv {
        HeapVal::Empty => Heap::empty(),
        HeapVal::Temp(n) => state.heaps[*n].clone(),
        HeapVal::CtxHeap(never) => match *never {},
    }
}

/// Heap-fetch for resource bodies. `CtxHeap(())` resolves to the
/// precondition heap delta (panics if accessed outside a resource with a
/// `requires`).
fn get_heap_resource(state: &EvalState, hv: &ResourceHeapVal) -> Heap {
    match hv {
        HeapVal::Empty => Heap::empty(),
        HeapVal::Temp(n) => state.heaps[*n].clone(),
        HeapVal::CtxHeap(()) => state
            .pre_heap
            .clone()
            .expect("HeapVal::CtxHeap outside resource-body with requires"),
    }
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

/// Evaluate a `PureInst<X>` given a context-specific heap-fetch.
fn eval_pure_inst<X, F>(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    pi: &PureInst<X>,
    get_heap: F,
) -> egg::Id
where
    F: Fn(&EvalState, &HeapVal<X>) -> Heap,
{
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
            let heap = get_heap(state, hv);
            let addr = state.get_val(ctx, loc);
            heap.value_at(addr).unwrap_or_else(|| ctx.fresh_symbolic_value("deref"))
        }
        PureInst::Perm(hv, loc) => {
            let heap = get_heap(state, hv);
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

/// Re-key a heap's chunks under the egraph's current canonical ids. When
/// two source addresses collapse to the same canonical id, merge their
/// chunks: sum perms via a `Plus` e-node and union their values.
fn canonicalize_heap(ctx: &mut VerifyContext<'_>, h: &Heap) -> Heap {
    let mut out = Heap::empty();
    let entries: Vec<(egg::Id, Chunk)> =
        h.entries().map(|(addr, chunk)| (addr, chunk.clone())).collect();
    for (addr, chunk) in entries {
        let canon = ctx.egraph.find(addr);
        if let Some(existing) = out.chunk(canon).cloned() {
            let perm = ctx.add(Symbolic::Binary(BinOp::Plus, [existing.perm, chunk.perm]));
            ctx.egraph.union(existing.value, chunk.value);
            out = out.with_chunk(canon, Chunk::new(perm, existing.value));
        } else {
            out = out.with_chunk(canon, chunk);
        }
    }
    out
}

/// Heap addition. Canonicalises both inputs first so chunks at e-class
/// equivalent addresses merge. On collision, perms are summed and values
/// are unioned in the egraph.
fn heap_union(ctx: &mut VerifyContext<'_>, h1: &Heap, h2: &Heap) -> Heap {
    let c1 = canonicalize_heap(ctx, h1);
    let c2 = canonicalize_heap(ctx, h2);
    let mut out = c1;
    let entries: Vec<(egg::Id, Chunk)> =
        c2.entries().map(|(addr, chunk)| (addr, chunk.clone())).collect();
    for (addr, chunk2) in entries {
        if let Some(existing) = out.chunk(addr).cloned() {
            let perm = ctx.add(Symbolic::Binary(BinOp::Plus, [existing.perm, chunk2.perm]));
            ctx.egraph.union(existing.value, chunk2.value);
            out = out.with_chunk(addr, Chunk::new(perm, existing.value));
        } else {
            out = out.with_chunk(addr, chunk2);
        }
    }
    out
}

/// Heap subtraction. Canonicalises both inputs first. Each canonical addr
/// of `h2` must be present in `h1`; perms are subtracted, values unioned.
fn heap_subtract(
    ctx: &mut VerifyContext<'_>,
    h1: &Heap,
    h2: &Heap,
) -> Result<Heap, VerifyError> {
    let c1 = canonicalize_heap(ctx, h1);
    let c2 = canonicalize_heap(ctx, h2);
    let mut out = c1;
    let entries: Vec<(egg::Id, Chunk)> =
        c2.entries().map(|(addr, chunk)| (addr, chunk.clone())).collect();
    for (addr, chunk2) in entries {
        let Some(existing) = out.chunk(addr).cloned() else {
            return Err(VerifyError::InsufficientPermission);
        };
        let perm = ctx.add(Symbolic::Binary(BinOp::Minus, [existing.perm, chunk2.perm]));
        ctx.egraph.union(existing.value, chunk2.value);
        out = out.with_chunk(addr, Chunk::new(perm, existing.value));
    }
    Ok(out)
}

fn eval_resource_heap_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    inst: &HeapInst<!, ()>,
) -> Heap {
    match inst {
        HeapInst::Acc(acc) => heap_acc(ctx, acc, state),
        HeapInst::Add(h1, h2) => {
            let l = get_heap_resource(state, h1);
            let r = get_heap_resource(state, h2);
            heap_union(ctx, &l, &r)
        }
        // TODO: condition-aware merge. Currently picks the then branch.
        HeapInst::Ternary(_cond, h1, _h2) => get_heap_resource(state, h1),
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
            let id = eval_pure_inst(ctx, state, pi, get_heap_resource);
            state.push_val(id);
        }
        InstKind::Heap(hi) => {
            let heap = eval_resource_heap_inst(ctx, state, hi);
            state.push_heap(heap);
        }
        InstKind::Ext(never) => match *never {},
    }
}

/// Evaluate a resource invocation as a **reusable proof**.
///
/// Contract: all of the body's structural facts (fresh values, chunk
/// presences, value identities, the precondition's boolean) are added
/// unconditionally to the caller's egraph. The function returns
/// `(heap_delta, bool_handle)`. The *outer* boolean is **not** assumed or
/// asserted inside this function — the caller decides whether to
/// `egraph.union(bool_handle, true_id)` (inhale) or
/// `egraph.rebuild(); assert find(bool_handle) == find(true_id)` (exhale).
///
/// The precondition (if `r.requires.is_some()`) is handled inside the body
/// because the design spec says "precondition's boolean is assumed inside
/// this body" (CLAUDE.md). That is a body-internal convention and is
/// distinct from how the *outer* boolean is treated.
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

    // Inner precondition: body-internal "assumed inside this body" per
    // CLAUDE.md. Stashing pre_heap makes HeapVal::CtxHeap(()) operands
    // resolve; unioning pre_bool with `true_` realises the assume.
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

    let result_heap = get_heap_resource(&res_state, &body.res.0);
    let result_bool = res_state.get_val(ctx, &body.res.1);
    Ok((result_heap, result_bool))
}

fn eval_method_heap_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    inst: &HeapInst<MethodHeapExt, !>,
) -> Result<Heap, VerifyError> {
    match inst {
        HeapInst::Acc(acc) => Ok(heap_acc(ctx, acc, state)),
        HeapInst::Add(h1, h2) => {
            let l = get_heap_method(state, h1);
            let r = get_heap_method(state, h2);
            Ok(heap_union(ctx, &l, &r))
        }
        // TODO: condition-aware merge. Currently picks the then branch.
        HeapInst::Ternary(_cond, h1, _h2) => Ok(get_heap_method(state, h1)),
        HeapInst::Ext(MethodHeapExt::Sub(h1, h2)) => {
            let l = get_heap_method(state, h1);
            let r = get_heap_method(state, h2);
            heap_subtract(ctx, &l, &r)
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
            let id = eval_pure_inst(ctx, state, pi, get_heap_method);
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
    _method_name: &str,
    method: &Method,
) -> Result<(), VerifyError> {
    let mut ctx = VerifyContext::new(&program.interner);
    let mut state = EvalState::new();

    for inst in &method.insts {
        eval_method_inst(&mut ctx, program, &mut state, inst)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::lang::Symbolic;

    fn fresh_ctx<'a>(interner: &'a lasso::Rodeo<vmir::MemberId>) -> VerifyContext<'a> {
        VerifyContext::new(interner)
    }

    #[test]
    fn heap_union_merges_egg_equivalent_addresses() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        // Two distinct addr e-nodes that we'll later union.
        let a = ctx.add(Symbolic::Fresh(egg::Symbol::from("a")));
        let b = ctx.add(Symbolic::Fresh(egg::Symbol::from("b")));
        let p1 = ctx.add(Symbolic::Real(num::BigInt::from(1).into()));
        let p2 = ctx.add(Symbolic::Real(num::BigInt::from(2).into()));
        let v1 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v1")));
        let v2 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v2")));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let h2 = Heap::empty().with_chunk(b, Chunk::new(p2, v2));

        // Make a and b e-class equivalent.
        ctx.egraph.union(a, b);
        ctx.egraph.rebuild();

        let merged = heap_union(&mut ctx, &h1, &h2);

        // After canonicalisation both chunks live under a single key.
        let canon = ctx.egraph.find(a);
        let chunk = merged.chunk(canon).expect("merged chunk missing");

        // Perm should be the e-node `p1 + p2`.
        let expected_perm =
            ctx.add(Symbolic::Binary(BinOp::Plus, [p1, p2]));
        ctx.egraph.rebuild();
        assert_eq!(ctx.egraph.find(chunk.perm), ctx.egraph.find(expected_perm));

        // v1 and v2 should now be in the same e-class.
        assert_eq!(ctx.egraph.find(v1), ctx.egraph.find(v2));

        // And only one chunk in the merged heap.
        assert_eq!(merged.entries().count(), 1);
    }

    #[test]
    fn heap_subtract_canonical_match() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(egg::Symbol::from("a")));
        let b = ctx.add(Symbolic::Fresh(egg::Symbol::from("b")));
        let p1 = ctx.add(Symbolic::Real(num::BigInt::from(1).into()));
        let p2 = ctx.add(Symbolic::Real(num::BigInt::from(2).into()));
        let v1 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v1")));
        let v2 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v2")));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let h2 = Heap::empty().with_chunk(b, Chunk::new(p2, v2));

        ctx.egraph.union(a, b);
        ctx.egraph.rebuild();

        let result = heap_subtract(&mut ctx, &h1, &h2).expect("subtract should succeed");

        let canon = ctx.egraph.find(a);
        let chunk = result.chunk(canon).expect("result chunk missing");
        let expected_perm =
            ctx.add(Symbolic::Binary(BinOp::Minus, [p1, p2]));
        ctx.egraph.rebuild();
        assert_eq!(ctx.egraph.find(chunk.perm), ctx.egraph.find(expected_perm));
    }

    #[test]
    fn heap_subtract_missing_addr_fails() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(egg::Symbol::from("a")));
        let b = ctx.add(Symbolic::Fresh(egg::Symbol::from("b")));
        let p1 = ctx.add(Symbolic::Real(num::BigInt::from(1).into()));
        let v1 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v1")));

        let h1 = Heap::empty();
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        // a and b are *not* unioned.
        let _ = b;

        let err = heap_subtract(&mut ctx, &h1, &h2)
            .err()
            .expect("subtract from empty must fail");
        assert!(matches!(err, VerifyError::InsufficientPermission));
    }
}
