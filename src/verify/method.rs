use crate::{
    verify::{
        context::VerifyContext,
        heap::{Chunk, Heap},
        lang::Symbolic,
    },
    vmir::{
        self, Acc, Assign, BinOp, Declaration, HeapExt, HeapInst, HeapVal, InstExt, InstKind,
        Literal, Method, MethodInst, PureInst, ResourceCall, ResourceInst, ResourcePureExt, Val,
    },
};

#[derive(Debug)]
pub enum VerifyError {
    AssertionFailed,
    InsufficientPermission,
    AbstractResourceCall,
    /// Encountered a method-only heap extension (e.g. `Assign`) in a body
    /// the verifier doesn't yet handle structurally. Reserved for
    /// not-yet-implemented variants.
    Unimplemented(&'static str),
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AssertionFailed => write!(f, "assertion failed"),
            Self::InsufficientPermission => write!(f, "insufficient permission"),
            Self::AbstractResourceCall => write!(f, "call to abstract resource"),
            Self::Unimplemented(what) => write!(f, "unimplemented: {what}"),
        }
    }
}

struct EvalState {
    vals: Vec<egg::Id>,
    heaps: Vec<Heap>,
    /// Set only inside a resource body whose owning `Resource` has a
    /// `requires`. Read by `ResourcePureExt::CtxDeref(addr)` operands.
    pre_heap: Option<Heap>,
}

impl EvalState {
    fn new() -> Self {
        Self {
            vals: Vec::new(),
            heaps: Vec::new(),
            pre_heap: None,
        }
    }

    fn with_args(args: Vec<egg::Id>) -> Self {
        Self {
            vals: args,
            heaps: Vec::new(),
            pre_heap: None,
        }
    }

    fn get_val(&self, ctx: &mut VerifyContext<'_>, val: &Val) -> egg::Id {
        match val {
            Val::Temp(n) => self.vals[*n],
            Val::Literal(lit) => ctx.add(lit_to_sym(lit)),
        }
    }

    fn push_val(&mut self, id: egg::Id) {
        self.vals.push(id);
    }
    fn push_heap(&mut self, heap: Heap) {
        self.heaps.push(heap);
    }
}

/// Heap-fetch is monomorphic — `HeapVal` carries no ctx-heap variant. The
/// precondition-heap concept lives in
/// `PureInst::Ext(ResourcePureExt::CtxDeref(_))`.
fn get_heap(state: &EvalState, hv: &HeapVal) -> Heap {
    match hv {
        HeapVal::Empty => Heap::empty(),
        HeapVal::Temp(n) => state.heaps[*n].clone(),
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

/// Best-effort literal extraction: scan the e-class for a `Symbolic::Real`
/// node. Returns the first one found. Used by heap arithmetic to fold
/// concrete-perm operations and detect zero/negative permission.
fn extract_real_literal(ctx: &VerifyContext<'_>, id: egg::Id) -> Option<num::BigRational> {
    let canon = ctx.egraph.find(id);
    for node in &ctx.egraph[canon].nodes {
        if let Symbolic::Real(r) = node {
            return Some(r.clone());
        }
    }
    None
}

/// Evaluate a `PureInst<P>`. The `Ext(P)` arm is delegated to a
/// context-specific evaluator (`eval_ext`); for `P = !` the closure is
/// uncallable, so the caller can pass `|_, _, never| match *never {}`.
fn eval_pure_inst<P, F>(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    pi: &PureInst<P>,
    eval_ext: F,
) -> egg::Id
where
    F: FnOnce(&mut VerifyContext<'_>, &EvalState, &P) -> egg::Id,
{
    match pi {
        PureInst::Fresh => ctx.fresh_symbolic_value("fresh"),
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
            heap.value_at(addr)
                .unwrap_or_else(|| ctx.fresh_symbolic_value("deref"))
        }
        PureInst::FunctionCall(_heap, fc) => {
            let args: Vec<egg::Id> = fc.args.iter().map(|v| state.get_val(ctx, v)).collect();
            ctx.add(Symbolic::FuncApp(fc.function, args.into()))
        }
        PureInst::Ext(ext) => eval_ext(ctx, state, ext),
    }
}

/// Pure-ext evaluator for resource bodies. Handles `CtxDeref(addr)`:
/// looks up `addr` in the precondition heap; falls back to fresh if
/// absent.
fn eval_resource_pure_ext(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    ext: &ResourcePureExt,
) -> egg::Id {
    match ext {
        ResourcePureExt::CtxDeref(addr) => {
            let addr_id = state.get_val(ctx, addr);
            let pre = state
                .pre_heap
                .as_ref()
                .expect("CtxDeref outside resource-body with requires");
            pre.value_at(addr_id)
                .unwrap_or_else(|| ctx.fresh_symbolic_value("ctx_deref"))
        }
        ResourcePureExt::CtxFunctionCall(call) => {
            let args: Vec<egg::Id> = call.args.iter().map(|v| state.get_val(ctx, v)).collect();
            ctx.add(Symbolic::FuncApp(call.function, args.into()))
        }
    }
}

/// Pure-ext evaluator for method bodies. Handles `PureExt::Perm`:
/// permission-amount query in the given heap.
fn eval_method_pure_ext(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    ext: &vmir::PureExt,
) -> egg::Id {
    match ext {
        vmir::PureExt::Perm(hv, loc) => {
            let heap = get_heap(state, hv);
            let addr = state.get_val(ctx, loc);
            heap.perm_at(addr).unwrap_or_else(|| zero_real(ctx))
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
    let entries: Vec<(egg::Id, Chunk)> = h
        .entries()
        .map(|(addr, chunk)| (addr, chunk.clone()))
        .collect();
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
    let entries: Vec<(egg::Id, Chunk)> = c2
        .entries()
        .map(|(addr, chunk)| (addr, chunk.clone()))
        .collect();
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
/// of `h2` must be present in `h1` with sufficient permission. When both
/// existing and subtracted perms are concrete `Real` literals, the
/// arithmetic is folded: negative result → `InsufficientPermission`, zero
/// → chunk dropped, positive → chunk kept with the literal remainder.
fn heap_subtract(ctx: &mut VerifyContext<'_>, h1: &Heap, h2: &Heap) -> Result<Heap, VerifyError> {
    let c1 = canonicalize_heap(ctx, h1);
    let c2 = canonicalize_heap(ctx, h2);
    let mut out = c1;
    let entries: Vec<(egg::Id, Chunk)> = c2
        .entries()
        .map(|(addr, chunk)| (addr, chunk.clone()))
        .collect();
    let zero = num::BigRational::from(num::BigInt::from(0));
    for (addr, chunk2) in entries {
        let Some(existing) = out.chunk(addr).cloned() else {
            return Err(VerifyError::InsufficientPermission);
        };
        match (
            extract_real_literal(ctx, existing.perm),
            extract_real_literal(ctx, chunk2.perm),
        ) {
            (Some(r1), Some(r2)) => {
                let diff = r1 - r2;
                if diff < zero {
                    return Err(VerifyError::InsufficientPermission);
                }
                ctx.egraph.union(existing.value, chunk2.value);
                if diff == zero {
                    out = out.without_chunk(addr);
                } else {
                    let perm = ctx.add(Symbolic::Real(diff));
                    out = out.with_chunk(addr, Chunk::new(perm, existing.value));
                }
            }
            _ => {
                let perm = ctx.add(Symbolic::Binary(BinOp::Minus, [existing.perm, chunk2.perm]));
                ctx.egraph.union(existing.value, chunk2.value);
                out = out.with_chunk(addr, Chunk::new(perm, existing.value));
            }
        }
    }
    Ok(out)
}

/// Evaluate a heap inst. `H` is the heap-ext slot; the `Ext(H)` arm is
/// delegated to `eval_heap_ext`. `Sub` may fail with
/// `InsufficientPermission`.
fn eval_heap_inst<H, F>(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    inst: &HeapInst<H>,
    eval_heap_ext: F,
) -> Result<Heap, VerifyError>
where
    F: FnOnce(&mut VerifyContext<'_>, &EvalState, &H) -> Result<Heap, VerifyError>,
{
    match inst {
        HeapInst::Acc(acc) => Ok(heap_acc(ctx, acc, state)),
        HeapInst::Add(h1, h2) => {
            let l = get_heap(state, h1);
            let r = get_heap(state, h2);
            Ok(heap_union(ctx, &l, &r))
        }
        HeapInst::Sub(h1, h2) => {
            let l = get_heap(state, h1);
            let r = get_heap(state, h2);
            heap_subtract(ctx, &l, &r)
        }
        // TODO: condition-aware merge. Currently picks the then branch.
        HeapInst::Ternary(_cond, h1, _h2) => Ok(get_heap(state, h1)),
        HeapInst::Ext(ext) => eval_heap_ext(ctx, state, ext),
    }
}

/// Heap-ext evaluator for method bodies. Currently `HeapExt::Assign` is
/// recognised but not implemented structurally — it returns an error.
fn eval_method_heap_ext(
    _ctx: &mut VerifyContext<'_>,
    _state: &EvalState,
    ext: &HeapExt,
) -> Result<Heap, VerifyError> {
    match ext {
        HeapExt::Assign(_heap, Assign { .. }) => Err(VerifyError::Unimplemented("HeapExt::Assign")),
    }
}

fn eval_resource_body_inst(
    ctx: &mut VerifyContext<'_>,
    state: &mut EvalState,
    inst: &ResourceInst,
) -> Result<(), VerifyError> {
    match &inst.kind {
        InstKind::Pure(_ty, pi) => {
            let id = eval_pure_inst(ctx, state, pi, eval_resource_pure_ext);
            state.push_val(id);
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, |_, _, never| match *never {})?;
            state.push_heap(heap);
        }
        InstKind::Ext(never) => match *never {},
    }
    Ok(())
}

/// Evaluate a resource invocation as a **reusable proof**.
///
/// Contract: all of the body's structural facts (fresh values, chunk
/// presences, value identities, the precondition's boolean) are added
/// unconditionally to the caller's egraph. Returns
/// `(heap_delta, bool_handle)`. The *outer* boolean is **not** assumed or
/// asserted here — the caller decides.
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

    let args: Vec<egg::Id> = call
        .args
        .iter()
        .map(|v| caller_state.get_val(ctx, v))
        .collect();

    let mut res_state = EvalState::with_args(args);

    // Caller-supplied ctx heap; readable inside the body via
    // `PureInst::Ext(CtxDeref(_))`.
    res_state.pre_heap = Some(get_heap(caller_state, &call.ctx_heap));

    for inst in &body.insts {
        eval_resource_body_inst(ctx, &mut res_state, inst)?;
    }

    let result_heap = get_heap(&res_state, &body.res.0);
    let result_bool = res_state.get_val(ctx, &body.res.1);
    Ok((result_heap, result_bool))
}

fn eval_method_inst(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    inst: &MethodInst,
) -> Result<(), VerifyError> {
    match &inst.kind {
        InstKind::Pure(_ty, pi) => {
            let id = eval_pure_inst(ctx, state, pi, eval_method_pure_ext);
            state.push_val(id);
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, eval_method_heap_ext)?;
            state.push_heap(heap);
        }
        InstKind::Ext(ext) => match ext {
            InstExt::Assume(val) => {
                let id = state.get_val(ctx, val);
                let true_ = ctx.add(Symbolic::Bool(true));
                ctx.egraph.union(id, true_);
            }
            InstExt::Assert(val) => {
                let id = state.get_val(ctx, val);
                ctx.egraph.rebuild();
                let true_ = ctx.add(Symbolic::Bool(true));
                if ctx.egraph.find(id) != ctx.egraph.find(true_) {
                    return Err(VerifyError::AssertionFailed);
                }
            }
            InstExt::ResourceCall(call) => {
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
    use crate::silver::{
        GlobalsCollector, IdentCollector, inline_macros, resolve_call_kinds, silver_parser,
        typecheck_program, walk::AstWalkable,
    };
    use crate::translate;
    use crate::verify::lang::Symbolic;

    fn fresh_ctx<'a>(interner: &'a lasso::Rodeo<vmir::MemberId>) -> VerifyContext<'a> {
        VerifyContext::new(interner)
    }

    fn lower(input: &str) -> vmir::Program {
        let mut program = silver_parser::sil_program(input).expect("parse");
        let mut ic = IdentCollector::default();
        program.walk_mut(&mut ic);
        let interner = ic.finalize();
        let mut gc = GlobalsCollector::new(&interner);
        program.walk(&mut gc);
        let globals = gc.finalize().expect("globals");
        resolve_call_kinds(&mut program, &interner, &globals).expect("call kinds");
        inline_macros(&mut program, &interner).expect("macros");
        let typed = typecheck_program(&mut program, &interner, &globals).expect("typecheck");
        translate::translate(&typed, &interner, &globals).expect("translate")
    }

    #[test]
    fn heap_union_merges_egg_equivalent_addresses() {
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

        let merged = heap_union(&mut ctx, &h1, &h2);

        let canon = ctx.egraph.find(a);
        let chunk = merged.chunk(canon).expect("merged chunk missing");

        let expected_perm = ctx.add(Symbolic::Binary(BinOp::Plus, [p1, p2]));
        ctx.egraph.rebuild();
        assert_eq!(ctx.egraph.find(chunk.perm), ctx.egraph.find(expected_perm));
        assert_eq!(ctx.egraph.find(v1), ctx.egraph.find(v2));
        assert_eq!(merged.entries().count(), 1);
    }

    #[test]
    fn heap_subtract_canonical_match() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(egg::Symbol::from("a")));
        let b = ctx.add(Symbolic::Fresh(egg::Symbol::from("b")));
        let p2 = ctx.add(Symbolic::Real(num::BigInt::from(2).into()));
        let p1 = ctx.add(Symbolic::Real(num::BigInt::from(1).into()));
        let v1 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v1")));
        let v2 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v2")));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p2, v1));
        let h2 = Heap::empty().with_chunk(b, Chunk::new(p1, v2));

        ctx.egraph.union(a, b);
        ctx.egraph.rebuild();

        let result = heap_subtract(&mut ctx, &h1, &h2).expect("subtract should succeed");

        let canon = ctx.egraph.find(a);
        let chunk = result.chunk(canon).expect("result chunk missing");
        let expected_perm = ctx.add(Symbolic::Real(num::BigInt::from(1).into()));
        ctx.egraph.rebuild();
        assert_eq!(ctx.egraph.find(chunk.perm), ctx.egraph.find(expected_perm));
        assert_eq!(ctx.egraph.find(v1), ctx.egraph.find(v2));
    }

    #[test]
    fn heap_subtract_exact_match_drops_chunk() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(egg::Symbol::from("a")));
        let p1 = ctx.add(Symbolic::Real(num::BigInt::from(1).into()));
        let v1 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v1")));
        let v2 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v2")));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v2));

        let result = heap_subtract(&mut ctx, &h1, &h2).expect("subtract should succeed");

        let canon = ctx.egraph.find(a);
        assert!(
            result.chunk(canon).is_none(),
            "zero-perm chunk must be dropped"
        );
    }

    #[test]
    fn heap_subtract_over_consume_fails() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(egg::Symbol::from("a")));
        let p1 = ctx.add(Symbolic::Real(num::BigInt::from(1).into()));
        let p2 = ctx.add(Symbolic::Real(num::BigInt::from(2).into()));
        let v1 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v1")));
        let v2 = ctx.add(Symbolic::Fresh(egg::Symbol::from("v2")));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p2, v2));

        let err = heap_subtract(&mut ctx, &h1, &h2)
            .err()
            .expect("over-consumption must fail");
        assert!(matches!(err, VerifyError::InsufficientPermission));
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
        let _ = b;

        let err = heap_subtract(&mut ctx, &h1, &h2)
            .err()
            .expect("subtract from empty must fail");
        assert!(matches!(err, VerifyError::InsufficientPermission));
    }

    #[test]
    fn const_fold_folds_subtraction() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let one = ctx.add(Symbolic::Real(num::BigInt::from(1).into()));
        let diff = ctx.add(Symbolic::Binary(BinOp::Minus, [one, one]));
        ctx.egraph.rebuild();

        let zero = ctx.add(Symbolic::Real(num::BigInt::from(0).into()));
        assert_eq!(ctx.egraph.find(diff), ctx.egraph.find(zero));
    }

    #[test]
    fn double_consume_predicate_should_fail() {
        let input = r#"
predicate number(this: Ref)

method consume(this: Ref)
    requires number(this)

method caller(this: Ref)
    requires number(this)
{
    consume(this)
    consume(this)
}
"#;
        let program = lower(input);
        let caller_id = program.interner.get("caller").expect("caller method");
        let vmir::Declaration::Method(caller) = &program.decls[caller_id] else {
            panic!("caller must be a Method");
        };
        let result = verify_method(&program, "caller", caller);
        assert!(
            matches!(result, Err(VerifyError::InsufficientPermission)),
            "expected InsufficientPermission, got {result:?}"
        );
    }
}
