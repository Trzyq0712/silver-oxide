use crate::{
    verify::{
        context::VerifyContext,
        heap::{Chunk, Heap},
        lang::Symbolic,
    },
    vmir::{
        self, Acc, Assign, BinOp, Declaration, HeapExt, HeapInst, HeapVal, InstExt, InstKind,
        Literal, Method, MethodInst, PathConds, Polarity, PureInst, ResourceCall, ResourceInst,
        Type, Val,
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
}

impl EvalState {
    fn new() -> Self {
        Self {
            vals: Vec::new(),
            heaps: Vec::new(),
        }
    }

    fn with_args(args: Vec<egg::Id>) -> Self {
        Self {
            vals: args,
            heaps: Vec::new(),
        }
    }

    fn get_val(&self, ctx: &mut VerifyContext<'_>, val: &Val) -> egg::Id {
        match val {
            Val::Temp(n) => self.vals[*n],
            Val::Literal(lit) => ctx.add(Symbolic::Lit(lit.clone())),
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
/// caller-supplied ctx heap of a resource body lives at
/// `state.heaps[0]` by convention (mirroring how params occupy the
/// initial `vals` slots).
fn get_heap(state: &EvalState, hv: &HeapVal) -> Heap {
    match hv {
        HeapVal::Empty => Heap::empty(),
        HeapVal::Temp(n) => state.heaps[*n].clone(),
    }
}

fn zero_real(ctx: &mut VerifyContext<'_>) -> egg::Id {
    ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())))
}

/// Best-effort literal extraction: scan the e-class for a real literal
/// node. Returns the first one found. Used by heap arithmetic to fold
/// concrete-perm operations and detect zero/negative permission.
fn extract_real_literal(ctx: &VerifyContext<'_>, id: egg::Id) -> Option<num::BigRational> {
    let canon = ctx.egraph.find(id);
    for node in &ctx.egraph[canon].nodes {
        if let Symbolic::Lit(Literal::Real(r)) = node {
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
    ty: &Type,
    pi: &PureInst<P>,
    eval_ext: F,
) -> egg::Id
where
    F: FnOnce(&mut VerifyContext<'_>, &EvalState, &P) -> egg::Id,
{
    match pi {
        PureInst::Fresh => ctx.fresh_symbolic_value(ty.clone()),
        PureInst::Binary(op, l, r) => {
            let lhs = state.get_val(ctx, l);
            let rhs = state.get_val(ctx, r);
            ctx.add(Symbolic::Binary(*op, ty.clone(), [lhs, rhs]))
        }
        PureInst::Ternary(c, t, e) => {
            let cond = state.get_val(ctx, c);
            let then_ = state.get_val(ctx, t);
            let else_ = state.get_val(ctx, e);
            ctx.add(Symbolic::Ite(ty.clone(), [cond, then_, else_]))
        }
        PureInst::Deref(hv, loc) => {
            let heap = get_heap(state, hv);
            let addr = state.get_val(ctx, loc);
            heap.value_at(addr)
                .unwrap_or_else(|| ctx.fresh_symbolic_value(ty.clone()))
        }
        PureInst::FunctionCall(_heap, fc) => {
            let args: Vec<egg::Id> = fc.args.iter().map(|v| state.get_val(ctx, v)).collect();
            ctx.add(Symbolic::FuncApp(fc.function, ty.clone(), args.into()))
        }
        PureInst::Ext(ext) => eval_ext(ctx, state, ext),
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
    // TODO: thread the snapshot's actual value type once `Acc` carries it.
    let value = ctx.fresh_symbolic_value(Type::Int);
    Heap::empty().with_chunk(addr, Chunk::new(perm, value))
}

/// Merge two fractional chunks at the same address. Decouples the operational
/// value pick from the declarative agreement axiom: `perm = p0 + p1`,
/// `value = (p0 > 0) ? v0 : v1` (intentionally asymmetric), and an assumed
/// `(p0 > 0 && p1 > 0) ==> (v0 == v1)`.
///
/// The assume is emitted by unioning the (desugared) implication with `true`;
/// it is not an eager `union(v0, v1)`. When both fractions are positive,
/// saturation folds the antecedent, collapses the implication to `v0 == v1`,
/// and `eq-true-union` fuses the values — erasing the ternary's asymmetry by
/// congruence. When a fraction is zero, the antecedent is `false` and the
/// asymmetric pick selects the genuinely-held value. `BinOp` has no `>`/`&&`/
/// `==>`, so these desugar to `Lt(0, p)` and `Ite` forms.
fn merge_chunks(
    ctx: &mut VerifyContext<'_>,
    p0: egg::Id,
    v0: egg::Id,
    p1: egg::Id,
    v1: egg::Id,
    pc_lits: &[(egg::Id, Polarity)],
) -> Chunk {
    let perm = ctx.add(Symbolic::Binary(BinOp::Plus, Type::Real, [p0, p1]));

    let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigRational::from(
        num::BigInt::from(0),
    ))));
    let p0_pos = ctx.add(Symbolic::Binary(BinOp::Lt, Type::Bool, [zero, p0]));
    let p1_pos = ctx.add(Symbolic::Binary(BinOp::Lt, Type::Bool, [zero, p1]));

    let vty = ctx.egraph[v0].data.ty.clone();
    let value = ctx.add(Symbolic::Ite(vty, [p0_pos, v0, v1]));

    // `(PC ∧ p0 > 0 ∧ p1 > 0) ==> (v0 == v1)` as the golden-rule ITE chain.
    // Fold innermost-first: p1_pos, p0_pos, then PC literals in reverse.
    let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
    let eq = ctx.add(Symbolic::Binary(BinOp::Eq, Type::Bool, [v0, v1]));
    let antecedents = [(p1_pos, Polarity::Positive), (p0_pos, Polarity::Positive)]
        .into_iter()
        .chain(pc_lits.iter().rev().copied());
    let imp = ctx.implication(eq, antecedents);
    ctx.egraph.union(imp, true_);

    Chunk::new(perm, value)
}

/// Re-key a heap's chunks under the egraph's current canonical ids. When
/// two source addresses collapse to the same canonical id, merge their
/// chunks via [`merge_chunks`].
fn canonicalize_heap(
    ctx: &mut VerifyContext<'_>,
    h: &Heap,
    pc_lits: &[(egg::Id, Polarity)],
) -> Heap {
    let mut out = Heap::empty();
    let entries: Vec<(egg::Id, Chunk)> = h
        .entries()
        .map(|(addr, chunk)| (addr, chunk.clone()))
        .collect();
    for (addr, chunk) in entries {
        let canon = ctx.egraph.find(addr);
        if let Some(existing) = out.chunk(canon).cloned() {
            let merged = merge_chunks(
                ctx, existing.perm, existing.value, chunk.perm, chunk.value, pc_lits,
            );
            out = out.with_chunk(canon, merged);
        } else {
            out = out.with_chunk(canon, chunk);
        }
    }
    out
}

/// Heap addition. Canonicalises both inputs first so chunks at e-class
/// equivalent addresses merge. On collision, chunks merge via [`merge_chunks`].
fn heap_union(
    ctx: &mut VerifyContext<'_>,
    h1: &Heap,
    h2: &Heap,
    pc_lits: &[(egg::Id, Polarity)],
) -> Heap {
    let c1 = canonicalize_heap(ctx, h1, pc_lits);
    let c2 = canonicalize_heap(ctx, h2, pc_lits);
    let mut out = c1;
    let entries: Vec<(egg::Id, Chunk)> = c2
        .entries()
        .map(|(addr, chunk)| (addr, chunk.clone()))
        .collect();
    for (addr, chunk2) in entries {
        if let Some(existing) = out.chunk(addr).cloned() {
            let merged = merge_chunks(
                ctx, existing.perm, existing.value, chunk2.perm, chunk2.value, pc_lits,
            );
            out = out.with_chunk(addr, merged);
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
fn heap_subtract(
    ctx: &mut VerifyContext<'_>,
    h1: &Heap,
    h2: &Heap,
    pc_lits: &[(egg::Id, Polarity)],
) -> Result<Heap, VerifyError> {
    let c1 = canonicalize_heap(ctx, h1, &[]);
    let c2 = canonicalize_heap(ctx, h2, &[]);
    let mut out = c1;
    let entries: Vec<(egg::Id, Chunk)> = c2
        .entries()
        .map(|(addr, chunk)| (addr, chunk.clone()))
        .collect();
    let zero_rat = num::BigRational::from(num::BigInt::from(0));
    for (addr, chunk2) in entries {
        let Some(existing) = out.chunk(addr).cloned() else {
            return Err(VerifyError::InsufficientPermission);
        };

        // Sufficiency goal: `existing.perm >= chunk2.perm`, i.e.
        // `not(existing.perm < chunk2.perm)`, desugared to an `Ite`.
        let lt = ctx.add(Symbolic::Binary(
            BinOp::Lt,
            Type::Bool,
            [existing.perm, chunk2.perm],
        ));
        let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        let goal = ctx.add(Symbolic::Ite(Type::Bool, [lt, false_, true_]));
        if !ctx.prove_under_pc(goal, pc_lits) {
            return Err(VerifyError::InsufficientPermission);
        }

        ctx.egraph.union(existing.value, chunk2.value);

        let remainder = ctx.add(Symbolic::Binary(
            BinOp::Minus,
            Type::Real,
            [existing.perm, chunk2.perm],
        ));
        if extract_real_literal(ctx, remainder).as_ref() == Some(&zero_rat) {
            out = out.without_chunk(addr);
        } else {
            out = out.with_chunk(addr, Chunk::new(remainder, existing.value));
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
    pc: &PathConds,
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
            let pc_lits: Vec<(egg::Id, Polarity)> = pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            Ok(heap_union(ctx, &l, &r, &pc_lits))
        }
        HeapInst::Sub(h1, h2) => {
            let l = get_heap(state, h1);
            let r = get_heap(state, h2);
            let pc_lits: Vec<(egg::Id, Polarity)> = pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            heap_subtract(ctx, &l, &r, &pc_lits)
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
        InstKind::Pure(ty, pi) => {
            let id = eval_pure_inst(ctx, state, ty, pi, |_, _, never| match *never {});
            state.push_val(id);
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, &inst.pc, |_, _, never| match *never {})?;
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

    // Caller-supplied ctx heap occupies the body's `HeapVal::Temp(0)`
    // slot, mirroring how params occupy `Val::Temp(0..n_params)`.
    res_state.push_heap(get_heap(caller_state, &call.ctx_heap));

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
        InstKind::Pure(ty, pi) => {
            let id = eval_pure_inst(ctx, state, ty, pi, eval_method_pure_ext);
            state.push_val(id);
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, &inst.pc, eval_method_heap_ext)?;
            state.push_heap(heap);
        }
        InstKind::Ext(ext) => match ext {
            InstExt::Assume(val) => {
                let id = state.get_val(ctx, val);
                let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
                ctx.egraph.union(id, true_);
                ctx.egraph.rebuild();
            }
            InstExt::Assert(val) => {
                let id = state.get_val(ctx, val);
                let pc_lits: Vec<(egg::Id, Polarity)> = inst
                    .pc
                    .conds
                    .iter()
                    .map(|(v, p)| (state.get_val(ctx, v), *p))
                    .collect();
                if !ctx.prove_under_pc(id, &pc_lits) {
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
    use crate::translate;
    use crate::verify::lang::Symbolic;
    use crate::viper::{
        GlobalsCollector, IdentCollector, disambiguate, inline_macros, typecheck_program,
        viper_parser, walk::AstWalkable,
    };

    fn fresh_ctx<'a>(interner: &'a lasso::Rodeo<vmir::MemberId>) -> VerifyContext<'a> {
        VerifyContext::new(interner)
    }

    fn lower(input: &str) -> vmir::Program {
        let mut program = viper_parser::vpr_program(input).expect("parse");
        let mut ic = IdentCollector::default();
        program.walk_mut(&mut ic);
        let interner = ic.finalize();
        let mut gc = GlobalsCollector::new(&interner);
        program.walk(&mut gc);
        let globals = gc.finalize().expect("globals");
        disambiguate(&mut program, &interner, &globals).expect("disambiguation");
        inline_macros(&mut program, &interner).expect("macros");
        let typed = typecheck_program(&mut program, &interner, &globals).expect("typecheck");
        translate::translate(&typed, &interner, &globals).expect("translate")
    }

    #[test]
    fn heap_union_merges_egg_equivalent_addresses() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Ref));
        let b = ctx.add(Symbolic::Fresh(1, Type::Ref));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let v1 = ctx.add(Symbolic::Fresh(2, Type::Int));
        let v2 = ctx.add(Symbolic::Fresh(3, Type::Int));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let h2 = Heap::empty().with_chunk(b, Chunk::new(p2, v2));

        ctx.egraph.union(a, b);
        ctx.egraph.rebuild();

        let merged = heap_union(&mut ctx, &h1, &h2, &[]);

        let canon = ctx.egraph.find(a);
        let chunk = merged.chunk(canon).expect("merged chunk missing");

        let expected_perm = ctx.add(Symbolic::Binary(BinOp::Plus, Type::Real, [p1, p2]));
        ctx.saturate();
        assert_eq!(ctx.egraph.find(chunk.perm), ctx.egraph.find(expected_perm));
        // Both fractions positive (1, 2) → agreement axiom fuses the values.
        assert_eq!(ctx.egraph.find(v1), ctx.egraph.find(v2));
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v1));
        assert_eq!(merged.entries().count(), 1);
    }

    #[test]
    fn merge_zero_fraction_picks_active_value() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Ref));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1, Type::Int));
        let v1 = ctx.add(Symbolic::Fresh(2, Type::Int));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p0, v0));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));

        let merged = heap_union(&mut ctx, &h1, &h2, &[]);
        let chunk = merged.chunk(ctx.egraph.find(a)).expect("merged chunk missing");
        ctx.saturate();

        // p0 = 0 → asymmetric ternary picks the active half v1; no fusion.
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v1));
        assert_ne!(ctx.egraph.find(v0), ctx.egraph.find(v1));
    }

    #[test]
    fn merge_both_active_fuses_values() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Ref));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1, Type::Int));
        let v1 = ctx.add(Symbolic::Fresh(2, Type::Int));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p0, v0));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));

        let merged = heap_union(&mut ctx, &h1, &h2, &[]);
        let chunk = merged.chunk(ctx.egraph.find(a)).expect("merged chunk missing");
        ctx.saturate();

        // Both fractions positive → agreement axiom fuses the symbolic values.
        assert_eq!(ctx.egraph.find(v0), ctx.egraph.find(v1));
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v0));
    }

    #[test]
    fn merge_under_false_pc_blocks_fusion() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Ref));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1, Type::Int));
        let v1 = ctx.add(Symbolic::Fresh(2, Type::Int));
        let false_lit = ctx.add(Symbolic::Lit(Literal::Bool(false)));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p0, v0));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));

        let merged = heap_union(&mut ctx, &h1, &h2, &[(false_lit, Polarity::Positive)]);
        let chunk = merged.chunk(ctx.egraph.find(a)).expect("merged chunk missing");
        ctx.saturate();

        // PC literal is `false` → implication collapses to its `true` fallback;
        // values must NOT fuse even though both fractions are positive.
        assert_ne!(ctx.egraph.find(v0), ctx.egraph.find(v1));
        // Value pick is independent of the PC gate.
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v0));
    }

    #[test]
    fn merge_under_true_pc_allows_fusion() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Ref));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1, Type::Int));
        let v1 = ctx.add(Symbolic::Fresh(2, Type::Int));
        let true_lit = ctx.add(Symbolic::Lit(Literal::Bool(true)));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p0, v0));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));

        let merged = heap_union(&mut ctx, &h1, &h2, &[(true_lit, Polarity::Positive)]);
        let _chunk = merged.chunk(ctx.egraph.find(a)).expect("merged chunk missing");
        ctx.saturate();

        // PC literal is `true` + both fractions positive → agreement fires.
        assert_eq!(ctx.egraph.find(v0), ctx.egraph.find(v1));
    }

    #[test]
    fn prove_under_empty_pc_proves_known_goal() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let g = ctx.add(Symbolic::Fresh(0, Type::Bool));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        ctx.egraph.union(g, true_);
        ctx.egraph.rebuild();

        // Goal already in the `true` eclass → proven under the empty PC.
        assert!(ctx.prove_under_pc(g, &[]));
    }

    #[test]
    fn prove_unknown_goal_fails() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        // A free boolean never driven to `true` is not provable.
        let g = ctx.add(Symbolic::Fresh(0, Type::Bool));
        assert!(!ctx.prove_under_pc(g, &[]));
    }

    #[test]
    fn prove_under_false_pc_is_vacuous() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        // Unprovable goal, but the path is unsatisfiable (`false`).
        let g = ctx.add(Symbolic::Fresh(0, Type::Bool));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        let false_lit = ctx.add(Symbolic::Lit(Literal::Bool(false)));

        assert!(ctx.prove_under_pc(g, &[(false_lit, Polarity::Positive)]));
        // The vacuous proof must NOT fuse the goal into `true` unconditionally.
        ctx.saturate();
        assert_ne!(ctx.egraph.find(g), ctx.egraph.find(true_));
    }

    #[test]
    fn prove_commits_conditional_implication() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let c = ctx.add(Symbolic::Fresh(0, Type::Bool));
        let x = ctx.add(Symbolic::Fresh(1, Type::Bool));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        // goal = `c ? true : x` — true under hypothesis `c`, unknown otherwise.
        let goal = ctx.add(Symbolic::Ite(Type::Bool, [c, true_, x]));

        // Provable under PC `<c>`; commits `c ==> goal` into the live graph.
        assert!(ctx.prove_under_pc(goal, &[(c, Polarity::Positive)]));

        // Not leaked unconditionally: `c` still unknown ⇒ goal not yet true.
        ctx.saturate();
        assert_ne!(ctx.egraph.find(goal), ctx.egraph.find(true_));

        // Once `c` is established, the goal collapses to `true`.
        ctx.egraph.union(c, true_);
        ctx.saturate();
        assert_eq!(ctx.egraph.find(goal), ctx.egraph.find(true_));
    }

    #[test]
    fn subtract_symbolic_perm_fails_without_proof() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Ref));
        let p_have = ctx.add(Symbolic::Fresh(1, Type::Real));
        let p_take = ctx.add(Symbolic::Fresh(2, Type::Real));
        let v1 = ctx.add(Symbolic::Fresh(3, Type::Int));
        let v2 = ctx.add(Symbolic::Fresh(4, Type::Int));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p_have, v1));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p_take, v2));

        // Symbolic perms → `have >= take` not provable by equality saturation.
        let err = heap_subtract(&mut ctx, &h1, &h2, &[])
            .err()
            .expect("symbolic-perm exhale must fail without a proof");
        assert!(matches!(err, VerifyError::InsufficientPermission));
    }

    #[test]
    fn heap_subtract_canonical_match() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Ref));
        let b = ctx.add(Symbolic::Fresh(1, Type::Ref));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2, Type::Int));
        let v2 = ctx.add(Symbolic::Fresh(3, Type::Int));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p2, v1));
        let h2 = Heap::empty().with_chunk(b, Chunk::new(p1, v2));

        ctx.egraph.union(a, b);
        ctx.egraph.rebuild();

        let result = heap_subtract(&mut ctx, &h1, &h2, &[]).expect("subtract should succeed");

        let canon = ctx.egraph.find(a);
        let chunk = result.chunk(canon).expect("result chunk missing");
        let expected_perm = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        ctx.egraph.rebuild();
        assert_eq!(ctx.egraph.find(chunk.perm), ctx.egraph.find(expected_perm));
        assert_eq!(ctx.egraph.find(v1), ctx.egraph.find(v2));
    }

    #[test]
    fn heap_subtract_exact_match_drops_chunk() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Ref));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2, Type::Int));
        let v2 = ctx.add(Symbolic::Fresh(3, Type::Int));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v2));

        let result = heap_subtract(&mut ctx, &h1, &h2, &[]).expect("subtract should succeed");

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

        let a = ctx.add(Symbolic::Fresh(0, Type::Ref));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let v1 = ctx.add(Symbolic::Fresh(2, Type::Int));
        let v2 = ctx.add(Symbolic::Fresh(3, Type::Int));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p2, v2));

        let err = heap_subtract(&mut ctx, &h1, &h2, &[])
            .err()
            .expect("over-consumption must fail");
        assert!(matches!(err, VerifyError::InsufficientPermission));
    }

    #[test]
    fn heap_subtract_missing_addr_fails() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Ref));
        let b = ctx.add(Symbolic::Fresh(1, Type::Ref));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2, Type::Int));

        let h1 = Heap::empty();
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let _ = b;

        let err = heap_subtract(&mut ctx, &h1, &h2, &[])
            .err()
            .expect("subtract from empty must fail");
        assert!(matches!(err, VerifyError::InsufficientPermission));
    }

    #[test]
    fn const_fold_folds_subtraction() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let one = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let diff = ctx.add(Symbolic::Binary(BinOp::Minus, Type::Real, [one, one]));
        ctx.egraph.rebuild();

        let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        assert_eq!(ctx.egraph.find(diff), ctx.egraph.find(zero));
    }

    #[test]
    fn const_fold_folds_ternary() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let cond = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        let t = ctx.add(Symbolic::Fresh(0, Type::Int));
        let e = ctx.add(Symbolic::Fresh(1, Type::Int));
        let ite = ctx.add(Symbolic::Ite(Type::Int, [cond, t, e]));
        ctx.saturate();

        // `true ? t : e` collapses to the symbolic `t`.
        assert_eq!(ctx.egraph.find(ite), ctx.egraph.find(t));
        assert_ne!(ctx.egraph.find(ite), ctx.egraph.find(e));
    }

    #[test]
    fn rewrite_ite_false_picks_else() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let cond = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let t = ctx.add(Symbolic::Fresh(0, Type::Int));
        let e = ctx.add(Symbolic::Fresh(1, Type::Int));
        let ite = ctx.add(Symbolic::Ite(Type::Int, [cond, t, e]));
        ctx.saturate();

        assert_eq!(ctx.egraph.find(ite), ctx.egraph.find(e));
        assert_ne!(ctx.egraph.find(ite), ctx.egraph.find(t));
    }

    #[test]
    fn rewrite_add_zero_int() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let x = ctx.add(Symbolic::Fresh(0, Type::Int));
        let zero = ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(0))));
        let sum = ctx.add(Symbolic::Binary(BinOp::Plus, Type::Int, [x, zero]));
        ctx.saturate();

        assert_eq!(ctx.egraph.find(sum), ctx.egraph.find(x));
    }

    #[test]
    fn rewrite_add_zero_real_commuted() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let x = ctx.add(Symbolic::Fresh(0, Type::Real));
        let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        // `0 + x` (commuted) must also fold to `x`.
        let sum = ctx.add(Symbolic::Binary(BinOp::Plus, Type::Real, [zero, x]));
        ctx.saturate();

        assert_eq!(ctx.egraph.find(sum), ctx.egraph.find(x));
    }

    #[test]
    fn eq_true_unions_args() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Int));
        let b = ctx.add(Symbolic::Fresh(1, Type::Int));
        let eq = ctx.add(Symbolic::Binary(BinOp::Eq, Type::Bool, [a, b]));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        // `assume a == b` is modelled as unioning the equality with `true`.
        ctx.egraph.union(eq, true_);
        ctx.saturate();

        assert_eq!(ctx.egraph.find(a), ctx.egraph.find(b));
    }

    #[test]
    fn eq_unknown_does_not_union() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Int));
        let b = ctx.add(Symbolic::Fresh(1, Type::Int));
        // Build the equality but never prove it true.
        let _eq = ctx.add(Symbolic::Binary(BinOp::Eq, Type::Bool, [a, b]));
        ctx.saturate();

        assert_ne!(ctx.egraph.find(a), ctx.egraph.find(b));
    }

    #[test]
    fn eq_true_propagates_through_congruence() {
        let mut interner = lasso::Rodeo::<vmir::MemberId>::new();
        let f = interner.get_or_intern("f");
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0, Type::Int));
        let b = ctx.add(Symbolic::Fresh(1, Type::Int));
        let fa = ctx.add(Symbolic::FuncApp(f, Type::Int, Box::from([a])));
        let fb = ctx.add(Symbolic::FuncApp(f, Type::Int, Box::from([b])));
        let eq = ctx.add(Symbolic::Binary(BinOp::Eq, Type::Bool, [a, b]));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        ctx.egraph.union(eq, true_);
        ctx.saturate();

        // Unioning the args lets congruence close `f(a) == f(b)`.
        assert_eq!(ctx.egraph.find(fa), ctx.egraph.find(fb));
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
