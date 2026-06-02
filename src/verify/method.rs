use crate::{
    verify::{
        context::VerifyContext,
        heap::{Chunk, Heap},
        lang::Symbolic,
        viz::{self, Snapshotter},
    },
    vmir::{
        self, Acc, Assign, BinOp, Declaration, HeapExt, HeapInst, HeapVal, InstContext, InstExt,
        Inst, InstKind, Literal, MemberId, Method, MethodInst, PathConds, Polarity, PureInst, Resource,
        ResourceCall, ResourceInst, Type, Val,
    },
};
use crate::vmir::display::VmirDisplay;

#[derive(Debug)]
pub enum VerifyError {
    AssertionFailed,
    InsufficientPermission,
    AbstractResourceCall,
    /// A resource's side condition (e.g. `acc` permission ≥ 0, division divisor
    /// ≠ 0) could not be discharged. Carries a human-readable description.
    SideCondition(&'static str),
    /// Encountered a method-only heap extension (e.g. `Assign`) in a body
    /// the verifier doesn't yet handle structurally. Reserved for
    /// not-yet-implemented variants.
    Unimplemented(&'static str),
    /// Verification failed while executing a specific instruction.
    AtInst {
        inst: String,
        source: Box<VerifyError>,
    },
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AssertionFailed => write!(f, "assertion failed"),
            Self::InsufficientPermission => write!(f, "insufficient permission"),
            Self::AbstractResourceCall => write!(f, "call to abstract resource"),
            Self::SideCondition(what) => write!(f, "side condition may not hold: {what}"),
            Self::Unimplemented(what) => write!(f, "unimplemented: {what}"),
            Self::AtInst { inst, source } => write!(f, "{source}\n    instruction: {inst}"),
        }
    }
}

impl VerifyError {
    fn with_inst(self, inst: String) -> Self {
        match self {
            Self::AtInst { .. } => self,
            _ => Self::AtInst {
                inst,
                source: Box::new(self),
            },
        }
    }

    #[cfg(test)]
    fn root_cause(&self) -> &VerifyError {
        match self {
            Self::AtInst { source, .. } => source.root_cause(),
            _ => self,
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

/// Render a single instruction (method or resource body) for error context.
fn format_inst<C: InstContext>(
    inst: &Inst<C>,
    interner: &lasso::Rodeo<MemberId>,
    val_base: usize,
    heap_base: usize,
) -> String
where
    C::InstExt: vmir::Bumps,
    C::PureExt: vmir::PureExtRender,
    C::HeapExt: vmir::HeapExtRender,
    for<'a> VmirDisplay<'a, (usize, usize, &'a PathConds, &'a C::InstExt)>: std::fmt::Display,
{
    VmirDisplay::new((val_base, heap_base, std::slice::from_ref(inst)), interner)
        .to_string()
        .trim()
        .to_string()
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

fn collect_pc_lits(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    pc: &PathConds,
) -> Vec<(egg::Id, Polarity)> {
    pc.conds
        .iter()
        .map(|(v, p)| (state.get_val(ctx, v), *p))
        .collect()
}

fn check_deref_permission(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    pc_lits: &[(egg::Id, Polarity)],
    heap: &HeapVal,
    loc: &Val,
) -> Result<(), VerifyError> {
    let addr = state.get_val(ctx, loc);
    let perm = get_heap(state, heap)
        .perm_at(addr)
        .unwrap_or_else(|| zero_real(ctx));
    let zero = zero_real(ctx);
    let positive = ctx.add(Symbolic::Binary(BinOp::Lt, Type::Bool, [zero, perm]));
    if ctx.prove_under_pc(positive, pc_lits) {
        Ok(())
    } else {
        Err(VerifyError::InsufficientPermission)
    }
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
/// The resource was already verified self-contained (see [`verify_resource`]),
/// so this does **not** step the body for the user (no per-instruction
/// snapshots) nor re-discharge its side conditions. It re-evaluates the body
/// atomically into the caller's egraph to produce `(heap_delta, bool_handle)`
/// and to inject the knowledge it yields (chunk-merge equalities). The *outer*
/// boolean is **not** assumed or asserted here — the caller decides.
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
    method_name: &str,
    method: &Method,
) -> Result<(), VerifyError> {
    let mut ctx = VerifyContext::new(&program.interner);
    let mut state = EvalState::new();
    let mut snap = Snapshotter::from_env(method_name);

    snap.snapshot(&ctx, None, "init", None);
    for inst in &method.insts {
        let vals_before = state.vals.len();
        let heaps_before = state.heaps.len();
        let inst_text = format_inst(inst, &program.interner, vals_before, heaps_before);
        if let InstKind::Pure(_, PureInst::Deref(heap, loc)) = &inst.kind {
            let pc_lits = collect_pc_lits(&mut ctx, &state, &inst.pc);
            if let Err(err) = check_deref_permission(&mut ctx, &state, &pc_lits, heap, loc) {
                return Err(err.with_inst(inst_text.clone()));
            }
        }
        if let Err(err) = eval_method_inst(&mut ctx, program, &mut state, inst) {
            return Err(err.with_inst(inst_text));
        }
        let highlight = (state.vals.len() > vals_before).then(|| state.vals[state.vals.len() - 1]);
        let label = viz::method_inst_label(&inst.kind, ctx.interner);
        snap.snapshot(&ctx, state.heaps.last(), &label, highlight);
    }

    Ok(())
}

/// Verify a resource self-contained: run its body in a fresh egraph with fresh
/// symbolic params and a parametric (empty) ctx heap, discharging each
/// instruction's side-condition obligations under its path condition. Abstract
/// resources have nothing to check. This establishes well-formedness **once**;
/// method call sites reuse it without re-checking (see [`eval_resource_call`]).
pub fn verify_resource(
    program: &vmir::Program,
    resource_name: &str,
    resource: &Resource,
) -> Result<(), VerifyError> {
    let Some(body) = resource.body.as_ref() else {
        return Ok(());
    };

    let mut ctx = VerifyContext::new(&program.interner);
    let params: Vec<egg::Id> = resource
        .params
        .iter()
        .map(|ty| ctx.fresh_symbolic_value(ty.clone()))
        .collect();
    let mut state = EvalState::with_args(params);
    // Parametric ctx heap: an empty heap whose reads yield fresh symbolics.
    state.push_heap(Heap::empty());

    let mut snap = Snapshotter::from_env(resource_name);
    snap.snapshot(&ctx, None, "init", None);

    for inst in &body.insts {
        let vals_before = state.vals.len();
        let heaps_before = state.heaps.len();
        let inst_text = format_inst(inst, &program.interner, vals_before, heaps_before);
        let pc_lits = collect_pc_lits(&mut ctx, &state, &inst.pc);
        if let InstKind::Pure(_, PureInst::Deref(heap, loc)) = &inst.kind {
            if let Err(err) = check_deref_permission(&mut ctx, &state, &pc_lits, heap, loc) {
                return Err(err.with_inst(inst_text.clone()));
            }
        }
        for (goal, msg) in inst_obligations(&mut ctx, &state, &inst.kind) {
            if !ctx.prove_under_pc(goal, &pc_lits) {
                return Err(VerifyError::SideCondition(msg).with_inst(inst_text.clone()));
            }
        }

        if let Err(err) = eval_resource_body_inst(&mut ctx, &mut state, inst) {
            return Err(err.with_inst(inst_text));
        }
        let highlight = (state.vals.len() > vals_before).then(|| state.vals[state.vals.len() - 1]);
        let label = viz::resource_inst_label(&inst.kind);
        snap.snapshot(&ctx, state.heaps.last(), &label, highlight);
    }

    Ok(())
}

/// Side-condition obligations implied by an instruction's kind, as
/// `(goal, description)` pairs that must each be proven `true` under the
/// instruction's path condition. `acc` requires a non-negative permission;
/// division requires a non-zero divisor.
fn inst_obligations<C: InstContext>(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    kind: &InstKind<C>,
) -> Vec<(egg::Id, &'static str)> {
    let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
    let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
    match kind {
        // `not(perm < 0)` desugared to an `Ite`.
        InstKind::Heap(HeapInst::Acc(acc)) => {
            let perm = state.get_val(ctx, &acc.perm);
            let zero = zero_real(ctx);
            let lt = ctx.add(Symbolic::Binary(BinOp::Lt, Type::Bool, [perm, zero]));
            let goal = ctx.add(Symbolic::Ite(Type::Bool, [lt, false_, true_]));
            vec![(goal, "permission may be negative")]
        }
        // `not(divisor == 0)` desugared to an `Ite`.
        InstKind::Pure(_, PureInst::Binary(BinOp::Div, _, r)) => {
            let rv = state.get_val(ctx, r);
            let rty = ctx.egraph[rv].data.ty.clone();
            let zero = zero_of(ctx, &rty);
            let eq = ctx.add(Symbolic::Binary(BinOp::Eq, Type::Bool, [rv, zero]));
            let goal = ctx.add(Symbolic::Ite(Type::Bool, [eq, false_, true_]));
            vec![(goal, "divisor may be zero")]
        }
        _ => vec![],
    }
}

/// Zero literal of the given numeric type (`Real` fallback for non-numeric).
fn zero_of(ctx: &mut VerifyContext<'_>, ty: &Type) -> egg::Id {
    match ty {
        Type::Int => ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(0)))),
        _ => zero_real(ctx),
    }
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
        assert!(matches!(err.root_cause(), VerifyError::InsufficientPermission));
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
        assert!(matches!(err.root_cause(), VerifyError::InsufficientPermission));
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
        assert!(matches!(err.root_cause(), VerifyError::InsufficientPermission));
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
            matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
            "expected InsufficientPermission, got {result:?}"
        );
    }

    #[test]
    fn ensures_does_not_double_count_carried_permission() {
        // `read` requires AND ensures `number(this)`. The ensures delta must be
        // produced-only (perm 1), not accumulated onto the requires delta
        // (which would yield perm 2). Likewise `add` carries number(this)/
        // number(other) through and adds number(res); every chunk stays at 1.
        let input = r#"
predicate number(this: Ref)

method assign(this: Ref, value: Int)
    ensures number(this)

method read(this: Ref) returns (val: Int)
    requires number(this)
    ensures number(this)

method add(this: Ref, other: Ref) returns (res: Ref)
    requires number(this) && number(other)
    ensures number(this) && number(other) && number(res)
{
    var a: Int := read(this)
    var b: Int := read(other)
    var sum: Int := a + b
    assign(res, sum)
}
"#;
        let program = lower(input);
        let add_id = program.interner.get("add").expect("add method");
        let vmir::Declaration::Method(add) = &program.decls[add_id] else {
            panic!("add must be a Method");
        };
        let result = verify_method(&program, "add", add);
        assert!(result.is_ok(), "expected Ok, got {result:?}");
    }

    #[test]
    fn exhale_exceeding_held_permission_fails() {
        // `client` holds only `1/2` of `acc(x.f)` but calls `needs_full`, whose
        // precondition exhales the full `1/1`. The exhale would drive the
        // permission to `-1/2`, so verification must fail rather than allow a
        // negative permission.
        let input = r#"
field f: Int

method needs_full(x: Ref)
    requires acc(x.f, 1/1)

method client(x: Ref)
    requires acc(x.f, 1/2)
{
    needs_full(x)
}
"#;
        let program = lower(input);
        let client_id = program.interner.get("client").expect("client method");
        let vmir::Declaration::Method(client) = &program.decls[client_id] else {
            panic!("client must be a Method");
        };
        let result = verify_method(&program, "client", client);
        assert!(
            matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
            "expected InsufficientPermission, got {result:?}"
        );
    }

    /// Verify the resource interned under `name`, panicking if it is missing or
    /// is not a `Resource`.
    fn verify_named_resource(program: &vmir::Program, name: &str) -> Result<(), VerifyError> {
        let id = program
            .interner
            .get(name)
            .unwrap_or_else(|| panic!("missing resource {name}"));
        let vmir::Declaration::Resource(r) = &program.decls[id] else {
            panic!("{name} must be a Resource");
        };
        verify_resource(program, name, r)
    }

    #[test]
    fn resource_negative_permission_rejected() {
        // `acc(x.f, 1/1 - 2/1)` folds to permission -1 → side condition fails.
        let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1 - 2/1)
"#;
        let program = lower(input);
        let result = verify_named_resource(&program, "m@requires");
        assert!(
            matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::SideCondition(_))),
            "expected SideCondition, got {result:?}"
        );
    }

    #[test]
    fn resource_positive_permission_ok() {
        let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
"#;
        let program = lower(input);
        let result = verify_named_resource(&program, "m@requires");
        assert!(result.is_ok(), "expected Ok, got {result:?}");
    }

    #[test]
    fn resource_div_by_zero_rejected() {
        // `x / 0` in the precondition → divisor side condition fails.
        let input = r#"
method m(x: Int)
    requires x / 0 == x
"#;
        let program = lower(input);
        let result = verify_named_resource(&program, "m@requires");
        assert!(
            matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::SideCondition(_))),
            "expected SideCondition, got {result:?}"
        );
    }

    /// Verify the method `name`, panicking if missing or not a `Method`.
    fn verify_named_method(program: &vmir::Program, name: &str) -> Result<(), VerifyError> {
        let id = program
            .interner
            .get(name)
            .unwrap_or_else(|| panic!("missing method {name}"));
        let vmir::Declaration::Method(m) = &program.decls[id] else {
            panic!("{name} must be a Method");
        };
        verify_method(program, name, m)
    }

    #[test]
    fn inline_inhale_then_exhale_roundtrips() {
        // Inhale a field + a fact about it (read against the growing heap), then
        // exhale the fact (read against the pre-exhale heap) and the permission.
        let input = r#"
field f: Int

method m(x: Ref)
{
    inhale acc(x.f, 1/1) && x.f == 5
    exhale x.f == 5
    exhale acc(x.f, 1/1)
}
"#;
        let program = lower(input);
        assert!(
            verify_named_method(&program, "m").is_ok(),
            "inhale/exhale roundtrip should verify"
        );
    }

    #[test]
    fn inline_exhale_without_permission_fails() {
        // Exhaling `1/1` while only `1/2` was inhaled drives permission negative.
        let input = r#"
field f: Int

method m(x: Ref)
{
    inhale acc(x.f, 1/2)
    exhale acc(x.f, 1/1)
}
"#;
        let program = lower(input);
        let result = verify_named_method(&program, "m");
        assert!(
            matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
            "expected InsufficientPermission, got {result:?}"
        );
    }

    #[test]
    fn inline_exhale_unproven_fact_fails() {
        // The exhaled boolean `x.f == 5` is not known (nothing assumed it).
        let input = r#"
field f: Int

method m(x: Ref)
{
    inhale acc(x.f, 1/1)
    exhale x.f == 5
}
"#;
        let program = lower(input);
        let result = verify_named_method(&program, "m");
        assert!(
            matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::AssertionFailed)),
            "expected AssertionFailed, got {result:?}"
        );
    }

    #[test]
    fn new_single_field_grants_full_permission() {
        let input = r#"
field f: Int

method m()
{
    var x: Ref := new(f)
    exhale acc(x.f, 1/1)
}
"#;
        let program = lower(input);
        assert!(
            verify_named_method(&program, "m").is_ok(),
            "new(f) should grant full permission to x.f"
        );
    }

    #[test]
    fn new_permission_is_exactly_full() {
        // `new(f)` grants exactly `1/1`; exhaling it twice over-consumes.
        let input = r#"
field f: Int

method m()
{
    var x: Ref := new(f)
    exhale acc(x.f, 1/1)
    exhale acc(x.f, 1/1)
}
"#;
        let program = lower(input);
        let result = verify_named_method(&program, "m");
        assert!(
            matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
            "expected InsufficientPermission, got {result:?}"
        );
    }

    #[test]
    fn perm_in_exhale_sees_removed_permission() {
        // `acc(x.f)` is exhaled first, so `perm(x.f)` then reads `none` (0).
        let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    exhale acc(x.f, 1/1) && perm(x.f) == none
}
"#;
        let program = lower(input);
        assert!(
            verify_named_method(&program, "m").is_ok(),
            "perm() in exhale must see the post-removal heap"
        );
    }

    #[test]
    fn perm_before_acc_in_exhale_is_full() {
        // `perm(x.f)` is read before its `acc` is subtracted, so it is `write` (1).
        let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    exhale perm(x.f) == write && acc(x.f, 1/1)
}
"#;
        let program = lower(input);
        assert!(
            verify_named_method(&program, "m").is_ok(),
            "perm() read before its acc must be full"
        );
    }

    #[test]
    fn perm_in_inhale_sees_added_permission() {
        // Inhale tracks the growing heap: after `acc(x.f)`, `perm(x.f) == write`.
        let input = r#"
field f: Int

method m(x: Ref)
{
    inhale acc(x.f, 1/1) && perm(x.f) == write
    exhale acc(x.f, 1/1)
}
"#;
        let program = lower(input);
        assert!(
            verify_named_method(&program, "m").is_ok(),
            "perm() in inhale must see the added permission"
        );
    }

    #[test]
    fn exhale_value_read_uses_pre_exhale_heap() {
        // The value `x.f` is read in the same exhale that gives up `acc(x.f)`;
        // value reads resolve against the fixed pre-exhale heap, so it works.
        let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    inhale x.f == 5
    exhale acc(x.f, 1/1) && x.f == 5
}
"#;
        let program = lower(input);
        assert!(
            verify_named_method(&program, "m").is_ok(),
            "value read in exhale must use the pre-exhale heap"
        );
    }

    #[test]
    fn assert_held_permission_ok() {
        // `assert acc(x.f)` becomes `perm(x.f) >= write`; held in full → ok, and
        // it is non-destructive, so the permission is still exhalable after.
        let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    assert acc(x.f, 1/1)
    exhale acc(x.f, 1/1)
}
"#;
        let program = lower(input);
        assert!(
            verify_named_method(&program, "m").is_ok(),
            "assert acc must hold and not consume the permission"
        );
    }

    #[test]
    fn assert_unheld_permission_fails() {
        // `perm(x.f) = 0 >= write` is false.
        let input = r#"
field f: Int

method m(x: Ref)
{
    assert acc(x.f, 1/1)
}
"#;
        let program = lower(input);
        let result = verify_named_method(&program, "m");
        assert!(
            matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::AssertionFailed)),
            "expected AssertionFailed, got {result:?}"
        );
    }

    #[test]
    fn deref_without_permission_fails() {
        let input = r#"
field f: Int

method m(x: Ref)
{
    assert x.f == 5
}
"#;
        let program = lower(input);
        let result = verify_named_method(&program, "m");
        assert!(
            matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
            "expected InsufficientPermission, got {result:?}"
        );
    }

    #[test]
    fn assert_pure_unproven_fails() {
        let input = r#"
method m(x: Int)
{
    assert x == 5
}
"#;
        let program = lower(input);
        let result = verify_named_method(&program, "m");
        assert!(
            matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::AssertionFailed)),
            "expected AssertionFailed, got {result:?}"
        );
    }

    #[test]
    fn assume_then_assert_pure() {
        let input = r#"
method m(x: Int)
{
    assume x == 5
    assert x == 5
}
"#;
        let program = lower(input);
        assert!(
            verify_named_method(&program, "m").is_ok(),
            "assumed fact must be assertable"
        );
    }

    #[test]
    fn assume_then_assert_acc() {
        // `assume acc(x.f)` records the fact `perm(x.f) >= write` (it adds no
        // chunk — unlike `inhale`); asserting the same fact then holds. The
        // permission is genuinely held here so the assumed fact is consistent.
        let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    assume acc(x.f, 1/1)
    assert acc(x.f, 1/1)
}
"#;
        let program = lower(input);
        assert!(
            verify_named_method(&program, "m").is_ok(),
            "assumed perm fact must be assertable"
        );
    }

    #[test]
    fn new_multiple_fields() {
        let input = r#"
field f: Int
field g: Int

method m()
{
    var x: Ref := new(f, g)
    exhale acc(x.f, 1/1) && acc(x.g, 1/1)
}
"#;
        let program = lower(input);
        assert!(
            verify_named_method(&program, "m").is_ok(),
            "new(f, g) should grant full permission to both fields"
        );
    }
}
