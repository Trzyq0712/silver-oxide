use std::collections::HashMap;

use crate::vmir::display::VmirDisplay;
use crate::{
    verify::{
        context::{ResourceCertificate, VerifyContext},
        heap::{Chunk, Heap},
        lang::Symbolic,
        viz::Snapshotter,
    },
    vmir::{
        self, Assign, BinOp, Declaration, HeapInst, HeapVal, Inst, InstKind, Literal, MemberId,
        Method, PathConds, Polarity, Precond, PureInst, Resource, ResourceCall, Sign, Target, Type,
        Val,
    },
};

#[derive(Debug)]
pub enum VerifyError {
    AssertionFailed,
    /// A `refute` whose expression turned out to be provable (so the refutation
    /// fails).
    RefuteFailed,
    InsufficientPermission,
    AbstractResourceCall,
    /// A resource's side condition (e.g. `acc` permission ≥ 0, division divisor
    /// ≠ 0) could not be discharged. Carries a human-readable description.
    SideCondition(&'static str),
    /// Encountered a method-only heap extension (e.g. `Assign`) in a body
    /// the verifier doesn't yet handle structurally. Reserved for
    /// not-yet-implemented variants.
    Unimplemented(&'static str),
    /// A call/fold/unfold targets a resource that produced no certificate —
    /// i.e. the resource itself failed its well-formedness verification.
    DependencyFailed,
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
            Self::RefuteFailed => write!(f, "refuted expression is actually provable"),
            Self::InsufficientPermission => write!(f, "insufficient permission"),
            Self::AbstractResourceCall => write!(f, "call to abstract resource"),
            Self::SideCondition(what) => write!(f, "side condition may not hold: {what}"),
            Self::Unimplemented(what) => write!(f, "unimplemented: {what}"),
            Self::DependencyFailed => {
                write!(f, "depends on a resource that failed to verify")
            }
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
fn format_inst(
    inst: &Inst,
    interner: &lasso::Rodeo<MemberId>,
    val_base: usize,
    heap_base: usize,
) -> String {
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

/// Heaps to visualize for an instruction, labeled as in VMIR (`h0`, `h1`, …).
/// For a heap `combine` this is the base operand plus the result; for any other
/// instruction it is the current working heap (if any). Called after the
/// instruction has been evaluated, so the result heap sits at `heaps_before`.
fn display_heaps(state: &EvalState, kind: &InstKind, heaps_before: usize) -> Vec<(String, Heap)> {
    match kind {
        InstKind::Heap(HeapInst::Combine { base, .. }) => vec![
            (base.to_string(), get_heap(state, base)),
            (
                format!("h{heaps_before}"),
                state.heaps[heaps_before].clone(),
            ),
        ],
        _ => state
            .heaps
            .last()
            .map(|h| (format!("h{}", state.heaps.len() - 1), h.clone()))
            .into_iter()
            .collect(),
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
    let positive = ctx.add(Symbolic::Binary(BinOp::Lt, [zero, perm]));
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

/// Evaluate a `PureInst` into its symbolic e-class id.
fn eval_pure_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    ty: &Type,
    pi: &PureInst,
) -> egg::Id {
    match pi {
        PureInst::Fresh => ctx.fresh_symbolic_value(ty.clone()),
        PureInst::Binary(op, l, r) => {
            let lhs = state.get_val(ctx, l);
            let rhs = state.get_val(ctx, r);
            ctx.add(Symbolic::Binary(*op, [lhs, rhs]))
        }
        PureInst::Ternary(c, t, e) => {
            let cond = state.get_val(ctx, c);
            let then_ = state.get_val(ctx, t);
            let else_ = state.get_val(ctx, e);
            ctx.add(Symbolic::Ite([cond, then_, else_]))
        }
        PureInst::RealCast(v) => {
            let inner = state.get_val(ctx, v);
            ctx.add(Symbolic::RealCast(inner))
        }
        PureInst::Deref(hv, loc) => {
            let heap = get_heap(state, hv);
            let addr = state.get_val(ctx, loc);
            heap.value_at(addr)
                .unwrap_or_else(|| ctx.fresh_symbolic_value(ty.clone()))
        }
        PureInst::FunctionCall(_heap, fc) => {
            let args: Vec<egg::Id> = fc.args.iter().map(|v| state.get_val(ctx, v)).collect();
            ctx.add_func_app(fc, ty.clone(), args.into())
        }
        // perm(loc): permission amount held at `loc` in the given heap.
        PureInst::Perm(hv, loc) => {
            let heap = get_heap(state, hv);
            let addr = state.get_val(ctx, loc);
            heap.perm_at(addr).unwrap_or_else(|| zero_real(ctx))
        }
    }
}

/// Singleton heap for `acc loc perm`: one chunk at `loc` with permission `perm`
/// and a fresh held value.
/// The declared return type of a `Function` declaration (`Int` fallback). Used
/// to type the synthesized `@addr` / snapshot `cons`/`proj` applications.
fn decl_ret_ty(program: &vmir::Program, id: MemberId) -> Type {
    match &program.decls[id] {
        Declaration::Function(f) => f.ret.clone(),
        _ => Type::Int,
    }
}

fn heap_acc(ctx: &mut VerifyContext<'_>, loc: &Val, perm: &Val, state: &EvalState) -> Heap {
    let addr = state.get_val(ctx, loc);
    let perm = state.get_val(ctx, perm);
    // The held value's type is the `T` in the location's `Addr<T>` type (the
    // `@addr` function's return type) — e.g. a field's type, or a predicate's
    // `@snap`. Fall back to `Int` if the location type can't be inferred.
    let value_ty = crate::verify::context::infer_type(
        &ctx.egraph,
        &ctx.fresh_types,
        &ctx.func_ret_types,
        addr,
        &mut HashMap::new(),
    )
    .and_then(|t| match t {
        Type::Addr(inner) => Some(*inner),
        _ => None,
    })
    .unwrap_or(Type::Int);
    let value = ctx.fresh_symbolic_value(value_ty);
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
    let perm = ctx.add(Symbolic::Binary(BinOp::Plus, [p0, p1]));

    let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigRational::from(
        num::BigInt::from(0),
    ))));
    let p0_pos = ctx.add(Symbolic::Binary(BinOp::Lt, [zero, p0]));
    let p1_pos = ctx.add(Symbolic::Binary(BinOp::Lt, [zero, p1]));

    let value = ctx.add(Symbolic::Ite([p0_pos, v0, v1]));

    // `(PC ∧ p0 > 0 ∧ p1 > 0) ==> (v0 == v1)` as the golden-rule ITE chain.
    // Fold innermost-first: p1_pos, p0_pos, then PC literals in reverse.
    let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
    let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [v0, v1]));
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
                ctx,
                existing.perm,
                existing.value,
                chunk.perm,
                chunk.value,
                pc_lits,
            );
            out = out.with_chunk(canon, merged);
        } else {
            out = out.with_chunk(canon, chunk);
        }
    }
    out
}

/// A field chunk extracted from a heap for the field axioms: its permission, the
/// field address function (`field_fn`), and the base ref (`field_fn(ref)`).
struct FieldChunk {
    perm: egg::Id,
    field_fn: MemberId,
    base: egg::Id,
}

/// Extract the field chunks of `h`: for each chunk whose canonical address holds
/// a `FuncApp(m, [ref])` with `m` a field address function, record its perm,
/// field, and base ref. Predicate locations (head not in `field_addrs`) are
/// skipped. Relies on the translation invariant that an address is always a bare
/// `field_fn(ref)` application (arity 1) — never a computed value.
fn field_chunks(ctx: &VerifyContext<'_>, h: &Heap) -> Vec<FieldChunk> {
    let mut out = Vec::new();
    for (addr, chunk) in h.entries() {
        let canon = ctx.egraph.find(addr);
        let found = ctx.egraph[canon].nodes.iter().find_map(|n| match n {
            Symbolic::FuncApp(m, args) if ctx.field_addrs.contains(m) && args.len() == 1 => {
                Some((*m, args[0]))
            }
            _ => None,
        });
        if let Some((field_fn, base)) = found {
            out.push(FieldChunk {
                perm: chunk.perm,
                field_fn,
                base,
            });
        }
    }
    out
}

/// Emit the field-permission axioms over `h` after a consolidation:
/// - **bound:** every field cell holds `perm ≤ 1` (`union((1 < perm) ? false :
///   true, true)`); a permission folding to `> 1` unions `false == true`, making
///   the unit inconsistent so any goal is dischargeable.
/// - **non-aliasing:** for two chunks of the *same* field whose permissions sum
///   (const-folds) to `> 1`, the base refs differ (`union(Eq(x, y), false)`).
///
/// Predicate locations are unbounded and never participate.
fn assume_field_axioms(ctx: &mut VerifyContext<'_>, h: &Heap) {
    let fields = field_chunks(ctx, h);
    if fields.is_empty() {
        return;
    }
    let one = ctx.add(Symbolic::Lit(Literal::Real(num::BigRational::from(
        num::BigInt::from(1),
    ))));
    let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
    let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));

    // Bound: perm ≤ 1 at each field location.
    for fc in &fields {
        let gt1 = ctx.add(Symbolic::Binary(BinOp::Lt, [one, fc.perm]));
        let le1 = ctx.add(Symbolic::Ite([gt1, false_, true_]));
        ctx.egraph.union(le1, true_);
    }

    // Non-aliasing: same field, perms sum > 1 ⇒ the refs differ.
    for i in 0..fields.len() {
        for j in (i + 1)..fields.len() {
            if fields[i].field_fn != fields[j].field_fn {
                continue;
            }
            let sum = ctx.add(Symbolic::Binary(
                BinOp::Plus,
                [fields[i].perm, fields[j].perm],
            ));
            let over_one = matches!(
                ctx.egraph[ctx.egraph.find(sum)].data.known(),
                Some(Literal::Real(r)) if *r > num::BigRational::from(num::BigInt::from(1))
            );
            if over_one {
                let (x, y) = (fields[i].base, fields[j].base);
                let eq_xy = ctx.add(Symbolic::Binary(BinOp::Eq, [x, y]));
                let eq_yx = ctx.add(Symbolic::Binary(BinOp::Eq, [y, x]));
                ctx.egraph.union(eq_xy, false_);
                ctx.egraph.union(eq_yx, false_);
            }
        }
    }
    ctx.egraph.rebuild();
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
                ctx,
                existing.perm,
                existing.value,
                chunk2.perm,
                chunk2.value,
                pc_lits,
            );
            out = out.with_chunk(addr, merged);
        } else {
            out = out.with_chunk(addr, chunk2);
        }
    }
    // Every heap `+` re-asserts the field axioms (bound + non-aliasing) on the
    // consolidated result.
    assume_field_axioms(ctx, &out);
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
        let lt = ctx.add(Symbolic::Binary(BinOp::Lt, [existing.perm, chunk2.perm]));
        let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        let goal = ctx.add(Symbolic::Ite([lt, false_, true_]));
        if !ctx.prove_under_pc(goal, pc_lits) {
            return Err(VerifyError::InsufficientPermission);
        }

        ctx.egraph.union(existing.value, chunk2.value);

        let remainder = ctx.add(Symbolic::Binary(BinOp::Minus, [existing.perm, chunk2.perm]));
        if extract_real_literal(ctx, remainder).as_ref() == Some(&zero_rat) {
            out = out.without_chunk(addr);
        } else {
            out = out.with_chunk(addr, Chunk::new(remainder, existing.value));
        }
    }
    Ok(out)
}

/// Evaluate a heap inst. `Sub` may fail with `InsufficientPermission`.
fn eval_heap_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    inst: &HeapInst,
    pc: &PathConds,
) -> Result<Heap, VerifyError> {
    match inst {
        // `base ± acc loc perm`: build the single chunk, then union (Add) or
        // subtract (Sub) it. The resource-target case is method-only (it needs
        // the program + certificates) and is handled in `eval_method_inst`.
        HeapInst::Combine {
            base,
            sign,
            target: Target::Loc(loc),
            perm,
        } => {
            let base_h = get_heap(state, base);
            let chunk = heap_acc(ctx, loc, perm, state);
            let pc_lits: Vec<(egg::Id, Polarity)> = pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            match sign {
                Sign::Add => Ok(heap_union(ctx, &base_h, &chunk, &pc_lits)),
                Sign::Sub => heap_subtract(ctx, &base_h, &chunk, &pc_lits),
            }
        }
        HeapInst::Combine {
            target: Target::Resource(_),
            ..
        } => Err(VerifyError::Unimplemented(
            "resource combine outside method body",
        )),
        // Fold/Unfold need the program + certificates; handled in
        // `eval_method_inst`.
        HeapInst::Fold { .. } | HeapInst::Unfold { .. } => Err(VerifyError::Unimplemented(
            "fold/unfold outside method body",
        )),
        // Field assignment `loc := val`: requires write permission at `loc`,
        // then updates the chunk's value (permission unchanged).
        HeapInst::Assign(heap, Assign { loc, val }) => {
            let h = get_heap(state, heap);
            let addr = state.get_val(ctx, loc);
            let new_val = state.get_val(ctx, val);
            let perm = h.perm_at(addr).unwrap_or_else(|| zero_real(ctx));
            // SIDECOND: prove `not(perm < 1)` (full/write permission) under pc.
            let pc_lits: Vec<(egg::Id, Polarity)> = pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            let write = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
            let lt = ctx.add(Symbolic::Binary(BinOp::Lt, [perm, write]));
            let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
            let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
            let goal = ctx.add(Symbolic::Ite([lt, false_, true_]));
            if !ctx.prove_under_pc(goal, &pc_lits) {
                return Err(VerifyError::InsufficientPermission);
            }
            Ok(h.with_chunk(addr, Chunk::new(perm, new_val)))
        }
    }
}

/// Evaluate one instruction of a resource body (well-formedness pass). Resource
/// bodies currently emit only `Pure`/`Heap`; the effectful variants are not yet
/// produced there (a follow-up enables inline `assume`).
fn eval_resource_body_inst(
    ctx: &mut VerifyContext<'_>,
    state: &mut EvalState,
    inst: &Inst,
) -> Result<(), VerifyError> {
    match &inst.kind {
        InstKind::Pure(ty, pi) => {
            let id = eval_pure_inst(ctx, state, ty, pi);
            state.push_val(id);
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, &inst.pc)?;
            state.push_heap(heap);
        }
        InstKind::Assume(_) | InstKind::Assert(_) | InstKind::Refute(_) => {
            return Err(VerifyError::Unimplemented(
                "effectful inst in resource body",
            ));
        }
    }
    Ok(())
}

/// Evaluate a resource invocation as a **reusable proof** by grafting the
/// resource's pre-verified certificate (see [`verify_resource`]) into the
/// caller's e-graph, substituting the formal params for the call args. This
/// transfers every proven merge for free — no re-walk, no re-saturation — and
/// returns `(heap_delta, bool_handle)`. The *outer* boolean is **not** assumed
/// or asserted here; the caller decides.
fn eval_resource_call(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    caller_state: &EvalState,
    call: &ResourceCall,
    certs: &HashMap<MemberId, ResourceCertificate>,
) -> Result<(Heap, egg::Id), VerifyError> {
    let Declaration::Resource(r) = &program.decls[call.resource] else {
        panic!("ResourceCall targets non-Resource declaration");
    };
    if r.body.is_none() {
        return Err(VerifyError::AbstractResourceCall);
    }
    let cert = certs
        .get(&call.resource)
        .ok_or(VerifyError::DependencyFailed)?;

    let args: Vec<egg::Id> = call
        .args
        .iter()
        .map(|v| caller_state.get_val(ctx, v))
        .collect();

    Ok(ctx.graft_certificate(cert, &args))
}

fn eval_method_inst(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceCertificate>,
) -> Result<(), VerifyError> {
    match &inst.kind {
        InstKind::Pure(ty, pi) => {
            let id = eval_pure_inst(ctx, state, ty, pi);
            state.push_val(id);
        }
        // `base ± acc <resource>(args) perm`: graft the resource's certificate,
        // scale its delta by `perm`, union (Add) / subtract (Sub) against `base`,
        // and implicitly assume (Add) / assert (Sub) the resource's boolean.
        InstKind::Heap(HeapInst::Combine {
            base,
            sign,
            target: Target::Resource(call),
            perm,
        }) => {
            let base_h = get_heap(state, base);
            let (delta, bool_id) = eval_resource_call(ctx, program, state, call, certs)?;
            let scale = state.get_val(ctx, perm);
            let scaled = scale_heap_perm(ctx, &delta, scale);
            let pc_lits: Vec<(egg::Id, Polarity)> = inst
                .pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            let out = match sign {
                Sign::Add => heap_union(ctx, &base_h, &scaled, &pc_lits),
                Sign::Sub => heap_subtract(ctx, &base_h, &scaled, &pc_lits)?,
            };
            match sign {
                Sign::Add => {
                    let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
                    ctx.egraph.union(bool_id, true_);
                    ctx.egraph.rebuild();
                }
                Sign::Sub => {
                    if !ctx.prove_under_pc(bool_id, &pc_lits) {
                        return Err(VerifyError::AssertionFailed);
                    }
                }
            }
            state.push_heap(out);
        }
        // `fold`: consume the predicate footprint (scaled by `perm`), assert the
        // body's pure facts, and produce a predicate chunk holding the snapshot
        // (`cons`) of the consumed field values.
        InstKind::Heap(HeapInst::Fold { base, call, perm }) => {
            let base_h = get_heap(state, base);
            let pmeta = program
                .pred_meta
                .get(&call.resource)
                .ok_or(VerifyError::Unimplemented(
                    "fold of non-flat/abstract predicate",
                ))?;
            let (snap_cons, addr_fn) = (pmeta.snap_cons, pmeta.addr_fn);
            let projs = pmeta.snap_projs.clone();
            let n_slots = projs.len();
            let cert = certs
                .get(&call.resource)
                .ok_or(VerifyError::DependencyFailed)?;
            let args: Vec<egg::Id> = call.args.iter().map(|v| state.get_val(ctx, v)).collect();
            let perm_id = state.get_val(ctx, perm);
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);

            let fp = ctx.graft_footprint(cert, &args);
            if fp.len() != n_slots {
                return Err(VerifyError::Unimplemented(
                    "predicate footprint shape mismatch",
                ));
            }
            let canon = canonicalize_heap(ctx, &base_h, &[]);
            // Raw field values feed the body's pure facts; the snapshot members
            // wrap each value as `(perm>0) ? Some(v) : None` (const-folds to
            // `Some(v)` ⇒ `v` for a statically-positive permission).
            let mut values = Vec::with_capacity(fp.len());
            let mut members = Vec::with_capacity(fp.len());
            let mut need_heap = Heap::empty();
            for (i, &(addr, bperm)) in fp.iter().enumerate() {
                let a = ctx.egraph.find(addr);
                let v = canon
                    .chunk(a)
                    .map(|c| c.value)
                    .unwrap_or_else(|| ctx.fresh_symbolic_value(Type::Int));
                let need = ctx.add(Symbolic::Binary(BinOp::Mult, [perm_id, bperm]));
                need_heap = need_heap.with_chunk(addr, Chunk::new(need, v));
                let elem = decl_ret_ty(program, projs[i]);
                let present = ctx.perm_positive(bperm);
                members.push(ctx.option_member(elem, present, v));
                values.push(v);
            }
            let subtracted = heap_subtract(ctx, &base_h, &need_heap, &pc_lits)?;
            let bool_id = ctx.graft_pred_bool(cert, &args, &values);
            if !ctx.prove_under_pc(bool_id, &pc_lits) {
                return Err(VerifyError::AssertionFailed);
            }
            let cons_args: Box<[egg::Id]> = members.into_iter().collect();
            let snap = ctx.add_func_app_id(snap_cons, decl_ret_ty(program, snap_cons), cons_args);
            let pred_addr =
                ctx.add_func_app_id(addr_fn, decl_ret_ty(program, addr_fn), args.into());
            let pred_chunk = Heap::empty().with_chunk(pred_addr, Chunk::new(perm_id, snap));
            let out = heap_union(ctx, &subtracted, &pred_chunk, &pc_lits);
            state.push_heap(out);
            // Collapse any snapshot tower created by repeated fold/unfold.
            ctx.reduce();
        }
        // `unfold`: inverse of fold — consume the predicate chunk, reproduce the
        // footprint (fields recovered by projecting the snapshot), assume the
        // body's pure facts.
        InstKind::Heap(HeapInst::Unfold { base, call, perm }) => {
            let base_h = get_heap(state, base);
            let pmeta = program
                .pred_meta
                .get(&call.resource)
                .ok_or(VerifyError::Unimplemented(
                    "unfold of non-flat/abstract predicate",
                ))?;
            let addr_fn = pmeta.addr_fn;
            let projs = pmeta.snap_projs.clone();
            let cert = certs
                .get(&call.resource)
                .ok_or(VerifyError::DependencyFailed)?;
            let args: Vec<egg::Id> = call.args.iter().map(|v| state.get_val(ctx, v)).collect();
            let perm_id = state.get_val(ctx, perm);
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);

            let pred_addr =
                ctx.add_func_app_id(addr_fn, decl_ret_ty(program, addr_fn), args.clone().into());
            let canon = canonicalize_heap(ctx, &base_h, &[]);
            let s = canon
                .chunk(ctx.egraph.find(pred_addr))
                .map(|c| c.value)
                .ok_or(VerifyError::InsufficientPermission)?;
            let pred_chunk = Heap::empty().with_chunk(pred_addr, Chunk::new(perm_id, s));
            let subtracted = heap_subtract(ctx, &base_h, &pred_chunk, &pc_lits)?;

            let fp = ctx.graft_footprint(cert, &args);
            if fp.len() != projs.len() {
                return Err(VerifyError::Unimplemented(
                    "predicate footprint shape mismatch",
                ));
            }
            let mut out = subtracted;
            let mut values = Vec::with_capacity(fp.len());
            for (i, &(addr, bperm)) in fp.iter().enumerate() {
                // `proj_i(s)` recovers the optional snapshot member; `reduce()`
                // collapses it to the constructor's i-th member when `s` is a
                // concrete `cons` (so repeated fold/unfold doesn't grow the
                // snapshot tower), and leaves it uninterpreted for an opaque
                // snapshot. `unwrap` then peels the `Option` to the field value.
                let elem = decl_ret_ty(program, projs[i]);
                let opt =
                    ctx.add_func_app_id(projs[i], ctx.option_type(elem.clone()), Box::new([s]));
                let pv = ctx.option_unwrap(elem, opt);
                let need = ctx.add(Symbolic::Binary(BinOp::Mult, [perm_id, bperm]));
                let chunk = Heap::empty().with_chunk(addr, Chunk::new(need, pv));
                out = heap_union(ctx, &out, &chunk, &pc_lits);
                values.push(pv);
            }
            let bool_id = ctx.graft_pred_bool(cert, &args, &values);
            let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
            ctx.egraph.union(bool_id, true_);
            ctx.egraph.rebuild();
            state.push_heap(out);
            // Collapse any snapshot tower created by repeated fold/unfold.
            ctx.reduce();
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, &inst.pc)?;
            state.push_heap(heap);
        }
        InstKind::Assume(val) => {
            let id = state.get_val(ctx, val);
            let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
            ctx.egraph.union(id, true_);
            ctx.egraph.rebuild();
        }
        InstKind::Assert(val) => {
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
        InstKind::Refute(val) => {
            // `refute A` succeeds iff `A` is NOT provable in this state.
            let id = state.get_val(ctx, val);
            let pc_lits: Vec<(egg::Id, Polarity)> = inst
                .pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            if ctx.prove_under_pc(id, &pc_lits) {
                return Err(VerifyError::RefuteFailed);
            }
        }
    }
    Ok(())
}

/// Scale every chunk's permission in `h` by `scale` (`perm := scale * perm`),
/// leaving values untouched. For the common `scale = 1` case the `1 * x → x`
/// rewrite folds the multiply away.
fn scale_heap_perm(ctx: &mut VerifyContext<'_>, h: &Heap, scale: egg::Id) -> Heap {
    let mut out = Heap::empty();
    for (addr, chunk) in h.entries() {
        let perm = ctx.add(Symbolic::Binary(BinOp::Mult, [scale, chunk.perm]));
        out = out.with_chunk(addr, Chunk::new(perm, chunk.value));
    }
    out
}

pub fn verify_method(
    program: &vmir::Program,
    method_name: &str,
    method: &Method,
    certs: &HashMap<MemberId, ResourceCertificate>,
) -> Result<(), VerifyError> {
    let mut ctx = VerifyContext::new(
        &program.interner,
        &program.adt_meta,
        program.field_addrs.clone(),
    );
    let mut state = EvalState::new();
    let mut snap = Snapshotter::from_env(method_name);

    snap.snapshot(&ctx, &[], "init", None);
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
        if let Err(err) = eval_method_inst(&mut ctx, program, &mut state, inst, certs) {
            return Err(err.with_inst(inst_text));
        }
        let highlight = (state.vals.len() > vals_before).then(|| state.vals[state.vals.len() - 1]);
        let heaps = display_heaps(&state, &inst.kind, heaps_before);
        snap.snapshot(&ctx, &heaps, &inst_text, highlight);
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
) -> Result<Option<ResourceCertificate>, VerifyError> {
    let Some(body) = resource.body.as_ref() else {
        // Abstract resource: nothing to prove, no certificate.
        return Ok(None);
    };

    let mut ctx = VerifyContext::new(
        &program.interner,
        &program.adt_meta,
        program.field_addrs.clone(),
    );
    let params: Vec<egg::Id> = resource
        .params
        .iter()
        .map(|ty| ctx.fresh_symbolic_value(ty.clone()))
        .collect();
    let mut state = EvalState::with_args(params.clone());
    // A two-state (`Ctx`) resource reads a parametric context heap as
    // `HeapVal::Temp(0)` (empty here; reads yield fresh symbolics), so pre-push
    // it. A self-framed resource has no precondition: its initial heap is
    // `Empty` and its emitted heaps start at `Temp(0)`, so push nothing.
    if !matches!(resource.precond, Precond::SelfFramed) {
        state.push_heap(Heap::empty());
    }

    let mut snap = Snapshotter::from_env(resource_name);
    snap.snapshot(&ctx, &[], "init", None);

    // Ordered per-acc footprint operands `(loc, perm)`, in body order — one per
    // syntactic `acc` (location target), kept unmerged for the fold/unfold
    // snapshot layout (the merged `delta` below is for inhale/exhale).
    let mut footprint_ops: Vec<(Val, Val)> = Vec::new();

    for inst in &body.insts {
        if let InstKind::Heap(HeapInst::Combine {
            target: Target::Loc(loc),
            perm,
            ..
        }) = &inst.kind
        {
            footprint_ops.push((loc.clone(), perm.clone()));
        }
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
        let heaps = display_heaps(&state, &inst.kind, heaps_before);
        snap.snapshot(&ctx, &heaps, &inst_text, highlight);
    }

    // Saturate so the certificate carries every proven merge, then snapshot the
    // result roots (canonicalized) for grafting at call sites.
    ctx.saturate();
    let delta_heap = get_heap(&state, &body.res.0);
    let delta: Vec<(egg::Id, egg::Id, egg::Id)> = delta_heap
        .entries()
        .map(|(addr, chunk)| {
            (
                ctx.egraph.find(addr),
                ctx.egraph.find(chunk.perm),
                ctx.egraph.find(chunk.value),
            )
        })
        .collect();
    // Unmerged, program-ordered footprint: each acc's `(addr, perm)` with the
    // *merged* chunk value at that address (so aliased slots stay separate yet
    // share their value). Drives the fold/unfold snapshot layout.
    let footprint: Vec<(egg::Id, egg::Id, egg::Id)> = footprint_ops
        .iter()
        .map(|(loc, perm)| {
            let addr = state.get_val(&mut ctx, loc);
            let addr = ctx.egraph.find(addr);
            let perm = state.get_val(&mut ctx, perm);
            let perm = ctx.egraph.find(perm);
            let value = delta_heap
                .chunk(addr)
                .map(|c| ctx.egraph.find(c.value))
                .unwrap_or_else(|| ctx.fresh_symbolic_value(Type::Int));
            (addr, perm, value)
        })
        .collect();
    let bool_val = state.get_val(&mut ctx, &body.res.1);
    let bool_id = ctx.egraph.find(bool_val);
    let params = params.iter().map(|&p| ctx.egraph.find(p)).collect();

    Ok(Some(ResourceCertificate {
        egraph: ctx.egraph.clone(),
        fresh_types: ctx.fresh_types.clone(),
        func_ret_types: ctx.func_ret_types.clone(),
        params,
        delta,
        footprint,
        bool_id,
    }))
}

/// Side-condition obligations implied by an instruction's kind, as
/// `(goal, description)` pairs that must each be proven `true` under the
/// instruction's path condition. `acc` requires a non-negative permission;
/// division requires a non-zero divisor.
fn inst_obligations(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    kind: &InstKind,
) -> Vec<(egg::Id, &'static str)> {
    let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
    let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
    match kind {
        // `not(perm < 0)` desugared to an `Ite`.
        InstKind::Heap(HeapInst::Combine { perm, .. }) => {
            let perm = state.get_val(ctx, perm);
            let zero = zero_real(ctx);
            let lt = ctx.add(Symbolic::Binary(BinOp::Lt, [perm, zero]));
            let goal = ctx.add(Symbolic::Ite([lt, false_, true_]));
            vec![(goal, "permission may be negative")]
        }
        // `not(divisor == 0)` desugared to an `Ite`. The divisor is homogeneous
        // with the result (casts), so the VMIR result type gives the zero's type.
        InstKind::Pure(ty, PureInst::Binary(BinOp::Div, _, r)) => {
            let rv = state.get_val(ctx, r);
            let zero = zero_of(ctx, ty);
            let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [rv, zero]));
            let goal = ctx.add(Symbolic::Ite([eq, false_, true_]));
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
mod e2e;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::lang::Symbolic;

    fn fresh_ctx<'a>(interner: &'a lasso::Rodeo<vmir::MemberId>) -> VerifyContext<'a> {
        VerifyContext::new(interner, &vmir::AdtMeta::default(), Default::default())
    }

    #[test]
    fn heap_union_merges_egg_equivalent_addresses() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let h2 = Heap::empty().with_chunk(b, Chunk::new(p2, v2));

        ctx.egraph.union(a, b);
        ctx.egraph.rebuild();

        let merged = heap_union(&mut ctx, &h1, &h2, &[]);

        let canon = ctx.egraph.find(a);
        let chunk = merged.chunk(canon).expect("merged chunk missing");

        let expected_perm = ctx.add(Symbolic::Binary(BinOp::Plus, [p1, p2]));
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

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p0, v0));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));

        let merged = heap_union(&mut ctx, &h1, &h2, &[]);
        let chunk = merged
            .chunk(ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();

        // p0 = 0 → asymmetric ternary picks the active half v1; no fusion.
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v1));
        assert_ne!(ctx.egraph.find(v0), ctx.egraph.find(v1));
    }

    #[test]
    fn merge_both_active_fuses_values() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p0, v0));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));

        let merged = heap_union(&mut ctx, &h1, &h2, &[]);
        let chunk = merged
            .chunk(ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();

        // Both fractions positive → agreement axiom fuses the symbolic values.
        assert_eq!(ctx.egraph.find(v0), ctx.egraph.find(v1));
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v0));
    }

    #[test]
    fn merge_under_false_pc_blocks_fusion() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let false_lit = ctx.add(Symbolic::Lit(Literal::Bool(false)));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p0, v0));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));

        let merged = heap_union(&mut ctx, &h1, &h2, &[(false_lit, Polarity::Positive)]);
        let chunk = merged
            .chunk(ctx.egraph.find(a))
            .expect("merged chunk missing");
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

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let true_lit = ctx.add(Symbolic::Lit(Literal::Bool(true)));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p0, v0));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));

        let merged = heap_union(&mut ctx, &h1, &h2, &[(true_lit, Polarity::Positive)]);
        let _chunk = merged
            .chunk(ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();

        // PC literal is `true` + both fractions positive → agreement fires.
        assert_eq!(ctx.egraph.find(v0), ctx.egraph.find(v1));
    }

    #[test]
    fn prove_under_empty_pc_proves_known_goal() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let g = ctx.add(Symbolic::Fresh(0));
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
        let g = ctx.add(Symbolic::Fresh(0));
        assert!(!ctx.prove_under_pc(g, &[]));
    }

    #[test]
    fn prove_under_false_pc_is_vacuous() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        // Unprovable goal, but the path is unsatisfiable (`false`).
        let g = ctx.add(Symbolic::Fresh(0));
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

        let c = ctx.add(Symbolic::Fresh(0));
        let x = ctx.add(Symbolic::Fresh(1));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        // goal = `c ? true : x` — true under hypothesis `c`, unknown otherwise.
        let goal = ctx.add(Symbolic::Ite([c, true_, x]));

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

        let a = ctx.add(Symbolic::Fresh(0));
        let p_have = ctx.add(Symbolic::Fresh(1));
        let p_take = ctx.add(Symbolic::Fresh(2));
        let v1 = ctx.add(Symbolic::Fresh(3));
        let v2 = ctx.add(Symbolic::Fresh(4));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p_have, v1));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p_take, v2));

        // Symbolic perms → `have >= take` not provable by equality saturation.
        let err = heap_subtract(&mut ctx, &h1, &h2, &[])
            .err()
            .expect("symbolic-perm exhale must fail without a proof");
        assert!(matches!(
            err.root_cause(),
            VerifyError::InsufficientPermission
        ));
    }

    #[test]
    fn heap_subtract_canonical_match() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

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

        let a = ctx.add(Symbolic::Fresh(0));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

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

        let a = ctx.add(Symbolic::Fresh(0));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

        let h1 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p2, v2));

        let err = heap_subtract(&mut ctx, &h1, &h2, &[])
            .err()
            .expect("over-consumption must fail");
        assert!(matches!(
            err.root_cause(),
            VerifyError::InsufficientPermission
        ));
    }

    #[test]
    fn heap_subtract_missing_addr_fails() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));

        let h1 = Heap::empty();
        let h2 = Heap::empty().with_chunk(a, Chunk::new(p1, v1));
        let _ = b;

        let err = heap_subtract(&mut ctx, &h1, &h2, &[])
            .err()
            .expect("subtract from empty must fail");
        assert!(matches!(
            err.root_cause(),
            VerifyError::InsufficientPermission
        ));
    }

    #[test]
    fn const_fold_folds_subtraction() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let one = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let diff = ctx.add(Symbolic::Binary(BinOp::Minus, [one, one]));
        ctx.egraph.rebuild();

        let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        assert_eq!(ctx.egraph.find(diff), ctx.egraph.find(zero));
    }

    #[test]
    fn const_fold_folds_ternary() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let cond = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        let t = ctx.add(Symbolic::Fresh(0));
        let e = ctx.add(Symbolic::Fresh(1));
        let ite = ctx.add(Symbolic::Ite([cond, t, e]));
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
        let t = ctx.add(Symbolic::Fresh(0));
        let e = ctx.add(Symbolic::Fresh(1));
        let ite = ctx.add(Symbolic::Ite([cond, t, e]));
        ctx.saturate();

        assert_eq!(ctx.egraph.find(ite), ctx.egraph.find(e));
        assert_ne!(ctx.egraph.find(ite), ctx.egraph.find(t));
    }

    #[test]
    fn rewrite_add_zero_int() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let x = ctx.add(Symbolic::Fresh(0));
        let zero = ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(0))));
        let sum = ctx.add(Symbolic::Binary(BinOp::Plus, [x, zero]));
        ctx.saturate();

        assert_eq!(ctx.egraph.find(sum), ctx.egraph.find(x));
    }

    #[test]
    fn rewrite_add_zero_real_commuted() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let x = ctx.add(Symbolic::Fresh(0));
        let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        // `0 + x` (commuted) must also fold to `x`.
        let sum = ctx.add(Symbolic::Binary(BinOp::Plus, [zero, x]));
        ctx.saturate();

        assert_eq!(ctx.egraph.find(sum), ctx.egraph.find(x));
    }

    #[test]
    fn eq_true_unions_args() {
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [a, b]));
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

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        // Build the equality but never prove it true.
        let _eq = ctx.add(Symbolic::Binary(BinOp::Eq, [a, b]));
        ctx.saturate();

        assert_ne!(ctx.egraph.find(a), ctx.egraph.find(b));
    }

    #[test]
    fn eq_true_propagates_through_congruence() {
        let mut interner = lasso::Rodeo::<vmir::MemberId>::new();
        let f = interner.get_or_intern("f");
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let fa = ctx.add(Symbolic::FuncApp(f, Box::from([a])));
        let fb = ctx.add(Symbolic::FuncApp(f, Box::from([b])));
        let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [a, b]));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        ctx.egraph.union(eq, true_);
        ctx.saturate();

        // Unioning the args lets congruence close `f(a) == f(b)`.
        assert_eq!(ctx.egraph.find(fa), ctx.egraph.find(fb));
    }

    /// Build `d != 0` as `not(d == 0)` = `ite(d == 0, false, true)`, returning
    /// the e-class id (test helper, pure VMIR / e-graph level).
    fn ne_zero(ctx: &mut VerifyContext<'_>, d: egg::Id) -> egg::Id {
        let zero = ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(0))));
        let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [d, zero]));
        let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        ctx.add(Symbolic::Ite([eq, false_, true_]))
    }

    #[test]
    fn graft_transfers_nonzero_knowledge() {
        // Pure VMIR / e-graph level — no Viper. A resource has *proven* its
        // formal param `d` non-zero (its certificate e-graph merges `d != 0`
        // with `true`). Grafting the certificate into a caller (param `d` → arg
        // `a`) transfers that fact: the caller then knows `a != 0` *without
        // assuming any boolean* — the knowledge comes from the merge alone.
        let interner = lasso::Rodeo::<vmir::MemberId>::new();

        // --- resource side: learn `d != 0` ---
        let mut rctx = fresh_ctx(&interner);
        let d = rctx.fresh_symbolic_value(Type::Int);
        let d_ne0 = ne_zero(&mut rctx, d);
        let r_true = rctx.add(Symbolic::Lit(Literal::Bool(true)));
        rctx.egraph.union(d_ne0, r_true); // the resource proved it
        rctx.egraph.rebuild();
        rctx.saturate();
        let cert = ResourceCertificate {
            egraph: rctx.egraph.clone(),
            fresh_types: rctx.fresh_types.clone(),
            func_ret_types: rctx.func_ret_types.clone(),
            params: vec![rctx.egraph.find(d)],
            delta: vec![],
            footprint: vec![],
            bool_id: rctx.egraph.find(d_ne0),
        };

        // --- caller side: graft, then check `a != 0` is known true ---
        let mut cctx = fresh_ctx(&interner);
        let a = cctx.fresh_symbolic_value(Type::Int);
        // No `Assume` anywhere — the only knowledge injected is the graft.
        let _ = cctx.graft_certificate(&cert, &[a]);
        cctx.egraph.rebuild();

        let a_ne0 = ne_zero(&mut cctx, a);
        let c_true = cctx.add(Symbolic::Lit(Literal::Bool(true)));
        cctx.saturate();
        assert_eq!(
            cctx.egraph.find(a_ne0),
            cctx.egraph.find(c_true),
            "grafted proof should make `a != 0` trivially true"
        );
    }

    #[test]
    fn realcast_folds_int_to_real() {
        // real(2) const-folds to the Real literal 2.
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);
        let two = ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(2))));
        let cast = ctx.add(Symbolic::RealCast(two));
        let real_two = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        ctx.saturate();
        assert_eq!(ctx.egraph.find(cast), ctx.egraph.find(real_two));
    }

    #[test]
    fn rewrite_and_true_collapses() {
        // b && true  =  ite(b, true, false)  =>  b
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);
        let b = ctx.add(Symbolic::Fresh(0));
        let t = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        let f = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let ite = ctx.add(Symbolic::Ite([b, t, f]));
        ctx.saturate();
        assert_eq!(ctx.egraph.find(ite), ctx.egraph.find(b));
    }

    #[test]
    fn rewrite_and_self_collapses() {
        // b && b  =  ite(b, b, false)  =>  b
        let interner = lasso::Rodeo::<vmir::MemberId>::new();
        let mut ctx = fresh_ctx(&interner);
        let b = ctx.add(Symbolic::Fresh(0));
        let f = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let ite = ctx.add(Symbolic::Ite([b, b, f]));
        ctx.saturate();
        assert_eq!(ctx.egraph.find(ite), ctx.egraph.find(b));
    }
}
