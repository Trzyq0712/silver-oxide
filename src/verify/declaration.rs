use std::collections::HashMap;

use crate::vmir::display::VmirDisplay;
use crate::{
    verify::{
        cert::{FunctionCertificate, ResourceCertificate},
        context::VerifyContext,
        error::VerifyError,
        heap::{Chunk, Heap, LocationKind},
        lang::Symbolic,
        viz::Snapshotter,
    },
    vmir::{
        self, Assign, BinOp, Bound, Declaration, Function, HeapInst, HeapVal, Inst, InstKind,
        Literal, MemberId, Method, PathConds, Polarity, PureInst, Resource, ResourceCall, Sign,
        Type, Val,
    },
};

struct EvalState {
    vals: Vec<egg::Id>,
    /// The VMIR `Type` of each `vals` entry, kept in lockstep. The location kind
    /// of an address operand is read straight from here (`loc_kind`) — no e-graph
    /// inference. Params seed the initial slots; every `Pure` inst pushes its type.
    val_types: Vec<Type>,
    heaps: Vec<Heap>,
}

impl EvalState {
    fn new() -> Self {
        Self {
            vals: Vec::new(),
            val_types: Vec::new(),
            heaps: Vec::new(),
        }
    }

    fn with_args(args: Vec<egg::Id>, arg_types: Vec<Type>) -> Self {
        debug_assert_eq!(args.len(), arg_types.len());
        Self {
            vals: args,
            val_types: arg_types,
            heaps: Vec::new(),
        }
    }

    fn get_val(&self, ctx: &mut VerifyContext<'_>, val: &Val) -> egg::Id {
        match val {
            Val::Temp(n) => self.vals[*n],
            Val::Literal(lit) => ctx.add(Symbolic::Lit(lit.clone())),
        }
    }

    /// The location kind of an address operand, from its tracked VMIR type. A
    /// non-`Temp` or non-`Addr`-typed operand has no kind (`None`).
    fn loc_kind(&self, val: &Val) -> Option<LocationKind> {
        match val {
            Val::Temp(n) => LocationKind::from_addr_type(&self.val_types[*n]),
            Val::Literal(_) => None,
        }
    }

    fn push_val(&mut self, id: egg::Id, ty: Type) {
        self.vals.push(id);
        self.val_types.push(ty);
    }
    fn push_heap(&mut self, heap: Heap) {
        self.heaps.push(heap);
    }
}

/// Render a single instruction (method or resource body) for error context.
fn format_inst(
    inst: &Inst,
    decls: &typed_index_collections::TiVec<MemberId, Declaration>,
    interner: &lasso::Rodeo,
    groups: &lasso::Rodeo<lasso::Spur>,
    val_base: usize,
    heap_base: usize,
) -> String {
    VmirDisplay::new(
        (val_base, heap_base, std::slice::from_ref(inst)),
        decls,
        interner,
        groups,
    )
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
        InstKind::Heap(
            HeapInst::Combine { base, .. }
            | HeapInst::Inhale { base, .. }
            | HeapInst::Exhale { base, .. },
        ) => vec![
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
            state
                .loc_kind(loc)
                .and_then(|k| heap.value_at(&k, addr))
                .unwrap_or_else(|| ctx.fresh_symbolic_value(ty.clone()))
        }
        PureInst::FunctionCall(fc) => {
            // A (possibly generic) Silver `function`: `type_args` are the
            // result-type vars, part of the `FuncApp` node identity (discriminant);
            // empty for a monomorphic call. Always heap-free: a heap-dependent
            // function receives its precondition snapshot as an ordinary arg.
            //
            // Just add the uninterpreted application — for abstract, heap-free,
            // and heap-dependent callees alike. A verified callee's definitional
            // equality `f(args) == body` is installed lazily by its own
            // `rewrite::function_rule` (registered into `ctx.axiom_rules` by
            // `assume_axioms` from `ctx.fn_certs`) the next time saturation runs
            // over this occurrence, not eagerly here.
            let args: Vec<egg::Id> = fc.args.iter().map(|v| state.get_val(ctx, v)).collect();
            ctx.add_func_app_id(
                crate::verify::func_registry::func_id_for_member(fc.function),
                fc.type_args.clone().into(),
                ty.clone(),
                args.into(),
            )
        }
        // `Snap` needs the program + certificates; every inst walker intercepts
        // it and dispatches to `eval_snap` before reaching this function.
        PureInst::Snap { .. } => {
            unreachable!("Snap is handled by eval_snap in the inst walkers")
        }
        // perm(loc): permission amount held at `loc` in the given heap.
        PureInst::Perm(hv, loc) => {
            let heap = get_heap(state, hv);
            let addr = state.get_val(ctx, loc);
            state
                .loc_kind(loc)
                .and_then(|k| heap.perm_at(&k, addr))
                .unwrap_or_else(|| zero_real(ctx))
        }
        // Semantic ADT nodes. Each is a `FuncApp` over a verifier-minted **concept**
        // id (one per `(head, variant[, field])`, see `verify::mono`); the ground
        // `type_args` ride in the node's operator identity (the discriminant), so
        // distinct instantiations never merge and the cons/proj/tag reductions fire
        // per concept regardless of instantiation.
        PureInst::AdtCons {
            adt,
            type_args,
            variant,
            args,
        } => {
            let cons = ctx.alloc.cons(*adt, *variant);
            let args: Vec<egg::Id> = args.iter().map(|v| state.get_val(ctx, v)).collect();
            ctx.add_func_app_id(cons, type_args.clone().into(), ty.clone(), args.into())
        }
        PureInst::AdtProj {
            adt,
            type_args,
            variant,
            field,
            base,
        } => {
            let proj = ctx.alloc.proj(*adt, *variant, *field);
            let base = state.get_val(ctx, base);
            ctx.add_func_app_id(proj, type_args.clone().into(), ty.clone(), Box::new([base]))
        }
        PureInst::AdtTag {
            adt,
            type_args,
            base,
        } => {
            let tag = ctx.alloc.tag(*adt);
            let base = state.get_val(ctx, base);
            ctx.add_func_app_id(tag, type_args.clone().into(), Type::Int, Box::new([base]))
        }
    }
}

fn heap_acc(ctx: &mut VerifyContext<'_>, loc: &Val, perm: &Val, state: &EvalState) -> Heap {
    let addr = state.get_val(ctx, loc);
    let perm = state.get_val(ctx, perm);
    // The location kind (group + held value type + bound) comes straight from the
    // address operand's VMIR `Type::Addr` — no e-graph inference.
    let kind = state
        .loc_kind(loc)
        .expect("acc location must be Addr-typed");
    let value = ctx.fresh_symbolic_value(kind.value.clone());
    Heap::empty().with_chunk(&kind, Chunk::new(addr, perm, value))
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
    addr: egg::Id,
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
    let true_ = ctx.true_();
    let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [v0, v1]));
    let antecedents = [(p1_pos, Polarity::Positive), (p0_pos, Polarity::Positive)]
        .into_iter()
        .chain(pc_lits.iter().rev().copied());
    let imp = ctx.implication(eq, antecedents);
    ctx.egraph.union(imp, true_);

    Chunk::new(addr, perm, value)
}

/// A location chunk extracted from a heap for the location axioms: its
/// permission, the location group tag, its argument e-classes, and its bound.
struct LocationChunk {
    perm: egg::Id,
    group: lasso::Spur,
    args: Vec<egg::Id>,
    bound: Bound,
}

/// A predicate's address type `&[name] Snap(id) @ *` — the group is the
/// predicate's interned tag (`Program.groups`), value its snapshot, unbounded.
fn pred_addr_type(program: &vmir::Program, pred_id: MemberId) -> Type {
    let group = program
        .groups
        .get(program.name(pred_id))
        .expect("predicate group tag not registered");
    Type::addr(group, Type::Snap(pred_id), Bound::Unbounded)
}

/// Extract the location chunks of `h`: for each chunk whose canonical address has
/// an `Addr{group,bound,..}` type (recovered by `infer_type`, so **computed**
/// addresses count too), record its perm, group, bound, and — for a direct
/// `@addr` application — its value-arg e-classes (used by the non-aliasing axiom).
fn location_chunks(ctx: &VerifyContext<'_>, h: &Heap) -> Vec<LocationChunk> {
    let mut out = Vec::new();
    for (kind, chunk) in h.entries() {
        // group/bound come straight from the chunk's location kind (VMIR-sourced) —
        // no inference. The value args for non-aliasing are read from the address
        // application node; absent for a computed address (no such node).
        let canon = ctx.egraph.find(chunk.addr);
        let args = ctx.egraph[canon]
            .nodes
            .iter()
            .find_map(|n| match n {
                Symbolic::FuncApp(f, _, args)
                    if matches!(ctx.func_ret_types.get(f), Some(Type::Addr { .. })) =>
                {
                    Some(args.to_vec())
                }
                _ => None,
            })
            .unwrap_or_default();
        out.push(LocationChunk {
            perm: chunk.perm,
            group: kind.group,
            bound: kind.bound.clone(),
            args,
        });
    }
    out
}

/// Emit the location axioms over `h` after a consolidation. Both are e-graph
/// facts the engine *resolves itself* (no Rust-side const-fold queries):
/// - **bound:** a `Bounded(b)` cell holds `perm ≤ b` — `union((b < perm) ?
///   false : true, true)`; a permission folding to `> b` unions `false == true`,
///   making the unit inconsistent so any goal is dischargeable.
/// - **non-aliasing:** two chunks of the *same* bounded location satisfy
///   `(permᵢ + permⱼ > b) ⟹ ¬(args equal)`, encoded as
///   `union(conj, (b < sum) ? false : conj)` where `conj = a0==b0 && a1==b1 …`.
///   When `b < sum` folds true the `ite` collapses `conj` to `false`. For arity
///   1 this is the single-`Eq` collapse (drives `a0 != a1`); for higher arity it
///   sets the whole conjunction false (the de-Morgan disjunction — the e-graph
///   won't pick a branch, SMT does later).
///
/// Unbounded locations (predicates) never participate.
fn assume_location_axioms(ctx: &mut VerifyContext<'_>, h: &Heap) {
    let chunks = location_chunks(ctx, h);
    if chunks.is_empty() {
        return;
    }
    let false_ = ctx.false_();
    let true_ = ctx.true_();

    // Bound: perm ≤ b at each bounded location.
    for c in &chunks {
        let Bound::Bounded(b) = &c.bound else {
            continue;
        };
        let b = ctx.add(Symbolic::Lit(Literal::Real(b.clone())));
        let gt = ctx.add(Symbolic::Binary(BinOp::Lt, [b, c.perm]));
        let le = ctx.add(Symbolic::Ite([gt, false_, true_]));
        ctx.egraph.union(le, true_);
    }

    // Non-aliasing: same bounded location, perms sum > bound ⇒ args differ.
    for i in 0..chunks.len() {
        for j in (i + 1)..chunks.len() {
            if chunks[i].group != chunks[j].group {
                continue;
            }
            let Bound::Bounded(b) = &chunks[i].bound else {
                continue;
            };
            let b = ctx.add(Symbolic::Lit(Literal::Real(b.clone())));
            let sum = ctx.add(Symbolic::Binary(
                BinOp::Plus,
                [chunks[i].perm, chunks[j].perm],
            ));
            let gt = ctx.add(Symbolic::Binary(BinOp::Lt, [b, sum]));
            // Both arg orders (the `!=` goal's `Eq` order is source-dependent).
            for (xs, ys) in [
                (&chunks[i].args, &chunks[j].args),
                (&chunks[j].args, &chunks[i].args),
            ] {
                let conj = conj_args_eq(ctx, xs, ys, true_, false_);
                let imp = ctx.add(Symbolic::Ite([gt, false_, conj]));
                ctx.egraph.union(conj, imp);
            }
        }
    }
    ctx.egraph.rebuild();
}

/// Build `xs0==ys0 && xs1==ys1 && …` as a right-nested `ite(eq, rest, false)`
/// chain (seeded `true`). For a single argument this is `ite(a==b, true, false)`,
/// which `ite-ident` collapses to `a==b`.
fn conj_args_eq(
    ctx: &mut VerifyContext<'_>,
    xs: &[egg::Id],
    ys: &[egg::Id],
    true_: egg::Id,
    false_: egg::Id,
) -> egg::Id {
    let mut acc = true_;
    for k in (0..xs.len()).rev() {
        let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [xs[k], ys[k]]));
        acc = ctx.add(Symbolic::Ite([eq, acc, false_]));
    }
    acc
}

/// Heap addition for a single location chunk of kind `kind`.
fn heap_union(
    ctx: &mut VerifyContext<'_>,
    h1: &Heap,
    kind: &LocationKind,
    chunk2: Chunk,
    pc_lits: &[(egg::Id, Polarity)],
) -> Heap {
    let mut out = h1.clone();
    let addr = ctx.egraph.find(chunk2.addr);
    // Find any congruent chunk already in this group (canonical-address match).
    let existing = out
        .chunks_of(kind)
        .iter()
        .find(|c| ctx.egraph.find(c.addr) == addr)
        .cloned();
    if let Some(existing) = existing {
        // Replace the existing chunk in place (keep its stored address key).
        let merged = merge_chunks(
            ctx,
            existing.addr,
            existing.perm,
            existing.value,
            chunk2.perm,
            chunk2.value,
            pc_lits,
        );
        out = out.with_chunk(kind, merged);
    } else {
        out = out.with_chunk(kind, chunk2);
    }
    assume_location_axioms(ctx, &out);
    out
}

/// Heap subtraction for a single location chunk of kind `kind`.
fn heap_subtract(
    ctx: &mut VerifyContext<'_>,
    h1: &Heap,
    kind: &LocationKind,
    chunk2: Chunk,
    pc_lits: &[(egg::Id, Polarity)],
) -> Result<Heap, VerifyError> {
    let mut out = h1.clone();
    let addr = ctx.egraph.find(chunk2.addr);
    let existing = out
        .chunks_of(kind)
        .iter()
        .find(|c| ctx.egraph.find(c.addr) == addr)
        .cloned();
    let Some(existing) = existing else {
        // No chunk at `addr`. Subtracting a provably-zero permission (e.g. a
        // conditional footprint slot whose guard is false — a nested predicate
        // `b ==> P(..)` with `b` false) is a no-op, so it need not be held.
        let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        let pos = ctx.add(Symbolic::Binary(BinOp::Lt, [zero, chunk2.perm]));
        let false_ = ctx.false_();
        let true_ = ctx.true_();
        let nonpos = ctx.add(Symbolic::Ite([pos, false_, true_]));
        if ctx.prove_under_pc(nonpos, pc_lits) {
            return Ok(out);
        }
        return Err(VerifyError::InsufficientPermission);
    };

    let lt = ctx.add(Symbolic::Binary(BinOp::Lt, [existing.perm, chunk2.perm]));
    let false_ = ctx.false_();
    let true_ = ctx.true_();
    let goal = ctx.add(Symbolic::Ite([lt, false_, true_]));
    if !ctx.prove_under_pc(goal, pc_lits) {
        return Err(VerifyError::InsufficientPermission);
    }

    ctx.egraph.union(existing.value, chunk2.value);

    let remainder = ctx.add(Symbolic::Binary(BinOp::Minus, [existing.perm, chunk2.perm]));
    let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
    let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [remainder, zero]));
    if ctx.prove_under_pc(eq, pc_lits) {
        out = out.without_chunk(kind, existing.addr);
    } else {
        out = out.with_chunk(kind, Chunk::new(existing.addr, remainder, existing.value));
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
        // subtract (Sub) it.
        HeapInst::Combine {
            base,
            sign,
            loc,
            perm,
        } => {
            let base_h = get_heap(state, base);
            let chunk = heap_acc(ctx, loc, perm, state);
            let pc_lits: Vec<(egg::Id, Polarity)> = pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            let (kind, ch) = chunk.entries().next().unwrap();
            let (kind, ch) = (kind.clone(), ch.clone());
            match sign {
                Sign::Add => Ok(heap_union(ctx, &base_h, &kind, ch, &pc_lits)),
                Sign::Sub => heap_subtract(ctx, &base_h, &kind, ch, &pc_lits),
            }
        }
        // Resource inhale/exhale need the program + certificates; method-only.
        HeapInst::Inhale { .. } | HeapInst::Exhale { .. } => Err(VerifyError::Unimplemented(
            "resource inhale/exhale outside method body",
        )),
        // Fold/Unfold need the program + certificates; handled in
        // `eval_method_inst`.
        HeapInst::Fold { .. } | HeapInst::Unfold { .. } => Err(VerifyError::Unimplemented(
            "fold/unfold outside method body",
        )),
        // Snapshot → heap reconstruction needs the program + certificates;
        // handled in `eval_method_inst` (function bodies are walked there).
        HeapInst::FromSnap { .. } => Err(VerifyError::Unimplemented(
            "FromSnap outside a function/method body",
        )),
        // Field assignment `loc := val`: requires write permission at `loc`,
        // then updates the chunk's value (permission unchanged).
        HeapInst::Assign(heap, Assign { loc, val }) => {
            let h = get_heap(state, heap);
            let addr = state.get_val(ctx, loc);
            let new_val = state.get_val(ctx, val);
            let kind = state
                .loc_kind(loc)
                .expect("assign location must be Addr-typed");
            let perm = h.perm_at(&kind, addr).unwrap_or_else(|| zero_real(ctx));
            // SIDECOND: prove `not(perm < 1)` (full/write permission) under pc.
            let pc_lits: Vec<(egg::Id, Polarity)> = pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            let write = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
            let lt = ctx.add(Symbolic::Binary(BinOp::Lt, [perm, write]));
            let false_ = ctx.false_();
            let true_ = ctx.true_();
            let goal = ctx.add(Symbolic::Ite([lt, false_, true_]));
            if !ctx.prove_under_pc(goal, &pc_lits) {
                return Err(VerifyError::InsufficientPermission);
            }
            Ok(h.with_chunk(&kind, Chunk::new(addr, perm, new_val)))
        }
    }
}

/// Evaluate one instruction of a resource body (well-formedness pass). Resource
/// bodies emit `Pure`/`Heap`; `unfold` is the one heap op handled specially
/// (shared with method bodies), the rest go through `eval_heap_inst`. The
/// effectful variants (`Assume`/`Assert`/`Refute`) are not produced here.
fn eval_resource_body_inst(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceCertificate>,
) -> Result<(), VerifyError> {
    match &inst.kind {
        // A heap-dependent function call inside a resource body narrows the
        // body's footprint heap with `Snap` — shared with method bodies.
        InstKind::Pure(ty, PureInst::Snap { .. }) => {
            let id = eval_snap(ctx, program, state, inst, certs)?;
            state.push_val(id, ty.clone());
        }
        InstKind::Pure(ty, pi) => {
            let id = eval_pure_inst(ctx, state, ty, pi);
            state.push_val(id, ty.clone());
        }
        // `unfold` inside a resource body verifies identically to a method
        // body (shared `eval_unfold`); only `Unfold` is emitted here.
        InstKind::Heap(HeapInst::Unfold { .. }) => eval_unfold(ctx, program, state, inst, certs)?,
        // The entry `heap_of req(args), s` of a two-state resource body:
        // reconstruct the pre-state heap from the snapshot parameter (implicitly
        // assuming the precondition resource's boolean).
        InstKind::Heap(HeapInst::FromSnap { .. }) => {
            let heap = eval_from_snap(ctx, program, state, inst, certs)?;
            state.push_heap(heap);
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

/// A grafted resource call: the heap delta, the boolean handle, and the
/// transplanted footprint slots `(perm, value)` in program order.
type GraftedCall = (Heap, egg::Id, Vec<(egg::Id, egg::Id)>);

/// Evaluate a resource invocation as a **reusable proof** by grafting the
/// resource's pre-verified certificate (see [`verify_resource`]) into the
/// caller's e-graph, substituting the formal params for the call args (a
/// two-state resource's pre-state snapshot is an ordinary trailing arg). This
/// transfers every proven merge for free — no re-walk, no re-saturation — and
/// returns `(heap_delta, bool_handle, footprint_slots)`. The *outer* boolean is
/// **not** assumed or asserted here; the caller decides.
fn eval_resource_call(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    caller_state: &EvalState,
    call: &ResourceCall,
    certs: &HashMap<MemberId, ResourceCertificate>,
) -> Result<GraftedCall, VerifyError> {
    let Declaration::Resource(r) = &program.decls[call.resource] else {
        panic!("ResourceCall targets non-Resource declaration");
    };
    if r.body.is_none() {
        panic!("call to abstract resource");
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
        // `Snap` needs the program + certificates (footprint graft), so it is
        // handled here rather than in `eval_pure_inst`.
        InstKind::Pure(ty, PureInst::Snap { .. }) => {
            let id = eval_snap(ctx, program, state, inst, certs)?;
            state.push_val(id, ty.clone());
        }
        InstKind::Pure(ty, pi) => {
            let id = eval_pure_inst(ctx, state, ty, pi);
            state.push_val(id, ty.clone());
        }
        // `base inhale <resource>(args) perm`: graft the resource's certificate,
        // scale its delta by `perm`, union against `base`, and **assume** the
        // resource's boolean. `base exhale ...` subtracts and **asserts** it.
        // A self-framed callee additionally yields its snapshot as a pure `Val`
        // (the pre-state handle a two-state call receives as trailing arg): on
        // inhale the slot values are the grafted delta values; on exhale the
        // subtraction below unions them with the consumed caller chunk values,
        // so the snapshot binds to the real pre-state either way.
        InstKind::Heap(
            hi @ (HeapInst::Inhale { base, call, perm } | HeapInst::Exhale { base, call, perm }),
        ) => {
            let is_inhale = matches!(hi, HeapInst::Inhale { .. });
            let base_h = get_heap(state, base);
            let (delta, bool_id, footprint) = eval_resource_call(ctx, program, state, call, certs)?;
            let scale = state.get_val(ctx, perm);
            let scaled = scale_heap_perm(ctx, &delta, scale);
            let pc_lits: Vec<(egg::Id, Polarity)> = inst
                .pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            let out = if is_inhale {
                let mut h = base_h.clone();
                for (kind, ch) in scaled.entries() {
                    h = heap_union(ctx, &h, kind, ch.clone(), &pc_lits);
                }
                // Guard the assumed bool by `0 < scale`: the resource is inhaled
                // exactly where its scaled permission is positive. An inhale
                // carries no path condition (it is lowered "total", the branch
                // living only in the `c ? 1/1 : 0/1` permission scale), so the
                // permission — not `inst.pc` — is the guard. On the off-branch
                // `scale` folds to `0/1`, `0 < 0` to `false`, and the bool is
                // asserted nowhere.
                let pos = ctx.perm_positive(scale);
                ctx.assume_guarded(bool_id, std::iter::once((pos, Polarity::Positive)));
                h
            } else {
                let mut h = base_h.clone();
                for (kind, ch) in scaled.entries() {
                    h = heap_subtract(ctx, &h, kind, ch.clone(), &pc_lits)?;
                }
                if !ctx.prove_under_pc(bool_id, &pc_lits) {
                    return Err(VerifyError::AssertionFailed);
                }
                h
            };
            state.push_heap(out);
            if let Some(res_id) = hi.snap_yield(&program.decls) {
                let s = snap_of_footprint(ctx, program, res_id, &footprint)?;
                state.push_val(s, Type::Snap(res_id));
            }
        }
        // `fold`: consume the predicate footprint (scaled by `perm`), assert the
        // body's pure facts, and produce a predicate chunk holding the snapshot
        // (`cons`) of the consumed field values.
        InstKind::Heap(HeapInst::Fold { base, call, perm }) => {
            let base_h = get_heap(state, base);
            let args: Vec<egg::Id> = call.args.iter().map(|v| state.get_val(ctx, v)).collect();
            let perm_id = state.get_val(ctx, perm);
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);

            // Consume the footprint from the current heap (reading its values),
            // asserting the predicate body; then place the predicate chunk holding
            // the snapshot of the consumed values.
            let FootprintResult { heap: out, members } = walk_footprint(
                ctx,
                program,
                certs,
                call.resource,
                &args,
                base_h.clone(),
                ValueSource::ReadHeap(base_h),
                Direction::Consume,
                Some(perm_id),
                &pc_lits,
            )?;
            let snap = build_snapshot(ctx, call.resource, members);
            let (pred_kind, pred_addr) = predicate_address(ctx, program, call.resource, &args);
            let out = heap_union(
                ctx,
                &out,
                &pred_kind,
                Chunk::new(pred_addr, perm_id, snap),
                &pc_lits,
            );
            state.push_heap(out);
            ctx.reduce();
        }
        // `unfold`: inverse of fold — consume the predicate chunk, reproduce the
        // footprint (fields recovered by projecting the snapshot), assume the
        // body's pure facts.
        InstKind::Heap(HeapInst::Unfold { .. }) => eval_unfold(ctx, program, state, inst, certs)?,
        // `heap_of R(args), s`: reconstruct a heap from a snapshot (the entry of
        // a heap-dependent function body), assuming the resource bool.
        InstKind::Heap(HeapInst::FromSnap { .. }) => {
            let heap = eval_from_snap(ctx, program, state, inst, certs)?;
            state.push_heap(heap);
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, &inst.pc)?;
            state.push_heap(heap);
        }
        InstKind::Assume(val) => {
            let id = state.get_val(ctx, val);
            // Guard by the path condition: an `assume` inside a branch holds only
            // on that branch (rev to match `implication`'s innermost-first fold).
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
            ctx.assume_guarded(id, pc_lits.iter().rev().copied());
        }
        InstKind::Assert(val) => {
            // TODO(heap-consolidation): `inst.heap` carries the heap this obligation
            // is checked in — once wired, consolidate it (materialise aliasing/
            // perm-sum facts into the e-graph) before `prove_under_pc`. Unused today.
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

/// Where a footprint slot's value comes from (see [`walk_footprint`]).
enum ValueSource {
    /// Read the chunk value at the slot's address from this heap (fresh if
    /// absent). Used by `fold`/`snap`, which read a heap they already hold.
    ReadHeap(Heap),
    /// Recover it from the snapshot `s` as `unwrap(proj_i(s))`. Used by
    /// `unfold`/`from_snap`, which reconstruct the footprint from a snapshot.
    ProjectSnap(egg::Id),
}

/// The direction of a footprint walk: consume a held footprint and **assert** the
/// resource's boolean (`fold`/`snap`), or produce one and **assume** it
/// (`unfold`/`from_snap`).
enum Direction {
    Consume,
    Produce,
}

/// The result of a footprint walk: the accumulator heap after all slot effects,
/// and — for a `Consume` walk — the snapshot members `present ? Some(v) : None`
/// per slot (empty for `Produce`, which builds no snapshot).
struct FootprintResult {
    heap: Heap,
    members: Vec<egg::Id>,
}

/// The single per-slot footprint loop behind `fold`, `unfold`, `snap` and
/// `from_snap`. For each footprint slot of `resource(args)`: graft the slot's
/// `(addr, perm)`, obtain the slot value from `source`, apply the slot's heap
/// effect to the `base` accumulator (subtract for `Consume`, union for
/// `Produce`; permission scaled by `scale` when `Some`), and thread the actual
/// value through `subst` so a value-dependent inner address (e.g. `P(this.next)`)
/// resolves. Finally graft the body boolean and discharge it per `direction`
/// (`Consume` asserts under `pc_lits`, `Produce` assumes it guarded by them).
///
/// The caller owns everything *around* the slots: the predicate-chunk add/remove
/// (bracketing differs — `fold` adds after, `unfold` removes before) and what to
/// do with `heap` (`snap` discards it — functions frame, they don't consume).
#[allow(clippy::too_many_arguments)]
fn walk_footprint(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    certs: &HashMap<MemberId, ResourceCertificate>,
    resource: MemberId,
    args: &[egg::Id],
    base: Heap,
    source: ValueSource,
    direction: Direction,
    scale: Option<egg::Id>,
    pc_lits: &[(egg::Id, Polarity)],
) -> Result<FootprintResult, VerifyError> {
    let vmir::Declaration::Resource(r) = &program.decls[resource] else {
        return Err(VerifyError::DependencyFailed);
    };
    let Some(vmir::Snapshot::Concrete(snap_adt)) = r.derive_snapshot() else {
        return Err(VerifyError::Unimplemented("footprint of abstract resource"));
    };
    let field_types = snap_adt.variants.into_iter().next().unwrap().field_types;
    let cert = certs.get(&resource).ok_or(VerifyError::DependencyFailed)?;

    let mut heap = base;
    let mut values = Vec::with_capacity(cert.footprint.len());
    let mut members = Vec::with_capacity(cert.footprint.len());
    let mut subst = ctx.footprint_param_subst(cert, args);
    for (i, (kind, c_addr, c_perm, c_val)) in cert.footprint.iter().enumerate() {
        let (addr, bperm) = ctx.graft_footprint_slot(cert, *c_addr, *c_perm, &subst);
        // Snapshot fields are `Option[T]`; the slot value has the inner `T`.
        let elem = field_types[i]
            .option_inner()
            .unwrap_or(&field_types[i])
            .clone();
        let value = match &source {
            // Values are read from the *original* heap (aliased slots agree).
            ValueSource::ReadHeap(h) => h
                .entries()
                .find_map(|(_, c)| {
                    (ctx.egraph.find(c.addr) == ctx.egraph.find(addr)).then_some(c.value)
                })
                .unwrap_or_else(|| ctx.fresh_symbolic_value(elem.clone())),
            // `proj_i(s)` recovers the optional member (collapsing to the `cons`
            // argument when `s` is concrete); `unwrap` peels to the field value.
            ValueSource::ProjectSnap(s) => {
                let proj_id = ctx.alloc.proj(resource, 0, i);
                let opt_ty = ctx.alloc.option_type(elem.clone());
                let opt = ctx.add_func_app_id(proj_id, Box::new([]), opt_ty, Box::new([*s]));
                ctx.option_unwrap(elem.clone(), opt)
            }
        };
        // The heap effect uses the (optionally scaled) permission; the snapshot
        // membership discriminant uses the *unscaled* cert perm.
        let p = match scale {
            Some(pm) => ctx.add(Symbolic::Binary(BinOp::Mult, [pm, bperm])),
            None => bperm,
        };
        let chunk = Chunk::new(addr, p, value);
        heap = match direction {
            Direction::Consume => heap_subtract(ctx, &heap, kind, chunk, pc_lits)?,
            Direction::Produce => heap_union(ctx, &heap, kind, chunk, pc_lits),
        };
        if let Direction::Consume = direction {
            let present = ctx.perm_positive(bperm);
            members.push(ctx.option_member(elem, present, value));
        }
        subst.insert(cert.egraph.find(*c_val), value);
        values.push(value);
    }
    let bool_id = ctx.graft_pred_bool(cert, args, &values);
    match direction {
        // The precondition/predicate body must hold over the consumed values.
        Direction::Consume => {
            if !ctx.prove_under_pc(bool_id, pc_lits) {
                return Err(VerifyError::AssertionFailed);
            }
        }
        // The reconstructed body facts hold only where this walk is reached.
        Direction::Produce => {
            ctx.assume_guarded(bool_id, pc_lits.iter().rev().copied());
        }
    }
    Ok(FootprintResult { heap, members })
}

/// The `cons` of a resource's snapshot from its per-slot `members`
/// (`present ? Some(v) : None`). Predicate snapshots are single-variant,
/// non-generic ADTs headed by the resource id.
fn build_snapshot(
    ctx: &mut VerifyContext<'_>,
    resource: MemberId,
    members: Vec<egg::Id>,
) -> egg::Id {
    let cons = ctx.alloc.cons(resource, 0);
    ctx.add_func_app_id(cons, Box::new([]), Type::Snap(resource), members.into())
}

/// A predicate's location kind and address e-class for `args`: the address is an
/// ordinary `FuncApp` to the predicate's own id (its `@addr` function), typed by
/// its recorded `Addr{..}` return type. Shared by `fold` and `unfold`.
fn predicate_address(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    pred: MemberId,
    args: &[egg::Id],
) -> (LocationKind, egg::Id) {
    let addr_ty = pred_addr_type(program, pred);
    let kind = LocationKind::from_addr_type(&addr_ty).expect("predicate address type");
    let addr = ctx.add_func_app_id(
        crate::verify::func_registry::func_id_for_member(pred),
        Box::new([]),
        addr_ty,
        args.into(),
    );
    (kind, addr)
}

/// Evaluate an `unfold`: consume the predicate chunk, reproduce the footprint
/// (fields recovered by projecting the snapshot), assume the body's pure facts.
/// Shared by method bodies and resource bodies; grafts the unfolded predicate's
/// pre-verified certificate (so the predicate must be verified first — a
/// self/mutual `unfolding` cycle is rejected upstream by `analyze`).
fn eval_unfold(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceCertificate>,
) -> Result<(), VerifyError> {
    let InstKind::Heap(HeapInst::Unfold { base, call, perm }) = &inst.kind else {
        unreachable!("eval_unfold called on a non-Unfold instruction");
    };
    let base_h = get_heap(state, base);
    let args: Vec<egg::Id> = call.args.iter().map(|v| state.get_val(ctx, v)).collect();
    let perm_id = state.get_val(ctx, perm);
    let pc_lits = collect_pc_lits(ctx, state, &inst.pc);

    // Consume the predicate chunk, recovering the snapshot `s` it holds.
    let (pred_kind, pred_addr) = predicate_address(ctx, program, call.resource, &args);
    let a = ctx.egraph.find(pred_addr);
    let s = base_h
        .entries()
        .find_map(|(_, c)| (ctx.egraph.find(c.addr) == a).then_some(c.value))
        .ok_or(VerifyError::InsufficientPermission)?;
    let out = heap_subtract(
        ctx,
        &base_h,
        &pred_kind,
        Chunk::new(pred_addr, perm_id, s),
        &pc_lits,
    )?;

    // Reproduce the footprint from `s` (`unwrap(proj_i(s))` per slot), assuming
    // the predicate body. `reduce()` afterward collapses any snapshot tower a
    // repeated fold/unfold round-trip created.
    let FootprintResult { heap: out, .. } = walk_footprint(
        ctx,
        program,
        certs,
        call.resource,
        &args,
        out,
        ValueSource::ProjectSnap(s),
        Direction::Produce,
        Some(perm_id),
        &pc_lits,
    )?;
    state.push_heap(out);
    ctx.reduce();
    Ok(())
}

/// Evaluate a `Snap`: narrow `heap` to the snapshot of the self-framed
/// resource `resource(args)` — the implicit precondition check of a
/// heap-dependent function call. Exhale-shaped but **non-consuming**: footprint
/// sufficiency is proven on a scratch subtraction chain (so aliased slots
/// require their sum) whose result is discarded — functions frame, they don't
/// consume. The resource's boolean is **asserted** over the values read from
/// `heap`, and the snapshot is the `cons` of those values
/// (`present ? Some(v) : None` per slot, as in `fold`). Returns the snapshot
/// e-class; the caller pushes it as the inst's `Val`.
fn eval_snap(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceCertificate>,
) -> Result<egg::Id, VerifyError> {
    let InstKind::Pure(
        _,
        PureInst::Snap {
            resource,
            args,
            heap,
        },
    ) = &inst.kind
    else {
        unreachable!("eval_snap called on a non-Snap instruction");
    };
    let h = get_heap(state, heap);
    let args: Vec<egg::Id> = args.iter().map(|v| state.get_val(ctx, v)).collect();
    let pc_lits = collect_pc_lits(ctx, state, &inst.pc);

    // Non-consuming: the sufficiency subtraction runs on a scratch clone of `h`
    // (so aliased slots require their sum) whose resulting heap is discarded —
    // functions frame, they don't consume. Values are read from `h`; the body
    // boolean is asserted. The snapshot is the `cons` of the per-slot members.
    let FootprintResult { members, .. } = walk_footprint(
        ctx,
        program,
        certs,
        *resource,
        &args,
        h.clone(),
        ValueSource::ReadHeap(h),
        Direction::Consume,
        None,
        &pc_lits,
    )?;
    let s = build_snapshot(ctx, *resource, members);
    ctx.reduce();
    Ok(s)
}

/// Build the snapshot a **self-framed** inhale/exhale yields: the `cons` of
/// `present ? Some(v) : None` per footprint slot, over the grafted
/// `(perm, value)` slot ids returned by [`eval_resource_call`]. Unlike
/// [`eval_snap`] there is no sufficiency check here — the inhale/exhale's own
/// union/subtract accounting already established (and bound) the chunks.
fn snap_of_footprint(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    resource: MemberId,
    footprint: &[(egg::Id, egg::Id)],
) -> Result<egg::Id, VerifyError> {
    let vmir::Declaration::Resource(r) = &program.decls[resource] else {
        return Err(VerifyError::DependencyFailed);
    };
    let Some(vmir::Snapshot::Concrete(snap_adt)) = r.derive_snapshot() else {
        return Err(VerifyError::Unimplemented("snapshot of abstract resource"));
    };
    let field_types = snap_adt.variants.into_iter().next().unwrap().field_types;
    let mut members = Vec::with_capacity(footprint.len());
    for (i, (perm, value)) in footprint.iter().enumerate() {
        let elem = field_types[i]
            .option_inner()
            .unwrap_or(&field_types[i])
            .clone();
        let present = ctx.perm_positive(*perm);
        members.push(ctx.option_member(elem, present, *value));
    }
    let s = build_snapshot(ctx, resource, members);
    ctx.reduce();
    Ok(s)
}

/// Evaluate a `FromSnap`: widen a snapshot value back into a heap — the entry
/// of a heap-dependent function body reconstructing its precondition heap from
/// the snapshot parameter. Inverse of [`eval_snap`], inhale-shaped: one chunk
/// per footprint slot at the grafted address with the footprint permission and
/// value `unwrap(proj_i(s))` (as in `unfold`), and the resource's boolean is
/// **assumed** over the projected values. Returns the reconstructed heap.
fn eval_from_snap(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceCertificate>,
) -> Result<Heap, VerifyError> {
    let InstKind::Heap(HeapInst::FromSnap {
        resource,
        args,
        snap,
    }) = &inst.kind
    else {
        unreachable!("eval_from_snap called on a non-FromSnap instruction");
    };
    let args: Vec<egg::Id> = args.iter().map(|v| state.get_val(ctx, v)).collect();
    let s = state.get_val(ctx, snap);
    let pc_lits = collect_pc_lits(ctx, state, &inst.pc);

    // Reconstruct the precondition heap: produce one chunk per footprint slot
    // valued `unwrap(proj_i(s))` into the empty heap, assuming the resource body
    // (guarded by the path condition — a `FromSnap` may sit under a branch).
    let FootprintResult { heap: out, .. } = walk_footprint(
        ctx,
        program,
        certs,
        *resource,
        &args,
        Heap::empty(),
        ValueSource::ProjectSnap(s),
        Direction::Produce,
        None,
        &pc_lits,
    )?;
    ctx.reduce();
    Ok(out)
}

/// Scale every chunk's permission in `h` by `scale` (`perm := scale * perm`),
/// leaving values untouched. For the common `scale = 1` case the `1 * x → x`
/// rewrite folds the multiply away.
fn scale_heap_perm(ctx: &mut VerifyContext<'_>, h: &Heap, scale: egg::Id) -> Heap {
    let mut out = Heap::empty();
    let entries: Vec<(LocationKind, Chunk)> =
        h.entries().map(|(k, c)| (k.clone(), c.clone())).collect();
    for (kind, chunk) in entries {
        let perm = ctx.add(Symbolic::Binary(BinOp::Mult, [scale, chunk.perm]));
        out = out.with_chunk(&kind, Chunk::new(chunk.addr, perm, chunk.value));
    }
    out
}

/// Axiomatize the state: make every domain axiom's fact available to the unit
/// about to be verified. A **ground** axiom (`ty_params == 0`) is evaluated
/// into the e-graph and its boolean merged with `true` up front; a **generic**
/// one becomes a lazy-instantiation rule (see `rewrite::axiom_rule`) chained
/// into this context's saturations, firing on each ground application of its
/// trigger. Axiom bodies are trusted — no obligations (div-by-zero, deref
/// permission) are checked on them.
///
/// Invariant: the eager ground-axiom evaluation below only ever sees **nullary**
/// quantifier occurrences — axioms are closed and `let` is rejected in pure
/// lowering, so an axiom's top-level `forall`s capture nothing. Occurrences
/// *with* capture arguments enter the e-graph when an outer quantifier
/// instance's body is built (`rewrite::build_instance`), or as ordinary
/// `FuncApp` evaluation of a hosting method/resource body (v3: `forall`s in
/// method statements and contracts capture enclosing params/locals; those
/// bodies are evaluated per unit, never eagerly here).
fn assume_axioms(ctx: &mut VerifyContext<'_>, program: &vmir::Program) -> Result<(), VerifyError> {
    for (id, decl) in program.decls.iter_enumerated() {
        // A pure `forall` becomes a value-σ lazy-instantiation rule, chained
        // into every saturation (like generic axioms). Its body is never
        // verified; instantiation adds a guarded clause per ground trigger.
        if let vmir::Declaration::Quantifier(q) = decl {
            let prepared = prepare_quantifier(ctx.alloc, id, q)?;
            let name = ctx.interner.resolve(&q.name).to_string();
            ctx.axiom_rules
                .push(crate::verify::rewrite::quantifier_rule(&name, prepared));
            continue;
        }
        let vmir::Declaration::Axiom(ax) = decl else {
            continue;
        };
        if ax.ty_params.count() == 0 {
            let mut state = EvalState::new();
            for inst in &ax.body.insts {
                match &inst.kind {
                    InstKind::Pure(ty, pi) => {
                        let id = eval_pure_inst(ctx, &state, ty, pi);
                        state.push_val(id, ty.clone());
                    }
                    InstKind::Assume(val) => {
                        let id = state.get_val(ctx, val);
                        let true_ = ctx.true_();
                        ctx.egraph.union(id, true_);
                        ctx.egraph.rebuild();
                    }
                    // An axiom body is never verified — a stray obligation
                    // (there are none today: callees are precondition-free)
                    // would be skipped, and heap insts cannot occur.
                    InstKind::Assert(_) => {}
                    _ => return Err(VerifyError::Unimplemented("non-pure inst in axiom body")),
                }
            }
            let res = state.get_val(ctx, &ax.body.res);
            let true_ = ctx.true_();
            ctx.egraph.union(res, true_);
            ctx.egraph.rebuild();
        } else {
            let prepared = prepare_axiom(ctx.alloc, ax)?;
            let name = ax
                .name
                .map(|n| ctx.interner.resolve(&n).to_string())
                .unwrap_or_else(|| "anon".to_string());
            ctx.axiom_rules
                .push(crate::verify::rewrite::axiom_rule(&name, prepared));
        }
    }
    // One lazy unfold rule per already-verified function certificate: `analyze`
    // guarantees a function only ever calls functions verified earlier (it
    // rejects (mutual) recursion as a dependency cycle), so every function this
    // unit could reference already has a cert in `fn_certs` by the time its
    // ctx is set up here — same guarantee the driver's topological order
    // (`mod.rs`) already relies on. Each rule transplants the cert's raw body
    // lazily, the moment a `FuncApp(f, ..)` occurrence is seen during
    // saturation (see `rewrite::function_rule`), instead of eagerly grafting
    // it once at translation-walk time.
    if let Some(fn_certs) = ctx.fn_certs {
        let fresh_counter = ctx.fresh_counter_handle();
        for (&id, cert) in fn_certs.iter() {
            let name = ctx.member_name(id);
            let func = crate::verify::func_registry::func_id_for_member(id);
            ctx.axiom_rules.push(crate::verify::rewrite::function_rule(
                &name,
                func,
                std::sync::Arc::clone(cert),
                std::sync::Arc::clone(&fresh_counter),
            ));
        }
    }
    Ok(())
}

/// Resolve a generic axiom's body into registry-level pure steps (every callee
/// down to its verifier `FuncId`) plus its trigger, ready for the applier —
/// which has no registry access at rule-application time.
fn prepare_axiom(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    ax: &vmir::Axiom,
) -> Result<crate::verify::rewrite::PreparedAxiom, VerifyError> {
    use crate::verify::rewrite::PreparedAxiom;
    let trigger = ax
        .covering_trigger()
        .ok_or(VerifyError::Unimplemented("generic axiom without trigger"))?;
    let trigger_func = crate::verify::func_registry::func_id_for_member(trigger.function);
    let trigger_type_args = trigger.type_args.clone();

    let insts = prepare_body(alloc, &ax.body.insts)?;
    Ok(PreparedAxiom {
        n_params: ax.ty_params.count(),
        trigger_func,
        trigger_type_args,
        insts,
        res: ax.body.res.clone(),
    })
}

/// Resolve a pure `forall` into a [`PreparedQuantifier`]: its body as
/// registry-level pure steps, its boolean result, its occurrence id and
/// capture-parameter arity, and its trigger (function + positional
/// bound/capture map). Instantiation pairs each ground occurrence with the
/// bound-variable σ read off ground applications of the trigger.
fn prepare_quantifier(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    id: vmir::MemberId,
    q: &vmir::Quantifier,
) -> Result<crate::verify::rewrite::PreparedQuantifier, VerifyError> {
    use crate::verify::rewrite::PreparedQuantifier;
    let insts = prepare_body(alloc, &q.body.insts)?;
    Ok(PreparedQuantifier {
        quant_func: crate::verify::func_registry::func_id_for_member(id),
        n_caps: q.params.len(),
        n_bound: q.bound.len(),
        trigger_func: crate::verify::func_registry::func_id_for_member(q.trigger.function),
        trig_args: q.trigger.args.clone(),
        insts,
        res: q.body.res.clone(),
    })
}

/// Lower an axiom/quantifier body's inst stream into registry-resolved pure
/// steps (every callee down to its verifier `FuncId`), ready for the applier —
/// which has no registry access at rule-application time. Shared by
/// [`prepare_axiom`] and [`prepare_quantifier`].
fn prepare_body(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    insts: &[vmir::Inst],
) -> Result<Vec<crate::verify::rewrite::AxiomInst>, VerifyError> {
    use crate::verify::rewrite::{AxiomInst, AxiomPure};
    let mut out = Vec::with_capacity(insts.len());
    for inst in insts {
        let prepared = match &inst.kind {
            InstKind::Pure(_, pi) => AxiomInst::Val(match pi {
                PureInst::Binary(op, l, r) => AxiomPure::Binary(*op, l.clone(), r.clone()),
                PureInst::Ternary(c, t, e) => AxiomPure::Ternary(c.clone(), t.clone(), e.clone()),
                PureInst::RealCast(v) => AxiomPure::RealCast(v.clone()),
                PureInst::FunctionCall(fc) => AxiomPure::App {
                    func: crate::verify::func_registry::func_id_for_member(fc.function),
                    type_args: fc.type_args.clone(),
                    args: fc.args.iter().cloned().collect(),
                },
                PureInst::AdtCons {
                    adt,
                    type_args,
                    variant,
                    args,
                } => AxiomPure::App {
                    func: alloc.cons(*adt, *variant),
                    type_args: type_args.clone(),
                    args: args.clone(),
                },
                PureInst::AdtProj {
                    adt,
                    type_args,
                    variant,
                    field,
                    base,
                } => AxiomPure::App {
                    func: alloc.proj(*adt, *variant, *field),
                    type_args: type_args.clone(),
                    args: vec![base.clone()],
                },
                PureInst::AdtTag {
                    adt,
                    type_args,
                    base,
                } => AxiomPure::App {
                    func: alloc.tag(*adt),
                    type_args: type_args.clone(),
                    args: vec![base.clone()],
                },
                PureInst::Fresh
                | PureInst::Deref(..)
                | PureInst::Perm(..)
                | PureInst::Snap { .. } => {
                    return Err(VerifyError::Unimplemented("impure inst in axiom body"));
                }
            }),
            InstKind::Assume(v) => AxiomInst::Assume(v.clone()),
            // Never verified; nothing to record.
            InstKind::Assert(_) => continue,
            _ => return Err(VerifyError::Unimplemented("non-pure inst in axiom body")),
        };
        out.push(prepared);
    }
    Ok(out)
}

/// Per-instruction evaluator: the shared signature of [`eval_method_inst`] and
/// [`eval_resource_body_inst`], so [`walk_body`] can be parameterized by which
/// one the body kind uses.
type EvalFn = fn(
    &mut VerifyContext<'_>,
    &vmir::Program,
    &mut EvalState,
    &Inst,
    &HashMap<MemberId, ResourceCertificate>,
) -> Result<(), VerifyError>;

/// The single body-walk shared by all three drivers: for each instruction,
/// discharge its side-condition [`inst_obligations`] under the path condition,
/// then evaluate it, snapshotting for the visualizer throughout. Keeping this in
/// one place is what makes an obligation added to `inst_obligations` impossible
/// to skip in one driver (the `5aad7bc` division-check bug: the check existed but
/// was wired into only one of three near-identical copies of this loop).
///
/// `eval` selects the per-inst semantics (method/function vs resource body).
/// `footprint_ops`, when `Some`, collects each `acc`'s `(loc, perm)` operand in
/// body order — the resource driver's one extra responsibility (drives the
/// fold/unfold snapshot layout); `None` for method and function bodies.
#[allow(clippy::too_many_arguments)]
fn walk_body(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    snap: &mut Snapshotter,
    insts: &[Inst],
    certs: &HashMap<MemberId, ResourceCertificate>,
    eval: EvalFn,
    mut footprint_ops: Option<&mut Vec<(Val, Val)>>,
) -> Result<(), VerifyError> {
    for inst in insts {
        if let (Some(ops), InstKind::Heap(HeapInst::Combine { loc, perm, .. })) =
            (&mut footprint_ops, &inst.kind)
        {
            ops.push((loc.clone(), perm.clone()));
        }
        let vals_before = state.vals.len();
        let heaps_before = state.heaps.len();
        let inst_text = format_inst(
            inst,
            &program.decls,
            &program.interner,
            &program.groups,
            vals_before,
            heaps_before,
        );
        let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
        for (goal, err) in inst_obligations(ctx, state, &inst.kind) {
            if !ctx.prove_under_pc(goal, &pc_lits) {
                return Err(err.with_inst(inst_text.clone()));
            }
        }
        if let Err(err) = eval(ctx, program, state, inst, certs) {
            return Err(err.with_inst(inst_text));
        }
        let highlight = (state.vals.len() > vals_before).then(|| state.vals[state.vals.len() - 1]);
        let heaps = display_heaps(state, &inst.kind, heaps_before);
        snap.snapshot(ctx, &heaps, &inst_text, highlight);
    }
    Ok(())
}

pub(crate) fn verify_method(
    program: &vmir::Program,
    method_name: &str,
    method: &Method,
    certs: &HashMap<MemberId, ResourceCertificate>,
    fn_certs: &HashMap<MemberId, std::sync::Arc<FunctionCertificate>>,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> Result<(), VerifyError> {
    let mut ctx = VerifyContext::new(&program.interner, &program.decls, &program.groups, alloc);
    ctx.fn_certs = Some(fn_certs);
    assume_axioms(&mut ctx, program)?;
    let mut state = EvalState::new();
    let mut snap = Snapshotter::from_env(method_name);

    snap.snapshot(&ctx, &[], "init", None);
    walk_body(
        &mut ctx,
        program,
        &mut state,
        &mut snap,
        &method.insts,
        certs,
        eval_method_inst,
        None,
    )
}

/// Verify a resource self-contained: run its body in a fresh egraph with fresh
/// symbolic params (a two-state resource's pre-state snapshot is an ordinary
/// trailing param), discharging each instruction's side-condition obligations
/// under its path condition. Abstract resources have nothing to check. This
/// establishes well-formedness **once**; method call sites reuse it without
/// re-checking (see [`eval_resource_call`]).
pub(crate) fn verify_resource(
    program: &vmir::Program,
    resource_name: &str,
    resource: &Resource,
    certs: &HashMap<MemberId, ResourceCertificate>,
    fn_certs: &HashMap<MemberId, std::sync::Arc<FunctionCertificate>>,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> Result<Option<ResourceCertificate>, VerifyError> {
    let Some(body) = resource.body.as_ref() else {
        // Abstract resource: nothing to prove, no certificate.
        return Ok(None);
    };

    let mut ctx = VerifyContext::new(&program.interner, &program.decls, &program.groups, alloc);
    ctx.fn_certs = Some(fn_certs);
    assume_axioms(&mut ctx, program)?;
    let params: Vec<egg::Id> = resource
        .params
        .iter()
        .map(|ty| ctx.fresh_symbolic_value(ty.clone()))
        .collect();
    // A two-state (`Ctx`) resource needs no special seeding: its pre-state
    // arrives as the trailing snapshot parameter (a fresh symbolic like any
    // other param) and its body's entry `FromSnap` reconstructs the pre-state
    // heap, implicitly assuming the precondition resource's boolean.
    let mut state = EvalState::with_args(params.clone(), resource.params.clone());

    let mut snap = Snapshotter::from_env(resource_name);
    snap.snapshot(&ctx, &[], "init", None);

    // Ordered per-acc footprint operands `(loc, perm)`, in body order — one per
    // syntactic `acc` (location target), kept unmerged for the fold/unfold
    // snapshot layout (the merged `delta` below is for inhale/exhale). Collected
    // by `walk_body` as it passes each `Combine`.
    let mut footprint_ops: Vec<(Val, Val)> = Vec::new();

    walk_body(
        &mut ctx,
        program,
        &mut state,
        &mut snap,
        &body.insts,
        certs,
        eval_resource_body_inst,
        Some(&mut footprint_ops),
    )?;

    // Saturate so the certificate carries every proven merge, then snapshot the
    // result roots (canonicalized) for grafting at call sites.
    ctx.saturate();
    let delta_heap = get_heap(&state, &body.res.0);
    // Each delta chunk keeps its `LocationKind` (VMIR-sourced) so grafting regroups
    // without inference.
    let delta: Vec<(LocationKind, egg::Id, egg::Id, egg::Id)> = delta_heap
        .entries()
        .map(|(kind, chunk)| {
            (
                kind.clone(),
                ctx.egraph.find(chunk.addr),
                ctx.egraph.find(chunk.perm),
                ctx.egraph.find(chunk.value),
            )
        })
        .collect();
    // Unmerged, program-ordered footprint: each acc's `(kind, addr, perm)` with the
    // *merged* chunk value at that address (so aliased slots stay separate yet
    // share their value). Drives the fold/unfold snapshot layout.
    let footprint: Vec<(LocationKind, egg::Id, egg::Id, egg::Id)> = footprint_ops
        .iter()
        .map(|(loc, perm)| {
            let kind = state
                .loc_kind(loc)
                .expect("footprint location must be Addr-typed");
            let addr = state.get_val(&mut ctx, loc);
            let addr = ctx.egraph.find(addr);
            let perm = state.get_val(&mut ctx, perm);
            let perm = ctx.egraph.find(perm);
            let value = delta_heap
                .entries()
                .find_map(|(_, c)| {
                    (ctx.egraph.find(c.addr) == addr).then(|| ctx.egraph.find(c.value))
                })
                .unwrap_or_else(|| ctx.fresh_symbolic_value(Type::Int));
            (kind, addr, perm, value)
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

/// Verify a non-recursive function: walk its body in a fresh egraph with fresh
/// symbolic params (`Val::Temp(0..n_params)`), discharging the stitched
/// entry-`assume f#requires` contract instruction, then snapshot the
/// (unsaturated) result e-class into a [`FunctionCertificate`] for other units
/// to lazily unfold at call sites (see `rewrite::function_rule`). Abstract
/// functions (no body) have nothing to verify.
///
/// The certificate is captured **without** an extra final `ctx.saturate()` —
/// only the ordinary per-inst walk's own resolution, so the body's literal
/// shape survives for pattern-triggered rules (quantifier/axiom instantiation,
/// keyed on `FuncApp` occurrences) to still see at unfold time, rather than
/// whatever structural simplifications a pre-emptive saturation would have
/// baked in.
///
/// A **heap-dependent** function's snapshot parameter seeds like any other param
/// (a fresh symbolic of `Type::Snap(req)`); its entry `FromSnap` reconstructs the
/// precondition heap `H(s)` and each body `Deref` congruence-resolves against
/// those chunks (`unwrap(proj_i(s))`). By the time this walk finishes, the
/// body's result e-class is already a pure symbolic term over the params
/// (including the snapshot param) regardless of heap-dependence — there is no
/// `Heap`/`HeapVal` node in the `Symbolic` e-graph language, only ordinary
/// `FuncApp`/`Ite`/`Binary` terms — so heap-free and heap-dependent functions
/// are captured and consumed identically; no special-casing needed here.
///
/// Callees — including the function's own `f#requires`/`f#ensures` contract
/// functions — are ordinary `Function` decls verified earlier in dependency
/// order, so their certificates are already in `fn_certs`, and `assume_axioms`
/// (called at the top of this function's own `ctx` setup) has already
/// installed their unfold rules — saturation (triggered constantly via
/// `prove_under_pc`) discharges the contract obligations lazily as needed.
pub(crate) fn verify_function(
    program: &vmir::Program,
    function_name: &str,
    function: &Function,
    certs: &HashMap<MemberId, ResourceCertificate>,
    fn_certs: &HashMap<MemberId, std::sync::Arc<FunctionCertificate>>,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> Result<Option<std::sync::Arc<FunctionCertificate>>, VerifyError> {
    let Some(body) = function.body.as_ref() else {
        // Abstract/uninterpreted function: no body to verify, no certificate.
        return Ok(None);
    };

    let mut ctx = VerifyContext::new(&program.interner, &program.decls, &program.groups, alloc);
    ctx.fn_certs = Some(fn_certs);
    assume_axioms(&mut ctx, program)?;
    // Params seed the initial `Val::Temp(0..n_params)` slots (heap-free: no ctx heap).
    let params: Vec<egg::Id> = function
        .params
        .iter()
        .map(|ty| ctx.fresh_symbolic_value(ty.clone()))
        .collect();
    let param_types: Vec<Type> = function.params.iter().cloned().collect();
    let mut state = EvalState::with_args(params.clone(), param_types);

    let mut snap = Snapshotter::from_env(function_name);
    snap.snapshot(&ctx, &[], "init", None);
    // The method-body eval path handles every inst a function body can contain
    // (pure ops, the entry/exit `assume`/`assert`, and `Snap`/`FromSnap` for
    // heap-dependent functions).
    walk_body(
        &mut ctx,
        program,
        &mut state,
        &mut snap,
        &body.insts,
        certs,
        eval_method_inst,
        None,
    )?;

    // No extra saturation here (see the doc comment above) — snapshot the
    // canonicalized result/param roots as they stand after the ordinary walk.
    let result = state.get_val(&mut ctx, &body.res);
    let result = ctx.egraph.find(result);
    let params = params.iter().map(|&p| ctx.egraph.find(p)).collect();
    Ok(Some(std::sync::Arc::new(FunctionCertificate {
        egraph: ctx.egraph.clone(),
        fresh_types: ctx.fresh_types.clone(),
        func_ret_types: ctx.func_ret_types.clone(),
        params,
        result,
    })))
}

/// Proof obligations implied by an instruction's kind, as `(goal, error)` pairs
/// that must each be proven `true` under the instruction's path condition. A
/// `Deref` requires a positive permission for the location it reads; `acc`
/// requires a non-negative permission; division requires a non-zero divisor.
///
/// This is the **single** source of per-instruction obligations: every body
/// driver (`verify_method`, `verify_resource`, `verify_function`) discharges
/// exactly this list, so an obligation added here is checked everywhere.
fn inst_obligations(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    kind: &InstKind,
) -> Vec<(egg::Id, VerifyError)> {
    match kind {
        // `0 < perm(heap, loc)` — the location must be framed by the heap being
        // read. In a function body that heap is the one the entry `FromSnap`
        // reconstructs from the snapshot parameter, so this failing means a read
        // outside the declared precondition.
        InstKind::Pure(_, PureInst::Deref(heap, loc)) => {
            let addr = state.get_val(ctx, loc);
            let perm = state
                .loc_kind(loc)
                .and_then(|k| get_heap(state, heap).perm_at(&k, addr))
                .unwrap_or_else(|| zero_real(ctx));
            let zero = zero_real(ctx);
            let goal = ctx.add(Symbolic::Binary(BinOp::Lt, [zero, perm]));
            vec![(goal, VerifyError::InsufficientPermission)]
        }
        // `not(perm < 0)` desugared to an `Ite`. Applies to a location combine
        // and to a resource inhale/exhale (their permission scale must be ≥ 0).
        InstKind::Heap(
            HeapInst::Combine { perm, .. }
            | HeapInst::Inhale { perm, .. }
            | HeapInst::Exhale { perm, .. },
        ) => {
            let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
            let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
            let perm = state.get_val(ctx, perm);
            let zero = zero_real(ctx);
            let lt = ctx.add(Symbolic::Binary(BinOp::Lt, [perm, zero]));
            let goal = ctx.add(Symbolic::Ite([lt, false_, true_]));
            vec![(
                goal,
                VerifyError::SideCondition("permission may be negative"),
            )]
        }
        // `not(divisor == 0)` desugared to an `Ite`. The divisor is homogeneous
        // with the result (casts), so the VMIR result type gives the zero's type.
        InstKind::Pure(ty, PureInst::Binary(BinOp::Div, _, r)) => {
            let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
            let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
            let rv = state.get_val(ctx, r);
            let zero = zero_of(ctx, ty);
            let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [rv, zero]));
            let goal = ctx.add(Symbolic::Ite([eq, false_, true_]));
            vec![(goal, VerifyError::SideCondition("divisor may be zero"))]
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

    fn fresh_ctx<'a>(interner: &'a lasso::Rodeo) -> VerifyContext<'a> {
        // Leak a `'static` empty allocator, names table, and group interner so the
        // returned context can borrow them.
        let alloc: &'static mut _ =
            Box::leak(Box::new(crate::verify::func_registry::FuncRegistry::empty()));
        let decls: &'static _ = Box::leak(Box::new(typed_index_collections::TiVec::<
            vmir::MemberId,
            vmir::Declaration,
        >::new()));
        let groups: &'static _ = Box::leak(Box::new(lasso::Rodeo::<lasso::Spur>::new()));
        VerifyContext::new(interner, decls, groups, alloc)
    }

    fn real(ctx: &mut VerifyContext<'_>, n: i64, d: i64) -> egg::Id {
        ctx.add(Symbolic::Lit(Literal::Real(num::BigRational::new(
            num::BigInt::from(n),
            num::BigInt::from(d),
        ))))
    }

    /// An **unbounded** test location kind — like a predicate, it triggers no
    /// bound/non-aliasing axioms, so the merge/subtract unit tests exercise the
    /// chunk accounting in isolation (as the old non-`Addr` test addresses did).
    fn test_kind() -> LocationKind {
        LocationKind {
            group: <lasso::Spur as lasso::Key>::try_from_usize(0).unwrap(),
            value: Type::Int,
            bound: Bound::Unbounded,
        }
    }

    // A multi-arg bounded location (not Viper-reachable; only via direct VMIR):
    // two chunks of the same location whose perms sum > bound, with all args
    // forced equal, must contradict (the conjunction of arg-equalities collapses
    // to false against the assumed-true equalities).
    #[test]
    fn multiarg_location_nonaliasing_all_args_equal_is_inconsistent() {
        let interner = lasso::Rodeo::new();
        let decls = typed_index_collections::TiVec::<vmir::MemberId, vmir::Declaration>::new();
        let mut groups = lasso::Rodeo::<lasso::Spur>::new();
        let g = groups.get_or_intern("g");
        let mut alloc = crate::verify::func_registry::FuncRegistry::empty();
        let mut ctx = VerifyContext::new(&interner, &decls, &groups, &mut alloc);

        // A 2-arg bounded address group `g` of held type `Int`, cap `1/1`. The
        // address is an ordinary `FuncApp` to the group's address function
        // (`FuncId(0)` here); its `Addr{..}` return type is recorded in
        // `func_ret_types` (recovered by `location_chunks`).
        let addr_ty = Type::addr(
            g,
            Type::Int,
            Bound::Bounded(num::BigRational::from(num::BigInt::from(1))),
        );
        let addr_fn = crate::verify::lang::FuncId(0);
        let (x0, y0) = (ctx.add(Symbolic::Fresh(0)), ctx.add(Symbolic::Fresh(1)));
        let (x1, y1) = (ctx.add(Symbolic::Fresh(2)), ctx.add(Symbolic::Fresh(3)));
        let a0 = ctx.add_func_app_id(addr_fn, Box::new([]), addr_ty.clone(), Box::new([x0, y0]));
        let a1 = ctx.add_func_app_id(addr_fn, Box::new([]), addr_ty.clone(), Box::new([x1, y1]));
        let k = LocationKind::from_addr_type(&addr_ty).unwrap();
        let (v0, v1) = (ctx.add(Symbolic::Fresh(4)), ctx.add(Symbolic::Fresh(5)));
        let (p0, p1) = (real(&mut ctx, 3, 4), real(&mut ctx, 1, 2)); // sum 5/4 > 1
        let heap = Heap::empty()
            .with_chunk(&k, Chunk::new(a0, p0, v0))
            .with_chunk(&k, Chunk::new(a1, p1, v1));

        // Assume both argument pairs are equal: x0==x1, y0==y1.
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        for (a, b) in [(x0, x1), (y0, y1)] {
            let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [a, b]));
            ctx.egraph.union(eq, true_);
        }
        ctx.egraph.rebuild();

        assume_location_axioms(&mut ctx, &heap);
        ctx.saturate();
        assert!(
            ctx.is_inconsistent(),
            "holding 5/4 across a 2-arg location with all args equal must contradict"
        );
    }

    #[test]
    fn heap_union_merges_egg_equivalent_addresses() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p1, v1));
        ctx.egraph.union(a, b);
        ctx.egraph.rebuild();

        let merged = heap_union(&mut ctx, &h1, &test_kind(), Chunk::new(b, p2, v2), &[]);

        let canon = ctx.egraph.find(a);
        let chunk = merged
            .chunk(&test_kind(), canon)
            .expect("merged chunk missing");

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
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p0, v0));
        let merged = heap_union(&mut ctx, &h1, &test_kind(), Chunk::new(a, p1, v1), &[]);
        let chunk = merged
            .chunk(&test_kind(), ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();

        // p0 = 0 → asymmetric ternary picks the active half v1; no fusion.
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v1));
        assert_ne!(ctx.egraph.find(v0), ctx.egraph.find(v1));
    }

    #[test]
    fn merge_both_active_fuses_values() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p0, v0));
        let merged = heap_union(&mut ctx, &h1, &test_kind(), Chunk::new(a, p1, v1), &[]);
        let chunk = merged
            .chunk(&test_kind(), ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();

        // Both fractions positive → agreement axiom fuses the symbolic values.
        assert_eq!(ctx.egraph.find(v0), ctx.egraph.find(v1));
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v0));
    }

    #[test]
    fn merge_under_false_pc_blocks_fusion() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let false_lit = ctx.add(Symbolic::Lit(Literal::Bool(false)));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p0, v0));
        let merged = heap_union(
            &mut ctx,
            &h1,
            &test_kind(),
            Chunk::new(a, p1, v1),
            &[(false_lit, Polarity::Positive)],
        );
        let chunk = merged
            .chunk(&test_kind(), ctx.egraph.find(a))
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
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let true_lit = ctx.add(Symbolic::Lit(Literal::Bool(true)));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p0, v0));
        let merged = heap_union(
            &mut ctx,
            &h1,
            &test_kind(),
            Chunk::new(a, p1, v1),
            &[(true_lit, Polarity::Positive)],
        );
        let _chunk = merged
            .chunk(&test_kind(), ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();

        // PC literal is `true` + both fractions positive → agreement fires.
        assert_eq!(ctx.egraph.find(v0), ctx.egraph.find(v1));
    }

    #[test]
    fn prove_under_empty_pc_proves_known_goal() {
        let interner = lasso::Rodeo::new();
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
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        // A free boolean never driven to `true` is not provable.
        let g = ctx.add(Symbolic::Fresh(0));
        assert!(!ctx.prove_under_pc(g, &[]));
    }

    #[test]
    fn prove_under_false_pc_is_vacuous() {
        let interner = lasso::Rodeo::new();
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
        let interner = lasso::Rodeo::new();
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
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p_have = ctx.add(Symbolic::Fresh(1));
        let p_take = ctx.add(Symbolic::Fresh(2));
        let v1 = ctx.add(Symbolic::Fresh(3));
        let v2 = ctx.add(Symbolic::Fresh(4));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p_have, v1));
        // Symbolic perms → `have >= take` not provable by equality saturation.
        let err = heap_subtract(&mut ctx, &h1, &test_kind(), Chunk::new(a, p_take, v2), &[])
            .err()
            .expect("symbolic-perm exhale must fail without a proof");
        assert!(matches!(
            err.root_cause(),
            VerifyError::InsufficientPermission
        ));
    }

    #[test]
    fn heap_subtract_canonical_match() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p2, v1));
        ctx.egraph.union(a, b);
        ctx.egraph.rebuild();

        let result = heap_subtract(&mut ctx, &h1, &test_kind(), Chunk::new(b, p1, v2), &[])
            .expect("subtract should succeed");

        let canon = ctx.egraph.find(a);
        let chunk = result
            .chunk(&test_kind(), canon)
            .expect("result chunk missing");
        let expected_perm = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        ctx.egraph.rebuild();
        assert_eq!(ctx.egraph.find(chunk.perm), ctx.egraph.find(expected_perm));
        assert_eq!(ctx.egraph.find(v1), ctx.egraph.find(v2));
    }

    #[test]
    fn heap_subtract_exact_match_drops_chunk() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p1, v1));
        let result = heap_subtract(&mut ctx, &h1, &test_kind(), Chunk::new(a, p1, v2), &[])
            .expect("subtract should succeed");

        let canon = ctx.egraph.find(a);
        assert!(
            result.chunk(&test_kind(), canon).is_none(),
            "zero-perm chunk must be dropped"
        );
    }

    #[test]
    fn heap_subtract_over_consume_fails() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p1, v1));
        let err = heap_subtract(&mut ctx, &h1, &test_kind(), Chunk::new(a, p2, v2), &[])
            .err()
            .expect("over-consumption must fail");
        assert!(matches!(
            err.root_cause(),
            VerifyError::InsufficientPermission
        ));
    }

    #[test]
    fn heap_subtract_missing_addr_fails() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));

        let h1 = Heap::empty();
        let err = heap_subtract(&mut ctx, &h1, &test_kind(), Chunk::new(a, p1, v1), &[])
            .err()
            .expect("subtract from empty must fail");
        assert!(matches!(
            err.root_cause(),
            VerifyError::InsufficientPermission
        ));
    }

    #[test]
    fn const_fold_folds_subtraction() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let one = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let diff = ctx.add(Symbolic::Binary(BinOp::Minus, [one, one]));
        ctx.egraph.rebuild();

        let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        assert_eq!(ctx.egraph.find(diff), ctx.egraph.find(zero));
    }

    #[test]
    fn const_fold_folds_ternary() {
        let interner = lasso::Rodeo::new();
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
        let interner = lasso::Rodeo::new();
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
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let x = ctx.add(Symbolic::Fresh(0));
        let zero = ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(0))));
        let sum = ctx.add(Symbolic::Binary(BinOp::Plus, [x, zero]));
        ctx.saturate();

        assert_eq!(ctx.egraph.find(sum), ctx.egraph.find(x));
    }

    #[test]
    fn rewrite_add_zero_real_commuted() {
        let interner = lasso::Rodeo::new();
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
        let interner = lasso::Rodeo::new();
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
        let interner = lasso::Rodeo::new();
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
        let mut interner = lasso::Rodeo::new();
        let f = crate::verify::lang::FuncId(lasso::Key::into_usize(interner.get_or_intern("f")));
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let fa = ctx.add(Symbolic::FuncApp(f, Box::from([]), Box::from([a])));
        let fb = ctx.add(Symbolic::FuncApp(f, Box::from([]), Box::from([b])));
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
        let interner = lasso::Rodeo::new();

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
        let interner = lasso::Rodeo::new();
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
        let interner = lasso::Rodeo::new();
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
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);
        let b = ctx.add(Symbolic::Fresh(0));
        let f = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let ite = ctx.add(Symbolic::Ite([b, b, f]));
        ctx.saturate();
        assert_eq!(ctx.egraph.find(ite), ctx.egraph.find(b));
    }
}
