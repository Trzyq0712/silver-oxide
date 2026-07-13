use std::collections::HashMap;

use crate::vmir::display::VmirDisplay;
use crate::{
    verify::{
        cert::{BodyRecipe, FunctionDefinition, ResourceDefinition},
        context::VerifyContext,
        error::VerifyError,
        heap::{Chunk, Heap, LocationKind},
        lang::Symbolic,
        viz::Snapshotter,
    },
    vmir::{
        self, Assign, BinOp, Bound, Declaration, Function, HeapInst, HeapVal, Inst, InstKind,
        Literal, MemberId, Method, PathConds, Polarity, PureInst, Resource, Sign, Type, Val,
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
    // Whether to drop the emptied chunk is a statement about the *heap*, so it has
    // to hold at the heap's scope — **unconditionally**, not under this
    // instruction's `pc`.
    //
    // The two differ because VMIR is linearized: the heap this subtract produces
    // flows on into the sibling branch, where `pc` does not hold. A guarded consume
    // (`h13 := <c> h12 - acc a (c ? 1/1 : 0/1)`, how the frontend lowers a move
    // inside an `if`) has remainder `1/1 - (c ? 1/1 : 0/1)` — zero under `c`, but a
    // full `1/1` under `!c`, where the permission was never given up. Proving
    // `remainder == 0` under `pc = <c>` and dropping the chunk loses the permission
    // for the `!c` path, which is what made the `else` arm of
    // `fn rect_new(a, b) { if a.x <= b.x { Rect{a,b} } else { Rect{b,a} } }` unable
    // to reclaim `a`.
    //
    // Const-fold, not `prove_under_pc`: this is heap hygiene, not an obligation, so
    // it must stay O(1). Asking the prover instead makes every subtract fall
    // through to the tier-3 clone and the tier-4 case split — the check is run once
    // per chunk per consume, and it dominated everything (93s vs 4s). Keeping a
    // chunk we merely *failed to prove* empty is always sound: the remainder term
    // evaluates to 0 on-path and to the retained permission off-path, and a
    // zero-permission chunk is inert (`perm > 0` gates every use). An ordinary
    // unguarded consume still folds to `1/1 - 1/1 = 0` and drops, as before.
    let empty = matches!(
        ctx.egraph[remainder].data.known(),
        Some(Literal::Real(r)) if *r == num::BigRational::from(num::BigInt::from(0))
    );
    if empty {
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
                Sign::Add => {
                    // Log the acc's minted value for resource purification (keyed
                    // by value e-class so two-state derefs stay distinct).
                    if let Some(events) = ctx.heap_events.as_mut() {
                        events.push(HeapEvent::Acc { value: ch.value });
                    }
                    Ok(heap_union(ctx, &base_h, &kind, ch, &pc_lits))
                }
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
    certs: &HashMap<MemberId, ResourceDefinition>,
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

fn eval_method_inst(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceDefinition>,
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
        // `base inhale <resource>(args) perm`: produce the resource's footprint
        // (fresh values), scaled by `perm`, into `base` and **assume** its
        // boolean; `base exhale ...` consumes the footprint from `base` and
        // **asserts** it. A self-framed callee additionally yields the snapshot
        // of its footprint as a pure `Val` (the pre-state handle a two-state call
        // receives). Both route through `walk_footprint`.
        InstKind::Heap(
            hi @ (HeapInst::Inhale { base, call, perm } | HeapInst::Exhale { base, call, perm }),
        ) => {
            let is_inhale = matches!(hi, HeapInst::Inhale { .. });
            let base_h = get_heap(state, base);
            let args: Vec<egg::Id> = call.args.iter().map(|v| state.get_val(ctx, v)).collect();
            let scale = state.get_val(ctx, perm);
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
            // Inhale: produce fresh chunks, assume the bool guarded by `0 < scale`
            // (it carries no path condition — the branch lives in the perm scale).
            // Exhale: consume the held chunks, assert the bool under `pc`.
            let (source, direction, bool_guard) = if is_inhale {
                let pos = ctx.perm_positive(scale);
                (
                    ValueSource::Fresh,
                    Direction::Produce,
                    vec![(pos, Polarity::Positive)],
                )
            } else {
                (
                    ValueSource::ReadHeap(base_h.clone()),
                    Direction::Consume,
                    pc_lits.clone(),
                )
            };
            let FootprintResult {
                heap: out, members, ..
            } = walk_footprint(
                ctx,
                program,
                certs,
                call.resource,
                &args,
                base_h,
                source,
                direction,
                Some(scale),
                &pc_lits,
                &bool_guard,
            )?;
            state.push_heap(out);
            if let Some(res_id) = hi.snap_yield(&program.decls) {
                let s = build_snapshot(ctx, res_id, members);
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
            let FootprintResult {
                heap: out, members, ..
            } = walk_footprint(
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
    /// absent). Used by `fold`/`snap`/`exhale`, which read a heap they hold.
    ReadHeap(Heap),
    /// Recover it from the snapshot `s` as `unwrap(proj_i(s))`. Used by
    /// `unfold`/`from_snap`, which reconstruct the footprint from a snapshot.
    ProjectSnap(egg::Id),
    /// A fresh unconstrained value per slot. Used by `inhale`, which produces a
    /// resource's footprint with unknown location values.
    Fresh,
}

/// The direction of a footprint walk: consume a held footprint and **assert** the
/// resource's boolean (`fold`/`snap`), or produce one and **assume** it
/// (`unfold`/`from_snap`).
enum Direction {
    Consume,
    Produce,
}

/// The result of a footprint walk: the accumulator heap after all slot effects,
/// the snapshot members `present ? Some(v) : None` per slot (for a `Consume`
/// walk; empty for `Produce`), and the grafted slot **addresses** in slot order
/// (for function purification's recipe log — see [`HeapEvent`]).
struct FootprintResult {
    heap: Heap,
    members: Vec<egg::Id>,
    /// Grafted slot values in slot order (for the purification event log).
    slot_values: Vec<egg::Id>,
}

/// A heap-reconstruction event logged during a **function or resource** body
/// walk (`ctx.heap_events`), in body order, so purification can rebuild each
/// `Deref`'s value as a pure recipe term. Events are keyed by the **value**
/// e-class each produces (not the address), so a two-state resource that reads
/// the same address in two heap states (`old(x.f)` vs `x.f`) stays distinct.
pub(crate) enum HeapEvent {
    /// An `acc(loc, perm)`: the freshly-minted location value.
    Acc { value: egg::Id },
    /// A `FromSnap`: the per-slot reconstructed values (`unwrap(proj_i(snap))`).
    FromSnap { values: Vec<egg::Id> },
    /// An `Unfold`: the consumed predicate chunk's value (the snapshot the new
    /// slots project from) and the per-slot reproduced values.
    Unfold {
        consumed: egg::Id,
        values: Vec<egg::Id>,
    },
    /// A `Snap` (nested heap-dependent call): the resource whose snapshot is
    /// taken and the per-slot values read from the current heap. The recipe term
    /// is `cons(Some(v_i))` — a self-framed footprint is fully held, so each slot
    /// is present.
    Snap {
        resource: MemberId,
        values: Vec<egg::Id>,
    },
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
    _program: &vmir::Program,
    certs: &HashMap<MemberId, ResourceDefinition>,
    resource: MemberId,
    args: &[egg::Id],
    base: Heap,
    source: ValueSource,
    direction: Direction,
    scale: Option<egg::Id>,
    pc_lits: &[(egg::Id, Polarity)],
    // The guard under which the body boolean is discharged (asserted for
    // `Consume`, assumed for `Produce`). Usually `pc_lits`; an `inhale` passes
    // `[0 < scale]` since it carries no path condition.
    bool_guard: &[(egg::Id, Polarity)],
) -> Result<FootprintResult, VerifyError> {
    use crate::verify::cert::SeedRef;
    let def = certs.get(&resource).ok_or(VerifyError::DependencyFailed)?;

    let mut heap = base;
    let mut values: Vec<egg::Id> = Vec::with_capacity(def.footprint.len());
    let mut members = Vec::with_capacity(def.footprint.len());
    let mut changed = Vec::new();
    for (i, slot) in def.footprint.iter().enumerate() {
        // Rebuild the slot's address and permission from their recipes, resolving
        // params to `args` and any earlier-slot value refs to `values` (so a
        // value-dependent inner address like `list(this.next)` resolves).
        let resolve = |r: &SeedRef| -> egg::Id {
            match r {
                SeedRef::Param(k) => args[*k],
                SeedRef::SlotValue(j) => values[*j],
            }
        };
        // Heap framing is a *syntactic* e-class match (`heap_subtract`,
        // `ValueSource::ReadHeap`), so a slot address has to be in normal form
        // before we look it up. A slot address that reaches through a snapshot —
        // `Pt(f(r, cons(Some(unwrap(proj_0(s))))))`, the shape a Rust `&mut`
        // reparented under `old(..)` produces — is only e-class-equal to the held
        // chunk's address once the `proj∘cons` / `unwrap∘Some` reductions have
        // fired.
        //
        // Reduce only when the rebuild actually introduced something to reduce.
        // The recipe is add-only, so if `build` added no e-node then every term it
        // named was already present — and therefore already normalized by the
        // reduce that first introduced it. Guarding on the node count keeps repeat
        // call sites (the common case: one resource, many uses) free; reducing
        // unconditionally per slot re-runs the ADT rule set over the whole e-graph
        // every time and costs ~3.5x end to end.
        let before = ctx.egraph.total_number_of_nodes();
        let addr = slot.addr.build(&mut ctx.egraph, resolve, &mut changed);
        let bperm = slot.perm.build(&mut ctx.egraph, resolve, &mut changed);
        if ctx.egraph.total_number_of_nodes() != before {
            ctx.reduce();
        }
        let addr = ctx.egraph.find(addr);
        let bperm = ctx.egraph.find(bperm);
        let elem = slot.elem.clone();
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
            // Inhale: an unconstrained fresh value per slot.
            ValueSource::Fresh => ctx.fresh_symbolic_value(elem.clone()),
        };
        // The heap effect uses the (optionally scaled) permission; the snapshot
        // membership discriminant uses the *unscaled* recipe perm.
        let p = match scale {
            Some(pm) => ctx.add(Symbolic::Binary(BinOp::Mult, [pm, bperm])),
            None => bperm,
        };
        let chunk = Chunk::new(addr, p, value);
        heap = match direction {
            Direction::Consume => heap_subtract(ctx, &heap, &slot.kind, chunk, pc_lits)?,
            Direction::Produce => heap_union(ctx, &heap, &slot.kind, chunk, pc_lits),
        };
        // Snapshot member `present ? Some(v) : None` (built for both directions —
        // `fold`/`snap` and snapshot-yielding `inhale`/`exhale` all need it).
        let present = ctx.perm_positive(bperm);
        members.push(ctx.option_member(elem, present, value));
        values.push(value);
    }
    // The body boolean over params ++ all slot values.
    let resolve = |r: &SeedRef| -> egg::Id {
        match r {
            SeedRef::Param(k) => args[*k],
            SeedRef::SlotValue(j) => values[*j],
        }
    };
    let bool_id = def.bool.build(&mut ctx.egraph, resolve, &mut changed);
    match direction {
        // The precondition/predicate body must hold over the consumed values.
        Direction::Consume => {
            if !ctx.prove_under_pc(bool_id, bool_guard) {
                return Err(VerifyError::AssertionFailed);
            }
        }
        // The reconstructed body facts hold only where this walk is reached.
        Direction::Produce => {
            ctx.assume_guarded(bool_id, bool_guard.iter().rev().copied());
        }
    }
    Ok(FootprintResult {
        heap,
        members,
        slot_values: values,
    })
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
    certs: &HashMap<MemberId, ResourceDefinition>,
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
    let FootprintResult {
        heap: out,
        slot_values,
        ..
    } = walk_footprint(
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
        &pc_lits,
    )?;
    // Log for purification: the new slots reconstruct as `unwrap(proj_j(s))`
    // where `s` is the recipe term of the consumed predicate value.
    if let Some(events) = ctx.heap_events.as_mut() {
        events.push(HeapEvent::Unfold {
            consumed: s,
            values: slot_values,
        });
    }
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
    certs: &HashMap<MemberId, ResourceDefinition>,
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
    let FootprintResult {
        members,
        slot_values,
        ..
    } = walk_footprint(
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
        &pc_lits,
    )?;
    // Log for purification: the snapshot reconstructs as `cons(Some(v_i))` over
    // these read values.
    if let Some(events) = ctx.heap_events.as_mut() {
        events.push(HeapEvent::Snap {
            resource: *resource,
            values: slot_values,
        });
    }
    let s = build_snapshot(ctx, *resource, members);

    // The precondition held here — `walk_footprint` proved footprint
    // sufficiency and the resource's bool. **Release the pre-token**: assume
    // `R#pre(args, s)`, the uninterpreted stamp guarding every fact the callee
    // exported (`pre_token`). Silicon does exactly this after consuming a
    // function's precondition at a call site (`Evaluator.scala:652`). The token
    // is never defined, so it can only ever become true here — which is what
    // makes the guarded facts sound.
    let name = program.name(*resource).to_string();
    let tok = ctx.alloc.pre_token(*resource, &name);
    let mut tok_args = args;
    tok_args.push(s);
    let tok = ctx.add_func_app_id(tok, Box::new([]), Type::Bool, tok_args.into());
    ctx.assume_guarded(tok, pc_lits.iter().rev().copied());

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
    certs: &HashMap<MemberId, ResourceDefinition>,
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
    let FootprintResult {
        heap: out,
        slot_values,
        ..
    } = walk_footprint(
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
        &pc_lits,
    )?;
    // Log for purification: these values reconstruct as `unwrap(proj_i(snap))`.
    if let Some(events) = ctx.heap_events.as_mut() {
        events.push(HeapEvent::FromSnap {
            values: slot_values,
        });
    }
    ctx.reduce();
    Ok(out)
}

/// Axiomatize the state: make every domain axiom's fact available to the unit
/// about to be verified. An axiom body is evaluated into the e-graph and its
/// boolean merged with `true` up front — domains are monomorphic, so there is no
/// type-σ instantiation; quantification over *values* is a `forall` in the body,
/// which becomes its own lazy-instantiation rule below. Axiom bodies are trusted
/// — no obligations (div-by-zero, deref permission) are checked on them.
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
        // into every saturation. Its body is never verified; instantiation adds
        // a guarded clause per ground trigger match.
        if let vmir::Declaration::Quantifier(q) = decl {
            let name = ctx.interner.resolve(&q.name).to_string();
            // One rule per trigger group (alternatives), sharing one
            // instantiation memo so two groups reaching the same σ build the
            // instance once.
            let memo = crate::verify::rewrite::quant_memo();
            for (k, prepared) in prepare_quantifier(ctx.alloc, id, q)?
                .into_iter()
                .enumerate()
            {
                ctx.axiom_rules
                    .push(crate::verify::rewrite::quantifier_rule(
                        &format!("{name}#t{k}"),
                        prepared,
                        std::sync::Arc::clone(&memo),
                    ));
            }
            continue;
        }
        let vmir::Declaration::Axiom(ax) = decl else {
            continue;
        };
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
    }
    // One lazy unfold rule per already-verified function certificate: `analyze`
    // guarantees a function only ever calls functions verified earlier (it
    // rejects (mutual) recursion as a dependency cycle), so every function this
    // unit could reference already has a cert in `fn_certs` by the time its
    // ctx is set up here — same guarantee the driver's topological order
    // (`mod.rs`) already relies on. Each rule rebuilds the recipe's body lazily
    // (add-only) the moment a `FuncApp(f, ..)` occurrence is seen during
    // saturation (see `rewrite::function_rule`), instead of eagerly grafting it
    // once at translation-walk time.
    if let Some(fn_certs) = ctx.fn_certs {
        for (&id, def) in fn_certs.iter() {
            let name = ctx.member_name(id);
            let func = crate::verify::func_registry::func_id_for_member(id);
            ctx.axiom_rules.push(crate::verify::rewrite::function_rule(
                &name,
                func,
                std::sync::Arc::clone(def),
            ));
            // A recursive function's post fact also triggers on its limited
            // twin `f'` — that is what delivers the postcondition at a
            // recursive unroll (the twin has no unfold rule by design).
            if def.limited.is_some() && def.facts.iter().any(|f| f.post) {
                ctx.axiom_rules
                    .push(crate::verify::rewrite::function_post_rule(
                        &name,
                        std::sync::Arc::clone(def),
                    ));
            }
        }
    }
    Ok(())
}

/// Resolve a pure `forall` into one [`PreparedQuantifier`] **per trigger group**
/// (the groups are alternatives — each gets its own instantiation rule): the
/// body as registry-level pure steps, its boolean result, the occurrence id and
/// capture arity, and the group's pattern terms with every head resolved to its
/// verifier `FuncId`. Instantiation pairs each ground occurrence with the
/// bound-variable σ read off a ground match of the group.
fn prepare_quantifier(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    id: vmir::MemberId,
    q: &vmir::Quantifier,
) -> Result<Vec<crate::verify::rewrite::PreparedQuantifier>, VerifyError> {
    use crate::verify::rewrite::PreparedQuantifier;
    let insts = prepare_body(alloc, &q.body.insts)?;
    q.triggers
        .iter()
        .map(|group| {
            let group = group
                .terms
                .iter()
                .map(|t| prepare_trig_term(alloc, t))
                .collect();
            Ok(PreparedQuantifier {
                quant_func: crate::verify::func_registry::func_id_for_member(id),
                n_caps: q.params.len(),
                n_bound: q.bound.len(),
                group,
                insts: insts.clone(),
                res: q.body.res.clone(),
            })
        })
        .collect()
}

/// Resolve a trigger pattern term's heads to verifier `FuncId`s — the same
/// mapping [`prepare_body`] applies to the corresponding `PureInst`, so a
/// pattern matches exactly the nodes a body would build.
fn prepare_trig_term(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    term: &vmir::TrigTerm,
) -> crate::verify::rewrite::PreparedTerm {
    use crate::verify::rewrite::PreparedTerm;
    match term {
        vmir::TrigTerm::Bound(i) => PreparedTerm::Bound(*i),
        vmir::TrigTerm::Capture(c) => PreparedTerm::Capture(*c),
        vmir::TrigTerm::Lit(lit) => PreparedTerm::Lit(lit.clone()),
        vmir::TrigTerm::App {
            head,
            type_args,
            args,
        } => {
            let func = match head {
                vmir::TrigHead::Func(id) => crate::verify::func_registry::func_id_for_member(*id),
                vmir::TrigHead::AdtCons { adt, variant } => alloc.cons(*adt, *variant),
                vmir::TrigHead::AdtProj {
                    adt,
                    variant,
                    field,
                } => alloc.proj(*adt, *variant, *field),
                vmir::TrigHead::AdtTag { adt } => alloc.tag(*adt),
            };
            PreparedTerm::App {
                func,
                type_args: type_args.iter().cloned().collect(),
                args: args.iter().map(|a| prepare_trig_term(alloc, a)).collect(),
            }
        }
    }
}

/// Lower an axiom/quantifier body's inst stream into registry-resolved pure
/// steps (every callee down to its verifier `FuncId`), ready for the applier —
/// which has no registry access at rule-application time.
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
    &HashMap<MemberId, ResourceDefinition>,
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
    certs: &HashMap<MemberId, ResourceDefinition>,
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
    certs: &HashMap<MemberId, ResourceDefinition>,
    fn_certs: &HashMap<MemberId, std::sync::Arc<FunctionDefinition>>,
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
    certs: &HashMap<MemberId, ResourceDefinition>,
    fn_certs: &HashMap<MemberId, std::sync::Arc<FunctionDefinition>>,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> Result<Option<ResourceDefinition>, VerifyError> {
    let Some(body) = resource.body.as_ref() else {
        // Abstract resource: nothing to prove, no definition.
        return Ok(None);
    };

    let mut ctx = VerifyContext::new(&program.interner, &program.decls, &program.groups, alloc);
    ctx.fn_certs = Some(fn_certs);
    ctx.heap_events = Some(Vec::new()); // record FromSnap/Unfold for purification
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
    let mut state = EvalState::with_args(params, resource.params.clone());

    let mut snap = Snapshotter::from_env(resource_name);
    snap.snapshot(&ctx, &[], "init", None);

    walk_body(
        &mut ctx,
        program,
        &mut state,
        &mut snap,
        &body.insts,
        certs,
        eval_resource_body_inst,
        None,
    )?;

    // Capture the body as a pure recipe (add-only; imports no e-classes). Each
    // call site rebuilds the footprint addresses/permissions and the body boolean
    // from the recipe and re-derives any merge it needs itself (Finding C).
    let events = ctx.heap_events.take().unwrap_or_default();
    let def = purify_resource(&mut ctx, resource, body, &state, &events)?;
    Ok(Some(def))
}

/// Verify a non-recursive function and capture its body as a **pure term
/// recipe** ([`FunctionDefinition`]) for other units to unfold lazily at call
/// sites (`rewrite::function_rule`). Abstract functions (no body) have nothing
/// to verify.
///
/// The walk runs the ordinary live eval (obligations, `FromSnap`/`Unfold` heap
/// reconstruction, `Deref` values), logging each heap-reconstruction event into
/// `ctx.heap_events`. Then [`purify_function`] re-walks the body once, turning it
/// into an add-only recipe over the params (and the snapshot param, for
/// heap-dependent functions): every `Deref` becomes the pure term the snapshot
/// projects to (`unwrap(proj_i(snap))`, possibly nested through `unfolding`), and
/// the entry `assume f#requires` is **dropped**. That drop is the whole point —
/// the old design cloned the verified e-graph, so a precondition-derived merge
/// (e.g. `g(x) ≡ 5` from `requires g(x)==5` once a body obligation saturated)
/// rode into every call site via `transplant`; a recipe imports no e-classes, so
/// it cannot leak (Finding B).
///
/// Callees — including the function's own `f#requires`/`f#ensures` contract
/// functions — are ordinary `Function` decls verified earlier in dependency
/// order, so their recipes are already in `fn_certs`, and `assume_axioms`
/// (called at the top of this function's own `ctx` setup) has already installed
/// their unfold rules — saturation (triggered via `prove_under_pc`) discharges
/// the contract obligations lazily as needed.
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_function(
    program: &vmir::Program,
    function_name: &str,
    self_id: MemberId,
    function: &Function,
    certs: &HashMap<MemberId, ResourceDefinition>,
    fn_certs: &HashMap<MemberId, std::sync::Arc<FunctionDefinition>>,
    // The members of `self_id`'s SCC iff it is a genuine recursion cycle (else
    // `None`). In-SCC callees are retargeted to their limited twin in the recipe,
    // and this function's own limited twin is recorded so its unfold rule frames
    // `f(x) == f'(x)`.
    recursive_scc: Option<&std::collections::HashSet<MemberId>>,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> Result<Option<std::sync::Arc<FunctionDefinition>>, VerifyError> {
    let Some(body) = function.body.as_ref() else {
        // Abstract/uninterpreted function: no body to verify. Its contract
        // decls are verified as ordinary Functions (spec WF); synthesize the
        // guarded post axiom from the contract links, if any.
        return Ok(contract_post_definition(
            alloc,
            program,
            self_id,
            function,
            recursive_scc.is_some(),
        ));
    };

    let mut ctx = VerifyContext::new(&program.interner, &program.decls, &program.groups, alloc);
    ctx.fn_certs = Some(fn_certs);
    ctx.heap_events = Some(Vec::new()); // record FromSnap/Unfold for purification
    assume_axioms(&mut ctx, program)?;
    // Recursive batch: every SCC member's spec-derived post axiom is available
    // while this body is checked (Silicon emits `post` in phase 1, before the
    // phase-2 body check) — this is what lets the exit assert use a recursive
    // call's postcondition (induction; termination is not checked, same as
    // Silicon without `decreases`).
    if let Some(scc) = recursive_scc {
        for &m in scc {
            let vmir::Declaration::Function(mf) = &program.decls[m] else {
                continue;
            };
            if let Some(post) = contract_post_definition(ctx.alloc, program, m, mf, false) {
                let name = ctx.member_name(m);
                let func = crate::verify::func_registry::func_id_for_member(m);
                ctx.axiom_rules
                    .push(crate::verify::rewrite::facts_rule(&name, func, post));
            }
        }
    }
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
    // (pure ops, the entry `assume`, `Snap`/`FromSnap`/`Unfold` for heap-dependent
    // functions).
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

    // Turn the walked body into a pure, add-only recipe (params → args at call
    // sites via `build_instance`), using the event log to reconstruct `Deref`
    // values as `unwrap(proj_i(snap))` terms.
    let events = ctx.heap_events.take().unwrap_or_default();
    let (steps, res, facts) = purify_function(
        &mut ctx,
        program,
        self_id,
        function,
        body,
        &state,
        &events,
        recursive_scc,
    )?;
    // A recursive function records its limited twin so the unfold rule frames
    // `f(x) == f'(x)`. Minted here (not in the recipe) so the id exists even if
    // the body has no reachable recursive call under some path.
    let limited = recursive_scc.map(|_| {
        let name = ctx.member_name(self_id);
        ctx.alloc.limited(self_id, &name)
    });
    Ok(Some(std::sync::Arc::new(FunctionDefinition {
        n_params: function.params.len(),
        steps,
        res: Some(res),
        limited,
        facts,
    })))
}

/// The **pre-token** guarding every fact a function's body exports: the
/// application `(func, args)` that must hold for the facts to fire, over the
/// function's own param space (`Val::Temp(0..n_params)` — so recipe space too,
/// where the params are the identity).
///
/// The two function flavours supply it differently, but the guard *shape* is the
/// same single boolean application either way:
/// - **heap-free**: `f#requires(params)`, a **defined** boolean function. A call
///   site's `Assert f#requires(args)` passing is what makes it true there.
/// - **heap-dependent**: `R#pre(args, s)`, an **uninterpreted** token over the
///   `#requires` Resource (see [`FuncRegistry::pre_token`]). The precondition is
///   not definable from `(args, s)` — it also demands the footprint — so the
///   token is stamped by [`eval_snap`] where the check passed.
///
/// `None` for a function without a precondition (its facts are unguarded).
fn pre_token(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    program: &vmir::Program,
    function: &Function,
) -> Option<(crate::verify::lang::FuncId, Vec<Val>)> {
    match function.requires.as_ref()? {
        vmir::Requires::Pure(rq) => Some((
            crate::verify::func_registry::func_id_for_member(rq.member),
            rq.args.clone(),
        )),
        vmir::Requires::Framed {
            resource,
            args,
            snap,
        } => {
            let name = program.name(*resource).to_string();
            let mut args = args.clone();
            args.push(snap.clone());
            Some((alloc.pre_token(*resource, &name), args))
        }
    }
}

/// Synthesize an **abstract** function's definition: no body, nothing to
/// verify — just the guarded post axiom `pre-token ⟹ f#ensures(params,
/// f(params))` built from the contract links. (Silicon's phase 1 emits
/// `post`/`postProp` for abstract functions once the spec is well-defined; our
/// contract decls get that WF check as ordinary `Function` verification,
/// scheduled first by the link edges in `analyze`.) `None` when there is nothing
/// to export: no ensures, or a generic function.
fn contract_post_definition(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    program: &vmir::Program,
    self_id: MemberId,
    function: &Function,
    // Set when this is the function's *own* definition and it sits in a
    // recursion cycle: the fact then expresses the result as the limited twin
    // `f'(params)` and the definition records `f'`, so the unfold rule frames
    // `f(x) == f'(x)`. Without the frame an abstract SCC member would be
    // unreachable from a sibling's recipe, which lowers it to `f'`. Cleared for
    // the in-batch pre-seed (rules keyed on the full ids, no frames installed
    // yet).
    recursive: bool,
) -> Option<std::sync::Arc<FunctionDefinition>> {
    use crate::verify::cert::Fact;
    use crate::verify::func_registry::func_id_for_member;
    use crate::verify::rewrite::{AxiomInst, AxiomPure};

    let en = function.ensures.as_ref()?;
    let limited = recursive.then(|| alloc.limited(self_id, program.name(self_id)));
    let n_params = function.params.len();
    let mut steps: Vec<AxiomInst> = Vec::new();
    let emit = |steps: &mut Vec<AxiomInst>, pure: AxiomPure| -> Val {
        let v = Val::Temp(n_params + steps.len());
        steps.push(AxiomInst::Val(pure));
        v
    };
    // Link args are over the params (`Temp(0..n_params)`) — identity in recipe
    // space, so they can be used verbatim.
    let mut guards = Vec::new();
    if let Some((func, args)) = pre_token(alloc, program, function) {
        let tok = emit(
            &mut steps,
            AxiomPure::App {
                func,
                type_args: Vec::new(),
                args,
            },
        );
        guards.push((tok, vmir::Polarity::Positive));
    }
    let self_app = emit(
        &mut steps,
        AxiomPure::App {
            func: limited.unwrap_or_else(|| func_id_for_member(self_id)),
            type_args: Vec::new(),
            args: (0..n_params).map(Val::Temp).collect(),
        },
    );
    let args: Vec<Val> = en
        .args
        .iter()
        .map(|a| match a {
            vmir::ContractArg::Val(v) => v.clone(),
            vmir::ContractArg::Result => self_app.clone(),
        })
        .collect();
    let cond = emit(
        &mut steps,
        AxiomPure::App {
            func: func_id_for_member(en.member),
            type_args: Vec::new(),
            args,
        },
    );
    Some(std::sync::Arc::new(FunctionDefinition {
        n_params,
        steps,
        res: None,
        limited,
        facts: vec![Fact {
            guards,
            cond,
            post: true,
        }],
    }))
}

/// Turn a walked function body into a pure recipe `(steps, res)` in dense
/// recipe-temp space (params `Temp(0..n_params)`, one slot per emitted step).
/// Re-walks `body.insts` maintaining `map: body-temp → recipe Val` (seeded with
/// the params) and `at: canonical address → recipe value term`, consuming the
/// ordered `events` for the `FromSnap`/`Unfold` slot addresses. Reads the live
/// `state.vals` (finalized after the walk) to resolve each `Deref`'s address to a
/// footprint slot by congruence.
#[allow(clippy::too_many_arguments)]
fn purify_function(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    self_id: MemberId,
    function: &Function,
    body: &vmir::FunctionBody,
    state: &EvalState,
    events: &[HeapEvent],
    // In-SCC callees (a recursion cycle's members) are lowered to their limited
    // twin so a downstream unfold of this recipe halts after one level; `None`
    // (non-recursive) keeps every callee as its full id.
    recursive_scc: Option<&std::collections::HashSet<MemberId>>,
) -> Result<
    (
        Vec<crate::verify::rewrite::AxiomInst>,
        Val,
        Vec<crate::verify::cert::Fact>,
    ),
    VerifyError,
> {
    use crate::verify::cert::Fact;
    use crate::verify::rewrite::{AxiomInst, AxiomPure};

    let n_params = function.params.len();
    let mut steps: Vec<AxiomInst> = Vec::new();
    // body-temp → recipe Val, seeded with the params (identity).
    let mut map: Vec<Val> = (0..n_params).map(Val::Temp).collect();
    let mut at: HashMap<egg::Id, Val> = HashMap::new();
    let mut events = events.iter();
    // ---- facts export (see `cert::Fact`): every body `Assert` was proven
    // under `pre ∧ pc`, so it re-exports as a guarded fact at call sites.
    let mut facts: Vec<Fact> = Vec::new();
    // Body `Val::Temp` index of each FunctionCall → callee, to spot the exit
    // `assert f#ensures(..)` (which exports in `f'(params)` shape instead).
    let mut callee_of: HashMap<usize, MemberId> = HashMap::new();
    // This function's pre-token (`f#requires(params)` when heap-free,
    // `R#pre(params, s)` when heap-dependent — see `pre_token`), as a recipe
    // step, emitted on first use.
    let guard_app = pre_token(ctx.alloc, program, function);
    let mut pre_guard: Option<Val> = None;

    // Emit a pure step, returning its dense recipe temp.
    let emit = |steps: &mut Vec<AxiomInst>, pure: AxiomPure| -> Val {
        let v = Val::Temp(n_params + steps.len());
        steps.push(AxiomInst::Val(pure));
        v
    };
    // This function's pre-token as a recipe step, emitted once on first use.
    // Its args are over the params, which are the identity in recipe space, so
    // they need no `tr`.
    let guard = |steps: &mut Vec<AxiomInst>,
                 app: &Option<(crate::verify::lang::FuncId, Vec<Val>)>,
                 cache: &mut Option<Val>|
     -> Option<Val> {
        let (func, args) = app.as_ref()?;
        if cache.is_none() {
            *cache = Some(emit(
                steps,
                AxiomPure::App {
                    func: *func,
                    type_args: Vec::new(),
                    args: args.clone(),
                },
            ));
        }
        cache.clone()
    };
    // Translate a body-space operand into recipe space.
    let tr = |map: &[Val], v: &Val| -> Val {
        match v {
            Val::Temp(n) => map[*n].clone(),
            Val::Literal(l) => Val::Literal(l.clone()),
        }
    };
    // The `option_value` accessor (`unwrap`) is monomorphic-per-elem.
    let project_unwrap = |ctx: &mut VerifyContext<'_>,
                          steps: &mut Vec<AxiomInst>,
                          resource: MemberId,
                          index: usize,
                          elem: Type,
                          snap: Val|
     -> Val {
        let proj = ctx.alloc.proj(resource, 0, index);
        let opt = emit(
            steps,
            AxiomPure::App {
                func: proj,
                type_args: Vec::new(),
                args: vec![snap],
            },
        );
        let value = ctx.alloc.option_value();
        emit(
            steps,
            AxiomPure::App {
                func: value,
                type_args: vec![elem],
                args: vec![opt],
            },
        )
    };

    // Per-resource footprint element types (`option_inner` of each snapshot field).
    let slot_elems = |resource: MemberId| -> Result<Vec<Type>, VerifyError> {
        let vmir::Declaration::Resource(r) = &ctx.decls[resource] else {
            return Err(VerifyError::DependencyFailed);
        };
        let Some(vmir::Snapshot::Concrete(snap)) = r.derive_snapshot() else {
            return Err(VerifyError::Unimplemented(
                "purify: abstract resource footprint",
            ));
        };
        Ok(snap
            .variants
            .into_iter()
            .next()
            .unwrap()
            .field_types
            .iter()
            .map(|t| t.option_inner().unwrap_or(t).clone())
            .collect())
    };

    for inst in &body.insts {
        match &inst.kind {
            InstKind::Pure(_, PureInst::Deref(..)) => {
                // The deref's own live value e-class keys the recipe term (keying
                // by value, not address, keeps two-state derefs distinct).
                let ec = ctx.egraph.find(state.vals[map.len()]);
                let v = at.get(&ec).cloned().ok_or(VerifyError::Unimplemented(
                    "purify: deref outside footprint",
                ))?;
                map.push(v);
            }
            InstKind::Pure(_, PureInst::Perm(..)) => {
                return Err(VerifyError::Unimplemented("purify: perm in function"));
            }
            // A nested heap-dependent call's `Snap`: the snapshot of the callee's
            // footprint, `cons(Some(v_i))` over the values read from the current
            // heap (a self-framed footprint is fully held, so each slot is Some).
            InstKind::Pure(_, PureInst::Snap { args, .. }) => {
                let Some(HeapEvent::Snap { resource, values }) = events.next() else {
                    unreachable!("Snap inst without a logged Snap event");
                };
                let elems = slot_elems(*resource)?;
                let some_id = ctx.alloc.option_some();
                let cons_id = ctx.alloc.cons(*resource, 0);
                let mut members = Vec::with_capacity(values.len());
                for (i, &value) in values.iter().enumerate() {
                    let v = at.get(&ctx.egraph.find(value)).cloned().ok_or(
                        VerifyError::Unimplemented("purify: snap value outside footprint"),
                    )?;
                    members.push(emit(
                        &mut steps,
                        AxiomPure::App {
                            func: some_id,
                            type_args: vec![elems[i].clone()],
                            args: vec![v],
                        },
                    ));
                }
                let s = emit(
                    &mut steps,
                    AxiomPure::App {
                        func: cons_id,
                        type_args: Vec::new(),
                        args: members,
                    },
                );
                // The nested callee's precondition was *checked here*, by this
                // `Snap`'s implicit exhale — but that check lives in the inst,
                // not in an `Assert`, so deriving facts from asserts misses it.
                // Export the callee's pre-token over the snapshot we just built,
                // so a caller who rebuilds this recipe (and thereby materializes
                // the nested `g(args, s)`) can discharge the guard on `g`'s own
                // post fact without re-running the check. This is Silicon's
                // `bodyPreconditionPropagationAxiom`
                // (`FunctionData.scala:302`): `f%pre ⟹ pres of everything f calls`.
                let name = program.name(*resource).to_string();
                let tok = ctx.alloc.pre_token(*resource, &name);
                let mut tok_args: Vec<Val> = args.iter().map(|a| tr(&map, a)).collect();
                tok_args.push(s.clone());
                let cond = emit(
                    &mut steps,
                    AxiomPure::App {
                        func: tok,
                        type_args: Vec::new(),
                        args: tok_args,
                    },
                );
                let mut guards: Vec<(Val, Polarity)> = Vec::new();
                if let Some(g) = guard(&mut steps, &guard_app, &mut pre_guard) {
                    guards.push((g, Polarity::Positive));
                }
                for (val, pol) in &inst.pc.conds {
                    guards.push((tr(&map, val), *pol));
                }
                facts.push(Fact {
                    guards,
                    cond,
                    post: false,
                });
                map.push(s);
            }
            InstKind::Pure(_, PureInst::Fresh) => {
                unreachable!("function body may not contain Fresh (method-only)");
            }
            InstKind::Pure(_, pi) => {
                let v = match pi {
                    PureInst::Binary(op, l, r) => {
                        emit(&mut steps, AxiomPure::Binary(*op, tr(&map, l), tr(&map, r)))
                    }
                    PureInst::Ternary(c, t, e) => emit(
                        &mut steps,
                        AxiomPure::Ternary(tr(&map, c), tr(&map, t), tr(&map, e)),
                    ),
                    PureInst::RealCast(x) => emit(&mut steps, AxiomPure::RealCast(tr(&map, x))),
                    PureInst::FunctionCall(fc) => {
                        callee_of.insert(map.len(), fc.function);
                        // A recursive call (callee in this function's SCC) targets
                        // the limited twin `f'` — uninterpreted, so unfolding this
                        // recipe at a call site stops after one level. Every other
                        // callee keeps its full id and unfolds normally.
                        let func = if recursive_scc.is_some_and(|s| s.contains(&fc.function)) {
                            let name = ctx.member_name(fc.function);
                            ctx.alloc.limited(fc.function, &name)
                        } else {
                            crate::verify::func_registry::func_id_for_member(fc.function)
                        };
                        emit(
                            &mut steps,
                            AxiomPure::App {
                                func,
                                type_args: fc.type_args.clone(),
                                args: fc.args.iter().map(|a| tr(&map, a)).collect(),
                            },
                        )
                    }
                    PureInst::AdtCons {
                        adt,
                        type_args,
                        variant,
                        args,
                    } => {
                        let func = ctx.alloc.cons(*adt, *variant);
                        emit(
                            &mut steps,
                            AxiomPure::App {
                                func,
                                type_args: type_args.clone(),
                                args: args.iter().map(|a| tr(&map, a)).collect(),
                            },
                        )
                    }
                    PureInst::AdtProj {
                        adt,
                        type_args,
                        variant,
                        field,
                        base,
                    } => {
                        let func = ctx.alloc.proj(*adt, *variant, *field);
                        emit(
                            &mut steps,
                            AxiomPure::App {
                                func,
                                type_args: type_args.clone(),
                                args: vec![tr(&map, base)],
                            },
                        )
                    }
                    PureInst::AdtTag {
                        adt,
                        type_args,
                        base,
                    } => {
                        let func = ctx.alloc.tag(*adt);
                        emit(
                            &mut steps,
                            AxiomPure::App {
                                func,
                                type_args: type_args.clone(),
                                args: vec![tr(&map, base)],
                            },
                        )
                    }
                    PureInst::Fresh
                    | PureInst::Deref(..)
                    | PureInst::Perm(..)
                    | PureInst::Snap { .. } => unreachable!("handled above"),
                };
                map.push(v);
            }
            // `FromSnap R(args), snap`: each slot value reconstructs as
            // `unwrap(proj_i(snap))`, keyed by the slot's live value e-class.
            InstKind::Heap(HeapInst::FromSnap { resource, snap, .. }) => {
                let Some(HeapEvent::FromSnap { values }) = events.next() else {
                    unreachable!("FromSnap inst without a logged FromSnap event");
                };
                let snap_recipe = tr(&map, snap);
                let elems = slot_elems(*resource)?;
                for (i, &value) in values.iter().enumerate() {
                    let v = project_unwrap(
                        ctx,
                        &mut steps,
                        *resource,
                        i,
                        elems[i].clone(),
                        snap_recipe.clone(),
                    );
                    at.insert(ctx.egraph.find(value), v);
                }
            }
            // `Unfold P(args)`: the consumed predicate chunk's recipe term `s` is
            // the snapshot the new footprint slots project from.
            InstKind::Heap(HeapInst::Unfold { call, .. }) => {
                let Some(HeapEvent::Unfold { consumed, values }) = events.next() else {
                    unreachable!("Unfold inst without a logged Unfold event");
                };
                let s = at.get(&ctx.egraph.find(*consumed)).cloned().ok_or(
                    VerifyError::Unimplemented("purify: unfold of unheld predicate"),
                )?;
                let elems = slot_elems(call.resource)?;
                for (j, &value) in values.iter().enumerate() {
                    let v = project_unwrap(
                        ctx,
                        &mut steps,
                        call.resource,
                        j,
                        elems[j].clone(),
                        s.clone(),
                    );
                    at.insert(ctx.egraph.find(value), v);
                }
            }
            // A function body may `fold` (via `folding … in …`); not yet purified.
            InstKind::Heap(HeapInst::Fold { .. }) => {
                return Err(VerifyError::Unimplemented("purify: fold in function body"));
            }
            InstKind::Heap(_) => {
                unreachable!("function body may not contain inhale/exhale/combine/assign");
            }
            // The entry `assume f#requires` is dropped — that is what keeps the
            // precondition out of the recipe (Finding B). Produces no body
            // temp, so `map` stays aligned.
            InstKind::Assume(_) => {}
            // An `Assert` was *proven* under `pre ∧ pc`, so it exports as a
            // guarded fact (Silicon's `bodyProp`; the exit post assert is its
            // `post` axiom) — replayed at every occurrence of this function.
            InstKind::Assert(v) => {
                let mut guards: Vec<(Val, Polarity)> = Vec::new();
                if let Some(g) = guard(&mut steps, &guard_app, &mut pre_guard) {
                    guards.push((g, Polarity::Positive));
                }
                for (val, pol) in &inst.pc.conds {
                    guards.push((tr(&map, val), *pol));
                }
                let is_post = matches!(v, Val::Temp(n)
                    if function.ensures.as_ref().is_some_and(|en| callee_of.get(n) == Some(&en.member)));
                if is_post {
                    // The post fact expresses the result as the (limited)
                    // application itself — `ens(params, f'(params))` — not the
                    // rebuilt body: at a recursive unroll's `f'(smaller)`
                    // occurrence the fact must talk about that very node
                    // (Silicon's `post` axiom `let r = f'(s,args) in …`).
                    let self_fid = if recursive_scc.is_some() {
                        let name = ctx.member_name(self_id);
                        ctx.alloc.limited(self_id, &name)
                    } else {
                        crate::verify::func_registry::func_id_for_member(self_id)
                    };
                    let self_app = emit(
                        &mut steps,
                        AxiomPure::App {
                            func: self_fid,
                            type_args: Vec::new(),
                            args: (0..n_params).map(Val::Temp).collect(),
                        },
                    );
                    let en = function.ensures.as_ref().unwrap();
                    let args: Vec<Val> = en
                        .args
                        .iter()
                        .map(|a| match a {
                            vmir::ContractArg::Val(v) => tr(&map, v),
                            vmir::ContractArg::Result => self_app.clone(),
                        })
                        .collect();
                    let cond = emit(
                        &mut steps,
                        AxiomPure::App {
                            func: crate::verify::func_registry::func_id_for_member(en.member),
                            type_args: Vec::new(),
                            args,
                        },
                    );
                    facts.push(Fact {
                        guards,
                        cond,
                        post: true,
                    });
                } else {
                    facts.push(Fact {
                        guards,
                        cond: tr(&map, v),
                        post: false,
                    });
                }
            }
            InstKind::Refute(_) => unreachable!("function body may not contain refute"),
        }
    }

    let res = tr(&map, &body.res);
    Ok((steps, res, facts))
}

/// An expression tree over params and footprint slot values, the intermediate
/// form a resource body purifies into. A resource emits *several* outputs (each
/// footprint slot's address and permission, and the body boolean), and an
/// address may depend on an earlier slot's value (`list(this.next)`), so each
/// output is [`flatten`]ed independently into a self-contained [`BodyRecipe`]
/// carrying only the seed slots it uses.
enum RTree {
    Param(usize),
    SlotValue(usize),
    Lit(vmir::Literal),
    Binary(BinOp, Box<RTree>, Box<RTree>),
    Ternary(Box<RTree>, Box<RTree>, Box<RTree>),
    RealCast(Box<RTree>),
    App(crate::verify::lang::FuncId, Vec<Type>, Vec<RTree>),
}

/// Flatten an [`RTree`] into a [`BodyRecipe`]: collect the distinct seed leaves
/// (in first-encounter order) as `seed_refs`, then emit one step per interior
/// node in dense recipe-temp space (`Temp(0..seed_refs.len())` are the seed,
/// steps after). No common-subexpression elimination — `build_instance`
/// hash-conses at rebuild time, so duplicate steps collapse in the e-graph.
fn flatten(tree: &RTree) -> BodyRecipe {
    use crate::verify::cert::SeedRef;
    use crate::verify::rewrite::{AxiomInst, AxiomPure};

    // Pass 1: collect distinct seed refs in first-encounter order.
    fn collect(tree: &RTree, seeds: &mut Vec<SeedRef>) {
        let key = match tree {
            RTree::Param(i) => Some(SeedRef::Param(*i)),
            RTree::SlotValue(i) => Some(SeedRef::SlotValue(*i)),
            _ => None,
        };
        if let Some(k) = key {
            if !seeds.iter().any(|s| {
                matches!((s, &k),
                (SeedRef::Param(a), SeedRef::Param(b)) if a == b)
                    || matches!((s, &k), (SeedRef::SlotValue(a), SeedRef::SlotValue(b)) if a == b)
            }) {
                seeds.push(k);
            }
            return;
        }
        match tree {
            RTree::Binary(_, l, r) => {
                collect(l, seeds);
                collect(r, seeds);
            }
            RTree::Ternary(c, t, e) => {
                collect(c, seeds);
                collect(t, seeds);
                collect(e, seeds);
            }
            RTree::RealCast(x) => collect(x, seeds),
            RTree::App(_, _, args) => args.iter().for_each(|a| collect(a, seeds)),
            RTree::Param(_) | RTree::SlotValue(_) | RTree::Lit(_) => {}
        }
    }
    let mut seed_refs = Vec::new();
    collect(tree, &mut seed_refs);

    let seed_temp = |k: &SeedRef| -> Val {
        let idx = seed_refs
            .iter()
            .position(|s| match (s, k) {
                (SeedRef::Param(a), SeedRef::Param(b)) => a == b,
                (SeedRef::SlotValue(a), SeedRef::SlotValue(b)) => a == b,
                _ => false,
            })
            .expect("seed ref collected in pass 1");
        Val::Temp(idx)
    };

    // Pass 2: emit steps, temps numbered after the seed.
    let base = seed_refs.len();
    let mut steps: Vec<AxiomInst> = Vec::new();
    let mut emit = |steps: &mut Vec<AxiomInst>, p: AxiomPure| -> Val {
        let v = Val::Temp(base + steps.len());
        steps.push(AxiomInst::Val(p));
        v
    };
    fn go(
        tree: &RTree,
        steps: &mut Vec<AxiomInst>,
        seed_temp: &impl Fn(&SeedRef) -> Val,
        emit: &mut impl FnMut(&mut Vec<AxiomInst>, AxiomPure) -> Val,
    ) -> Val {
        match tree {
            RTree::Param(i) => seed_temp(&SeedRef::Param(*i)),
            RTree::SlotValue(i) => seed_temp(&SeedRef::SlotValue(*i)),
            RTree::Lit(l) => Val::Literal(l.clone()),
            RTree::Binary(op, l, r) => {
                let l = go(l, steps, seed_temp, emit);
                let r = go(r, steps, seed_temp, emit);
                emit(steps, AxiomPure::Binary(*op, l, r))
            }
            RTree::Ternary(c, t, e) => {
                let c = go(c, steps, seed_temp, emit);
                let t = go(t, steps, seed_temp, emit);
                let e = go(e, steps, seed_temp, emit);
                emit(steps, AxiomPure::Ternary(c, t, e))
            }
            RTree::RealCast(x) => {
                let x = go(x, steps, seed_temp, emit);
                emit(steps, AxiomPure::RealCast(x))
            }
            RTree::App(func, tys, args) => {
                let args = args.iter().map(|a| go(a, steps, seed_temp, emit)).collect();
                emit(
                    steps,
                    AxiomPure::App {
                        func: *func,
                        type_args: tys.clone(),
                        args,
                    },
                )
            }
        }
    }
    let res = go(tree, &mut steps, &seed_temp, &mut emit);
    BodyRecipe {
        seed_refs,
        steps,
        res,
    }
}

/// Build an [`RTree`] for a pure inst from the body-temp → `RTree` map. `Deref`,
/// `Perm`, `Snap`, and `Fresh` are handled by the caller (they consult the
/// footprint slot table or are illegal), so this covers only the structural ops.
fn rtree_pure(ctx: &mut VerifyContext<'_>, map: &[RTree], pi: &PureInst) -> RTree {
    let tr = |v: &Val| -> RTree {
        match v {
            Val::Temp(n) => map[*n].clone_tree(),
            Val::Literal(l) => RTree::Lit(l.clone()),
        }
    };
    match pi {
        PureInst::Binary(op, l, r) => RTree::Binary(*op, Box::new(tr(l)), Box::new(tr(r))),
        PureInst::Ternary(c, t, e) => {
            RTree::Ternary(Box::new(tr(c)), Box::new(tr(t)), Box::new(tr(e)))
        }
        PureInst::RealCast(x) => RTree::RealCast(Box::new(tr(x))),
        PureInst::FunctionCall(fc) => RTree::App(
            crate::verify::func_registry::func_id_for_member(fc.function),
            fc.type_args.clone(),
            fc.args.iter().map(&tr).collect(),
        ),
        PureInst::AdtCons {
            adt,
            type_args,
            variant,
            args,
        } => RTree::App(
            ctx.alloc.cons(*adt, *variant),
            type_args.clone(),
            args.iter().map(&tr).collect(),
        ),
        PureInst::AdtProj {
            adt,
            type_args,
            variant,
            field,
            base,
        } => RTree::App(
            ctx.alloc.proj(*adt, *variant, *field),
            type_args.clone(),
            vec![tr(base)],
        ),
        PureInst::AdtTag {
            adt,
            type_args,
            base,
        } => RTree::App(ctx.alloc.tag(*adt), type_args.clone(), vec![tr(base)]),
        PureInst::Fresh | PureInst::Deref(..) | PureInst::Perm(..) | PureInst::Snap { .. } => {
            unreachable!("handled by purify_resource before rtree_pure")
        }
    }
}

impl RTree {
    fn clone_tree(&self) -> RTree {
        match self {
            RTree::Param(i) => RTree::Param(*i),
            RTree::SlotValue(i) => RTree::SlotValue(*i),
            RTree::Lit(l) => RTree::Lit(l.clone()),
            RTree::Binary(op, l, r) => {
                RTree::Binary(*op, Box::new(l.clone_tree()), Box::new(r.clone_tree()))
            }
            RTree::Ternary(c, t, e) => RTree::Ternary(
                Box::new(c.clone_tree()),
                Box::new(t.clone_tree()),
                Box::new(e.clone_tree()),
            ),
            RTree::RealCast(x) => RTree::RealCast(Box::new(x.clone_tree())),
            RTree::App(f, tys, args) => RTree::App(
                *f,
                tys.clone(),
                args.iter().map(|a| a.clone_tree()).collect(),
            ),
        }
    }

    /// `unwrap(proj_i(self))` — the value a footprint slot projects from a
    /// snapshot recipe (`FromSnap`/`Unfold`), mirroring `eval`'s
    /// `option_unwrap(proj_i(s))`.
    fn project_unwrap(
        self,
        ctx: &mut VerifyContext<'_>,
        resource: MemberId,
        i: usize,
        elem: Type,
    ) -> RTree {
        let proj = ctx.alloc.proj(resource, 0, i);
        let opt = RTree::App(proj, Vec::new(), vec![self]);
        let value = ctx.alloc.option_value();
        RTree::App(value, vec![elem], vec![opt])
    }
}

/// Turn a walked resource body into a pure [`ResourceDefinition`] recipe. Like
/// [`purify_function`] (params → recipe temps; `Deref` resolves to the value at
/// its address; `FromSnap`/`Unfold` reconstruct via the `HeapEvent` log), but
/// each `Combine` (`acc`) records a footprint slot whose value is a placeholder
/// (`SlotValue(i)`), and the body boolean plus each slot address/permission are
/// flattened into independent recipes.
fn purify_resource(
    ctx: &mut VerifyContext<'_>,
    resource: &Resource,
    body: &vmir::ResourceBody,
    state: &EvalState,
    events: &[HeapEvent],
) -> Result<crate::verify::cert::ResourceDefinition, VerifyError> {
    use crate::verify::cert::{ResourceDefinition, SlotRecipe};

    let n_params = resource.params.len();
    let mut map: Vec<RTree> = (0..n_params).map(RTree::Param).collect();
    // Address e-class → the value held there, as an RTree.
    let mut at: HashMap<egg::Id, RTree> = HashMap::new();
    let mut footprint: Vec<SlotRecipe> = Vec::new();
    let mut events = events.iter();

    let slot_elems =
        |ctx: &VerifyContext<'_>, resource: MemberId| -> Result<Vec<Type>, VerifyError> {
            let vmir::Declaration::Resource(r) = &ctx.decls[resource] else {
                return Err(VerifyError::DependencyFailed);
            };
            let Some(vmir::Snapshot::Concrete(snap)) = r.derive_snapshot() else {
                return Err(VerifyError::Unimplemented(
                    "purify: abstract resource footprint",
                ));
            };
            Ok(snap
                .variants
                .into_iter()
                .next()
                .unwrap()
                .field_types
                .iter()
                .map(|t| t.option_inner().unwrap_or(t).clone())
                .collect())
        };

    for inst in &body.insts {
        match &inst.kind {
            InstKind::Pure(_, PureInst::Deref(..)) => {
                // The deref's own live value e-class keys the recipe term (keying
                // by value, not address, keeps two-state derefs — `x.f` vs
                // `old(x.f)` — distinct).
                let ec = ctx.egraph.find(state.vals[map.len()]);
                let rt = at.get(&ec).ok_or(VerifyError::Unimplemented(
                    "purify: deref outside footprint",
                ))?;
                map.push(rt.clone_tree());
            }
            InstKind::Pure(_, PureInst::Perm(..)) => {
                return Err(VerifyError::Unimplemented("purify: perm in resource"));
            }
            // A nested heap-dependent call's `Snap`: the snapshot of the callee's
            // footprint, `cons(Some(v_i))` over the values read from the current
            // heap (a self-framed footprint is fully held, so each slot is Some).
            InstKind::Pure(_, PureInst::Snap { .. }) => {
                let Some(HeapEvent::Snap { resource, values }) = events.next() else {
                    unreachable!("Snap inst without a logged event");
                };
                let elems = slot_elems(ctx, *resource)?;
                let some_id = ctx.alloc.option_some();
                let cons_id = ctx.alloc.cons(*resource, 0);
                let mut members = Vec::with_capacity(values.len());
                for (i, &value) in values.iter().enumerate() {
                    let v_rt = at
                        .get(&ctx.egraph.find(value))
                        .ok_or(VerifyError::Unimplemented(
                            "purify: snap value outside footprint",
                        ))?
                        .clone_tree();
                    members.push(RTree::App(some_id, vec![elems[i].clone()], vec![v_rt]));
                }
                map.push(RTree::App(cons_id, Vec::new(), members));
            }
            InstKind::Pure(_, PureInst::Fresh) => {
                unreachable!("resource body may not contain Fresh (method-only)");
            }
            InstKind::Pure(_, pi) => {
                let rt = rtree_pure(ctx, &map, pi);
                map.push(rt);
            }
            // `acc(loc, perm)`: a footprint slot. Its value is the placeholder
            // `SlotValue(i)` (supplied at graft time); the slot records recipes for
            // its address and permission.
            InstKind::Heap(HeapInst::Combine {
                sign: Sign::Add,
                loc,
                perm,
                ..
            }) => {
                let i = footprint.len();
                // The address is always a `FunctionCall` result (a temp); the
                // permission may be a literal (`1/1`).
                let Val::Temp(loc_t) = loc else {
                    unreachable!("acc address is a temp");
                };
                let kind = state
                    .loc_kind(loc)
                    .expect("acc location must be Addr-typed");
                let elem = kind.value.clone();
                let addr = flatten(&map[*loc_t]);
                let perm_rt = match perm {
                    Val::Temp(n) => map[*n].clone_tree(),
                    Val::Literal(l) => RTree::Lit(l.clone()),
                };
                let perm = flatten(&perm_rt);
                // Key the slot value by the acc's minted value e-class (logged),
                // so a later `Deref` of it resolves to this `SlotValue(i)`.
                let Some(HeapEvent::Acc { value }) = events.next() else {
                    unreachable!("acc inst without a logged Acc event");
                };
                at.insert(ctx.egraph.find(*value), RTree::SlotValue(i));
                footprint.push(SlotRecipe {
                    kind,
                    elem,
                    addr,
                    perm,
                });
            }
            // Two-state resource entry / nested reconstruction: slot values project
            // from the snapshot recipe (as in `purify_function`).
            InstKind::Heap(HeapInst::FromSnap { resource, snap, .. }) => {
                let Some(HeapEvent::FromSnap { values }) = events.next() else {
                    unreachable!("FromSnap inst without a logged event");
                };
                let snap_rt = match snap {
                    Val::Temp(n) => map[*n].clone_tree(),
                    Val::Literal(l) => RTree::Lit(l.clone()),
                };
                let elems = slot_elems(ctx, *resource)?;
                for (i, &value) in values.iter().enumerate() {
                    let rt =
                        snap_rt
                            .clone_tree()
                            .project_unwrap(ctx, *resource, i, elems[i].clone());
                    at.insert(ctx.egraph.find(value), rt);
                }
            }
            InstKind::Heap(HeapInst::Unfold { call, .. }) => {
                let Some(HeapEvent::Unfold { consumed, values }) = events.next() else {
                    unreachable!("Unfold inst without a logged event");
                };
                let s = at
                    .get(&ctx.egraph.find(*consumed))
                    .ok_or(VerifyError::Unimplemented(
                        "purify: unfold of unheld predicate",
                    ))?
                    .clone_tree();
                let elems = slot_elems(ctx, call.resource)?;
                for (j, &value) in values.iter().enumerate() {
                    let rt = s
                        .clone_tree()
                        .project_unwrap(ctx, call.resource, j, elems[j].clone());
                    at.insert(ctx.egraph.find(value), rt);
                }
            }
            InstKind::Heap(_) => {
                return Err(VerifyError::Unimplemented(
                    "purify: unsupported heap inst in resource",
                ));
            }
            // Contract-stitched assume/assert produce no value and don't affect the
            // body result; drop them.
            InstKind::Assume(_) | InstKind::Assert(_) => {}
            InstKind::Refute(_) => unreachable!("resource body may not contain refute"),
        }
    }

    // The body boolean is the second component of the result tuple.
    let bool_rt = match &body.res.1 {
        Val::Temp(n) => map[*n].clone_tree(),
        Val::Literal(l) => RTree::Lit(l.clone()),
    };
    Ok(ResourceDefinition {
        footprint,
        bool: flatten(&bool_rt),
    })
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
        InstKind::Pure(ty, PureInst::Binary(BinOp::Div | BinOp::Mod, _, r)) => {
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
