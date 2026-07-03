//! Lower a `typed::Method` body into a `vmir::Method` (a flat `Vec<Inst>`).
//! Control flow is linearized through the basic-block CFG (`viper::cfg`):
//! blocks are walked in topological order, each lowered under its reaching path
//! condition, with phi (`ite`) nodes at joins and a single linear heap.

use std::collections::HashMap;

use lasso::Spur;
use typed_index_collections::TiVec;

use crate::translate::reach::{and_val, block_reach, build_entry_env, not_val};
use crate::translate::sink::Sink;
use crate::translate::spatial::{self, SpatialMode};
use crate::translate::{Builder, TranslationError, lower_type, pure_exp, resource};
use crate::viper::cfg::{self, BlockId, EdgeSide, Terminator};
use crate::viper::typed;
use crate::vmir::{
    self, HeapInst, HeapVal, PathConds, Polarity, PureInst, ResourceCall, TRUE, Type, Val,
};

pub(crate) fn lower_method(
    b: &Builder<'_>,
    m: &typed::Method,
    name: Spur,
    body: &typed::StmtBlock,
) -> Result<vmir::Method, TranslationError> {
    // Control flow is linearized through the basic-block CFG: blocks are walked
    // in topological order, each lowered under its reaching path condition, with
    // phi (`ite`) nodes reconciling variables at joins. The heap is *not* phi'd —
    // it threads linearly through the walk, off-path contributions gated to 0
    // permission (see `Sink::gate_perm`).
    let cfg = cfg::build_cfg(body).map_err(|_| {
        TranslationError::Unsupported("method control flow (loop or undefined label)")
    })?;

    let mut sink = Sink::new(0, 0);

    // Initial environment: fresh values for params and rets. The method has no
    // signature on the VMIR side — params/rets are just initial Fresh insts.
    let mut init_env: HashMap<Spur, Val> = HashMap::new();
    let mut param_vals: Vec<Val> = Vec::with_capacity(m.params.len());
    for p in &m.params {
        let v = sink.emit_pure(b.lower_type(&p.ty), PureInst::Fresh);
        init_env.insert(p.name.0, v.clone());
        param_vals.push(v);
    }
    let mut ret_names: Vec<Spur> = Vec::with_capacity(m.rets.len());
    for r in &m.rets {
        let v = sink.emit_pure(b.lower_type(&r.ty), PureInst::Fresh);
        init_env.insert(r.name.0, v);
        ret_names.push(r.name.0);
    }

    // Types of every method-scoped variable, needed to type phi nodes at joins.
    let mut var_types: HashMap<Spur, Type> = HashMap::new();
    for p in &m.params {
        var_types.insert(p.name.0, b.lower_type(&p.ty));
    }
    for r in &m.rets {
        var_types.insert(r.name.0, b.lower_type(&r.ty));
    }
    collect_var_types(&b.name_map, &body.0, &mut var_types);

    // Inhale this method's own precondition into the linear heap that every
    // block threads: `h, s := current + acc self#requires`. The yielded
    // snapshot is the method's pre-state handle, passed to the `#ensures`
    // exhale at every exit.
    let mut current_heap: HeapVal = HeapVal::Empty;
    let mut req_snap: Option<Val> = None;
    if let Some(req_id) = b.method_requires(m.name.0) {
        let (h, s) = emit_resource_combine(
            b,
            &mut sink,
            vmir::Sign::Add,
            req_id,
            current_heap,
            param_vals.clone(),
        );
        current_heap = h;
        req_snap = s;
    }
    // Baseline for unlabeled `old`: the post-requires-inhale heap.
    let baseline = current_heap;
    let mut labeled: HashMap<Spur, HeapVal> = HashMap::new();

    let order = cfg.topo_order();
    let preds = cfg.predecessors();
    let reachable = cfg.reachable();

    // Per-block reaching condition (`pc`), its materialized boolean `Val` (for
    // edges/phis), and the branch condition `Val` of a `Branch` block.
    let n = cfg.blocks.len();
    let mut reach_pc: TiVec<BlockId, PathConds> = (0..n).map(|_| PathConds::default()).collect();
    let mut reach_val: TiVec<BlockId, Val> = (0..n).map(|_| TRUE).collect();
    let mut cond_val: TiVec<BlockId, Option<Val>> = (0..n).map(|_| None).collect();
    let mut exit_env: HashMap<BlockId, HashMap<Spur, Val>> = HashMap::new();

    for bid in order {
        if !reachable.contains(&bid) {
            continue;
        }

        let (pc, rval, env) = if bid == cfg.entry {
            (PathConds::default(), TRUE, init_env.clone())
        } else {
            // Incoming edges from reachable predecessors: (pred, edge_val, edge_pc).
            let edges: Vec<(BlockId, Val, PathConds)> = preds[bid]
                .iter()
                .filter(|(p, _)| reachable.contains(p))
                .map(|(p, side)| {
                    let rpc = reach_pc[*p].clone();
                    let rv = reach_val[*p].clone();
                    match side {
                        EdgeSide::Goto => (*p, rv, rpc),
                        EdgeSide::Then => {
                            let c = cond_val[*p].clone().expect("branch pred has a condition");
                            let mut epc = rpc;
                            epc.conds.push((c.clone(), Polarity::Positive));
                            (*p, and_val(&mut sink, rv, c), epc)
                        }
                        EdgeSide::Else => {
                            let c = cond_val[*p].clone().expect("branch pred has a condition");
                            let mut epc = rpc;
                            epc.conds.push((c.clone(), Polarity::Negative));
                            let nc = not_val(&mut sink, c);
                            (*p, and_val(&mut sink, rv, nc), epc)
                        }
                    }
                })
                .collect();

            let (pc, rval) = block_reach(&mut sink, &edges);
            let edge_vals: Vec<(BlockId, Val)> =
                edges.iter().map(|(p, ev, _)| (*p, ev.clone())).collect();
            let env = build_entry_env(&mut sink, &edge_vals, &exit_env, &var_types);
            (pc, rval, env)
        };
        reach_pc[bid] = pc.clone();
        reach_val[bid] = rval;

        // `label L` captures the heap at block entry for later `old[L]`.
        if let Some(l) = cfg.blocks[bid].label {
            labeled.insert(l, current_heap);
        }

        // Lower the block's statements and terminator under its path condition.
        let mut env = env;
        let blk = &cfg.blocks[bid];
        let (new_heap, cond): (HeapVal, Option<Val>) = sink.with_conds(&pc, |sink| {
            let mut heap = current_heap;
            for stmt in &blk.stmts {
                heap = lower_stmt(b, &mut env, sink, heap, baseline, &mut labeled, stmt)?;
            }
            let cond = match &blk.term {
                Terminator::Branch { cond, .. } => {
                    let old = pure_exp::OldHeaps {
                        baseline,
                        labeled: &labeled,
                    };
                    let cv = pure_exp::lower(
                        b,
                        &env,
                        sink,
                        pure_exp::HeapCtx::same_with_old(heap, &old),
                        cond,
                    )?;
                    Some(cv)
                }
                // At each exit, exhale the postcondition gated by this block's
                // pc against the final values of the return variables.
                Terminator::Return => {
                    if let Some(ens_id) = b.method_ensures(m.name.0) {
                        let mut ens_args = param_vals.clone();
                        for name in &ret_names {
                            ens_args.push(env.get(name).cloned().expect("return var bound"));
                        }
                        // A two-state `#ensures` reads the pre-state through its
                        // trailing snapshot parameter — the snapshot yielded by
                        // the entry `#requires` inhale.
                        if b.is_ctx_resource(ens_id) {
                            let s = req_snap
                                .clone()
                                .expect("two-state ensures implies an inhaled requires");
                            ens_args.push(s);
                        }
                        // `base` is the exit heap (delta subtracted from it).
                        (heap, _) =
                            emit_resource_combine(b, sink, vmir::Sign::Sub, ens_id, heap, ens_args);
                    }
                    None
                }
                Terminator::Goto(_) => None,
            };
            Ok::<_, TranslationError>((heap, cond))
        })?;
        current_heap = new_heap;
        cond_val[bid] = cond;
        exit_env.insert(bid, env);
    }

    Ok(vmir::Method {
        name,
        insts: sink.insts,
    })
}

/// Collect the VMIR type of every method-scoped `var` declaration (plus the
/// already-seeded params/rets), recursing through `if`/block statements. Viper
/// locals are method-scoped, so a single flat map suffices for phi typing.
fn collect_var_types(
    names: &HashMap<Spur, vmir::MemberId>,
    stmts: &[typed::Statement],
    out: &mut HashMap<Spur, Type>,
) {
    use typed::Statement as S;
    for s in stmts {
        match s {
            S::Var(idents, _) => {
                for id in idents {
                    out.insert(id.name.0, lower_type(names, &[], &id.ty));
                }
            }
            S::If(_, then, els) => {
                collect_var_types(names, &then.0, out);
                if let Some(e) = els {
                    collect_var_types(names, &e.0, out);
                }
            }
            S::Block(inner) => collect_var_types(names, &inner.0, out),
            _ => {}
        }
    }
}

fn lower_stmt(
    b: &Builder<'_>,
    env: &mut HashMap<Spur, Val>,
    sink: &mut Sink,
    current_heap: HeapVal,
    baseline: HeapVal,
    labeled: &mut HashMap<Spur, HeapVal>,
    stmt: &typed::Statement,
) -> Result<HeapVal, TranslationError> {
    use typed::Statement as S;
    match stmt {
        S::Var(idents, None) => {
            for id in idents {
                let ty = b.lower_type(&id.ty);
                let v = sink.emit_pure(ty, PureInst::Fresh);
                env.insert(id.name.0, v);
            }
            Ok(current_heap)
        }
        S::Var(idents, Some(typed::AssignRhs::Exp(pure))) => {
            if idents.len() != 1 {
                return Err(TranslationError::Unsupported("multi-LHS var := exp"));
            }
            let old = pure_exp::OldHeaps {
                baseline,
                labeled: &*labeled,
            };
            let v = pure_exp::lower(
                b,
                env,
                sink,
                pure_exp::HeapCtx::same_with_old(current_heap, &old),
                pure,
            )?;
            env.insert(idents[0].name.0, v);
            Ok(current_heap)
        }
        S::Var(idents, Some(typed::AssignRhs::MethodCall(call))) => {
            let ret_names: Vec<Spur> = idents.iter().map(|i| i.name.0).collect();
            let ret_types: Vec<vmir::Type> = idents.iter().map(|i| b.lower_type(&i.ty)).collect();
            lower_method_call(
                b,
                env,
                sink,
                current_heap,
                baseline,
                labeled,
                call,
                &ret_names,
                &ret_types,
            )
        }
        S::Assign(lhss, typed::AssignRhs::MethodCall(call)) => {
            let mut ret_names = Vec::with_capacity(lhss.len());
            for lhs in lhss {
                match lhs {
                    typed::AssignLhs::Var(name) => ret_names.push(name.0),
                    typed::AssignLhs::Field(_, _) => {
                        return Err(TranslationError::Unsupported("field lvalue"));
                    }
                }
            }
            let ret_types: Vec<vmir::Type> = ret_names
                .iter()
                .map(|spur| {
                    env.get(spur)
                        .map(|_| ())
                        .ok_or_else(|| {
                            TranslationError::UnknownIdent(b.interner.resolve(spur).to_string())
                        })
                        // type is recovered from env via name lookup, but env stores Val.
                        // For Phase 2 minimal scope, accept that the LHS variables have been
                        // declared earlier with `var` and assume their types match the
                        // callee's return signature. We use Fresh-typed Int as a placeholder
                        // only when we cannot resolve — better solution lands with proper type
                        // tracking in the env.
                        .map(|_| vmir::Type::Int)
                })
                .collect::<Result<_, _>>()?;
            lower_method_call(
                b,
                env,
                sink,
                current_heap,
                baseline,
                labeled,
                call,
                &ret_names,
                &ret_types,
            )
        }
        S::Assign(lhss, typed::AssignRhs::Exp(pure)) => {
            if lhss.len() != 1 {
                return Err(TranslationError::Unsupported("multi-LHS assign := exp"));
            }
            let old = pure_exp::OldHeaps {
                baseline,
                labeled: &*labeled,
            };
            let hctx = pure_exp::HeapCtx::same_with_old(current_heap, &old);
            let v = pure_exp::lower(b, env, sink, hctx, pure)?;
            match &lhss[0] {
                typed::AssignLhs::Var(n) => {
                    env.insert(n.0, v);
                    Ok(current_heap)
                }
                // `e.f := v`: mutate the heap at `field@addr(e)` to `v`. The
                // `Assign` is guarded — it requires write permission at the loc.
                typed::AssignLhs::Field(base, fname) => {
                    let base_val = pure_exp::lower(b, env, sink, hctx, base)?;
                    let addr = resource::field_addr(b, sink, base_val, fname.0)?;
                    // Inside an `if` arm the heap is a single timeline, so the
                    // write must be conditional in its *value*: `pc ? v : old`.
                    let val = if sink.branch_conds().is_empty() {
                        v
                    } else {
                        let ty = b.lower_type(&pure.ty);
                        let old = sink.emit_pure_guarded(
                            ty.clone(),
                            PureInst::Deref(current_heap, addr.clone()),
                        );
                        sink.gate_value(v, old, ty)
                    };
                    Ok(sink.emit_heap_guarded(HeapInst::Assign(
                        current_heap,
                        vmir::Assign { loc: addr, val },
                    )))
                }
            }
        }
        S::Var(idents, Some(typed::AssignRhs::New(sof))) => {
            if idents.len() != 1 {
                return Err(TranslationError::Unsupported("multi-LHS var := new"));
            }
            lower_new(b, env, sink, current_heap, idents[0].name.0, sof)
        }
        S::Assign(lhss, typed::AssignRhs::New(sof)) => {
            if lhss.len() != 1 {
                return Err(TranslationError::Unsupported("multi-LHS assign := new"));
            }
            let name = match &lhss[0] {
                typed::AssignLhs::Var(n) => n.0,
                typed::AssignLhs::Field(_, _) => {
                    return Err(TranslationError::Unsupported("field lvalue"));
                }
            };
            lower_new(b, env, sink, current_heap, name, sof)
        }
        S::If(_, _, _) => Err(TranslationError::Unsupported("if statement")),
        S::Block(_) => Err(TranslationError::Unsupported("nested block")),
        S::Fold(pwp) => lower_fold_unfold(b, env, sink, current_heap, baseline, labeled, pwp, true),
        S::Unfold(pwp) => {
            lower_fold_unfold(b, env, sink, current_heap, baseline, labeled, pwp, false)
        }
        // Source-level assert/assume are non-destructive: the assertion is
        // reduced to a boolean over the current heap (each `acc(loc, p)` becomes
        // `perm(loc) >= p`) and asserted/assumed. The heap is unchanged.
        S::Assert(e) => {
            let old = pure_exp::OldHeaps {
                baseline,
                labeled: &*labeled,
            };
            if let Some(v) =
                spatial::lower_assertion_bool(b, env, sink, current_heap, Some(&old), e)?
            {
                // The obligation is checked in the current heap.
                sink.with_heap(current_heap, |sink| sink.emit_assert(v));
            }
            Ok(current_heap)
        }
        S::Refute(e) => {
            let old = pure_exp::OldHeaps {
                baseline,
                labeled: &*labeled,
            };
            if let Some(v) =
                spatial::lower_assertion_bool(b, env, sink, current_heap, Some(&old), e)?
            {
                sink.with_heap(current_heap, |sink| sink.emit_refute(v));
            }
            Ok(current_heap)
        }
        S::Assume(e) => {
            let old = pure_exp::OldHeaps {
                baseline,
                labeled: &*labeled,
            };
            if let Some(v) =
                spatial::lower_assertion_bool(b, env, sink, current_heap, Some(&old), e)?
            {
                sink.emit_assume(v);
            }
            Ok(current_heap)
        }
        // A `label L` marks the current heap state for later `old[L](...)`.
        S::Label(l) => {
            labeled.insert(*l, current_heap);
            Ok(current_heap)
        }
        // Control flow is linearized via the CFG (`viper::cfg`) before reaching
        // straight-line lowering; a bare `goto` here is not yet wired.
        S::Goto(_) => Err(TranslationError::Unsupported("goto statement")),
        // Inhale: add the assertion's heap delta to the current heap and assume
        // its boolean. Heap-dependent sub-expressions are evaluated against the
        // growing heap (`ReadHeap::Track`), so later conjuncts can observe the
        // permissions just inhaled.
        S::Inhale(e) => {
            let old = pure_exp::OldHeaps {
                baseline,
                labeled: &*labeled,
            };
            let (h_out, bv) = spatial::lower_spatial(
                b,
                env,
                sink,
                current_heap,
                SpatialMode::Inhale,
                Some(&old),
                e,
            )?;
            if let Some(v) = bv {
                sink.emit_assume(v);
            }
            Ok(h_out)
        }
        // Exhale: subtract the assertion's heap delta (accumulated from
        // `Empty`) from the current heap and assert its boolean. All
        // heap-dependent sub-expressions are evaluated against the heap from
        // *before* the exhale (`ReadHeap::Fixed(current_heap)`), since the
        // permissions are still held at that point.
        S::Exhale(e) => {
            // Subtraction happens inside `lower_spatial` (left-to-right), so a
            // `perm` in the assertion observes the running reduced heap, while
            // value reads use the fixed pre-exhale `current_heap`.
            let old = pure_exp::OldHeaps {
                baseline,
                labeled: &*labeled,
            };
            let (h_out, bv) = spatial::lower_spatial(
                b,
                env,
                sink,
                current_heap,
                SpatialMode::Exhale {
                    value_heap: current_heap,
                },
                Some(&old),
                e,
            )?;
            if let Some(v) = bv {
                // The exhale's boolean is over the pre-exhale state, so it is
                // checked in `current_heap` (not the reduced `h_out`).
                sink.with_heap(current_heap, |sink| sink.emit_assert(v));
            }
            Ok(h_out)
        }
    }
}

/// Lower `lhs := new(fields)`: allocate a fresh `Ref`, bind it to `lhs`, and
/// inhale full permission to each listed field (`acc(lhs.f, write)`), adding the
/// chunks to the current heap. `new(*)` is not yet supported.
fn lower_new(
    b: &Builder<'_>,
    env: &mut HashMap<Spur, Val>,
    sink: &mut Sink,
    current_heap: HeapVal,
    lhs: Spur,
    sof: &typed::StarOrFields,
) -> Result<HeapVal, TranslationError> {
    let v = sink.emit_pure(Type::Ref, PureInst::Fresh);
    env.insert(lhs, v.clone());

    match sof {
        typed::StarOrFields::Fields(fields) => {
            let mut heap = current_heap;
            for f in fields {
                let (loc, perm) = resource::field_acc(b, sink, v.clone(), f.0, vmir::write())?;
                let perm = sink.gate_perm(perm);
                heap = sink.emit_heap(HeapInst::Combine {
                    base: heap,
                    sign: vmir::Sign::Add,
                    loc,
                    perm,
                });
            }
            Ok(heap)
        }
        typed::StarOrFields::Star => Err(TranslationError::Unsupported("new(*)")),
    }
}

/// Lower `fold P(args)` / `unfold P(args)` to a `HeapInst::Fold`/`Unfold`. The
/// predicate id, args, and perm come from the statement; the resulting heap is
/// the new working heap.
fn lower_fold_unfold(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    current_heap: HeapVal,
    baseline: HeapVal,
    labeled: &HashMap<Spur, HeapVal>,
    pwp: &typed::PredicateWithPerm<typed::MethodBodyExt>,
    is_fold: bool,
) -> Result<HeapVal, TranslationError> {
    let old = pure_exp::OldHeaps { baseline, labeled };
    let hctx = pure_exp::HeapCtx::same_with_old(current_heap, &old);
    let (call, perm) = pure_exp::lower_pred_call(b, env, sink, hctx, pwp)?;
    let perm = sink.gate_perm(perm);
    let inst = if is_fold {
        HeapInst::Fold {
            base: current_heap,
            call,
            perm,
        }
    } else {
        HeapInst::Unfold {
            base: current_heap,
            call,
            perm,
        }
    };
    Ok(sink.emit_heap_guarded(inst))
}

fn lower_method_call(
    b: &Builder<'_>,
    env: &mut HashMap<Spur, Val>,
    sink: &mut Sink,
    current_heap: HeapVal,
    baseline: HeapVal,
    labeled: &HashMap<Spur, HeapVal>,
    call: &typed::Call<typed::MethodBodyExt>,
    ret_names: &[Spur],
    ret_types: &[vmir::Type],
) -> Result<HeapVal, TranslationError> {
    // Lower argument expressions (may contain `old(...)`).
    let old = pure_exp::OldHeaps { baseline, labeled };
    let mut args: Vec<Val> = Vec::with_capacity(call.args.len());
    for a in &call.args {
        args.push(pure_exp::lower(
            b,
            env,
            sink,
            pure_exp::HeapCtx::same_with_old(current_heap, &old),
            a,
        )?);
    }

    let mut heap = current_heap;

    // Exhale precondition (if present): `h, s := heap - acc m#requires(args)`
    // (implicitly asserts the requires bool). The yielded snapshot captures the
    // callee's pre-state (the consumed chunk values) for the ensures inhale.
    let mut req_snap: Option<Val> = None;
    if let Some(req_id) = b.method_requires(call.name.0) {
        let (h, s) = emit_resource_combine(b, sink, vmir::Sign::Sub, req_id, heap, args.clone());
        heap = h;
        req_snap = s;
    }

    // Allocate fresh return values BEFORE the post-condition inhale.
    let mut ret_vals: Vec<Val> = Vec::with_capacity(ret_names.len());
    for (spur, ty) in ret_names.iter().zip(ret_types.iter()) {
        let v = sink.emit_pure(ty.clone(), PureInst::Fresh);
        env.insert(*spur, v.clone());
        ret_vals.push(v);
    }

    // Inhale postcondition (if present): `h := heap + acc m#ensures(args, rets[, s])`
    // (implicitly assumes the ensures bool). A two-state `#ensures` reads the
    // callee's pre-state through its trailing snapshot argument — the snapshot
    // yielded by the precondition exhale above.
    if let Some(ens_id) = b.method_ensures(call.name.0) {
        let mut ens_args = args.clone();
        ens_args.extend(ret_vals.iter().cloned());
        if b.is_ctx_resource(ens_id) {
            let s = req_snap
                .clone()
                .expect("two-state ensures implies an exhaled requires");
            ens_args.push(s);
        }
        (heap, _) = emit_resource_combine(b, sink, vmir::Sign::Add, ens_id, heap, ens_args);
    }

    Ok(heap)
}

/// Emit `h[, s] := base <sign> acc <resource>(args) write`: combine the
/// resource's full-permission delta onto `base`, implicitly assuming (`Add`) or
/// asserting (`Sub`) its boolean. Returns the resulting heap plus, for a
/// **self-framed** callee, the snapshot `Val` the inst yields (the pre-state
/// handle passed on as the trailing argument of a two-state resource call —
/// e.g. `m#requires`'s snapshot feeding `m#ensures`). A two-state callee
/// yields no snapshot.
fn emit_resource_combine(
    b: &Builder<'_>,
    sink: &mut Sink,
    sign: vmir::Sign,
    resource: vmir::MemberId,
    base: HeapVal,
    args: Vec<Val>,
) -> (HeapVal, Option<Val>) {
    let yields_snap = !b.is_ctx_resource(resource);
    // Gate the permission by the current branch path condition so a contract
    // inhaled/exhaled inside an `if` arm contributes nothing on the other path
    // (the empty top-level pc leaves `write` unchanged).
    let perm = sink.gate_perm(vmir::write());
    sink.emit_resource_combine(
        base,
        sign,
        ResourceCall { resource, args },
        perm,
        yields_snap,
    )
}
