//! Lower a `typed::Method` body into a `vmir::Method` (a flat
//! `Vec<MethodInst>`). Straight-line only.

use std::collections::HashMap;

use lasso::Spur;

use crate::translate::pure_exp::{self, Sink};
use crate::translate::resource::{self, SpatialMode};
use crate::translate::{Builder, TranslationError, lower_type};
use crate::viper::typed;
use crate::vmir::{self, HeapInst, HeapVal, PureInst, ResourceCall, Type, Val};

pub(crate) fn lower_method(
    b: &Builder<'_>,
    m: &typed::Method,
    body: &typed::StmtBlock,
) -> Result<vmir::Method, TranslationError> {
    let mut sink = Sink::new(0, 0);
    let mut env: HashMap<Spur, Val> = HashMap::new();

    // Emit fresh values for params and rets inline. The method has no
    // signature on the VMIR side — params/rets are just initial Fresh insts.
    let mut param_vals: Vec<Val> = Vec::with_capacity(m.params.len());
    for p in &m.params {
        let v = sink.emit_pure(lower_type(&p.ty), PureInst::Fresh);
        env.insert(p.name.0, v.clone());
        param_vals.push(v);
    }
    let mut ret_vals: Vec<Val> = Vec::with_capacity(m.rets.len());
    for r in &m.rets {
        let v = sink.emit_pure(lower_type(&r.ty), PureInst::Fresh);
        env.insert(r.name.0, v.clone());
        ret_vals.push(v);
    }

    let mut current_heap: HeapVal = HeapVal::Empty;

    // Inhale this method's own precondition: `h := current + acc self@requires`
    // (implicitly assumes the requires bool).
    if let Some(&req_id) = b.method_requires.get(&m.name.0) {
        current_heap = emit_resource_combine(
            b,
            &mut sink,
            vmir::Sign::Add,
            req_id,
            current_heap,
            param_vals.clone(),
        );
    }

    // Baseline for unlabeled `old`: the heap right after the precondition is
    // inhaled (`HeapVal::Empty` when there is no precondition). `labeled`
    // accumulates the heap captured at each `label L` as lowering proceeds.
    let baseline = current_heap;
    let mut labeled: HashMap<Spur, HeapVal> = HashMap::new();
    for stmt in &body.0 {
        current_heap = lower_stmt(
            b,
            &mut env,
            &mut sink,
            current_heap,
            baseline,
            &mut labeled,
            stmt,
        )?;
    }

    // Exhale this method's own postcondition: `h := current - acc self@ensures`
    // (implicitly asserts the ensures bool).
    if let Some(&ens_id) = b.method_ensures.get(&m.name.0) {
        let mut ens_args = param_vals;
        ens_args.extend(ret_vals);
        let _h_new =
            emit_resource_combine(b, &mut sink, vmir::Sign::Sub, ens_id, current_heap, ens_args);
    }

    Ok(vmir::Method { insts: sink.insts })
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
                let ty = lower_type(&id.ty);
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
            let ret_types: Vec<vmir::Type> = idents.iter().map(|i| lower_type(&i.ty)).collect();
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
                    Ok(sink.emit_heap_guarded(HeapInst::Assign(
                        current_heap,
                        vmir::Assign { loc: addr, val: v },
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
                resource::lower_assertion_bool(b, env, sink, current_heap, Some(&old), e)?
            {
                sink.emit_assert(v);
            }
            Ok(current_heap)
        }
        S::Assume(e) => {
            let old = pure_exp::OldHeaps {
                baseline,
                labeled: &*labeled,
            };
            if let Some(v) =
                resource::lower_assertion_bool(b, env, sink, current_heap, Some(&old), e)?
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
        // Inhale: add the assertion's heap delta to the current heap and assume
        // its boolean. Heap-dependent sub-expressions are evaluated against the
        // growing heap (`ReadHeap::Track`), so later conjuncts can observe the
        // permissions just inhaled.
        S::Inhale(e) => {
            let old = pure_exp::OldHeaps {
                baseline,
                labeled: &*labeled,
            };
            let (h_out, bv) = resource::lower_spatial(
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
            let (h_out, bv) = resource::lower_spatial(
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
                sink.emit_assert(v);
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
                heap = sink.emit_heap(HeapInst::Combine {
                    base: heap,
                    sign: vmir::Sign::Add,
                    target: vmir::Target::Loc(loc),
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
    let pred_id = *b.name_map.get(&pwp.pred_call.name.0).ok_or_else(|| {
        TranslationError::UnknownIdent(b.interner.resolve(&pwp.pred_call.name.0).to_string())
    })?;
    let old = pure_exp::OldHeaps { baseline, labeled };
    let hctx = pure_exp::HeapCtx::same_with_old(current_heap, &old);
    let mut args = Vec::with_capacity(pwp.pred_call.args.len());
    for a in &pwp.pred_call.args {
        args.push(pure_exp::lower(b, env, sink, hctx, a)?);
    }
    let perm = pure_exp::lower(b, env, sink, hctx, &pwp.perm)?;
    // Predicates are self-framed (context-free): no ctx heap.
    let call = ResourceCall {
        resource: pred_id,
        ctx_heap: None,
        args,
    };
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

    // Exhale precondition (if present): `h := heap - acc m@requires(args)`
    // (implicitly asserts the requires bool).
    if let Some(&req_id) = b.method_requires.get(&call.name.0) {
        heap = emit_resource_combine(b, sink, vmir::Sign::Sub, req_id, heap, args.clone());
    }

    // Allocate fresh return values BEFORE the post-condition inhale.
    let mut ret_vals: Vec<Val> = Vec::with_capacity(ret_names.len());
    for (spur, ty) in ret_names.iter().zip(ret_types.iter()) {
        let v = sink.emit_pure(ty.clone(), PureInst::Fresh);
        env.insert(*spur, v.clone());
        ret_vals.push(v);
    }

    // Inhale postcondition (if present): `h := heap + acc m@ensures(args, rets)`
    // (implicitly assumes the ensures bool).
    if let Some(&ens_id) = b.method_ensures.get(&call.name.0) {
        let mut ens_args = args.clone();
        ens_args.extend(ret_vals.iter().cloned());
        heap = emit_resource_combine(b, sink, vmir::Sign::Add, ens_id, heap, ens_args);
    }

    Ok(heap)
}

/// Emit `h := base <sign> acc <resource>(args) write`: combine the resource's
/// full-permission delta onto `base`, implicitly assuming (`Add`) or asserting
/// (`Sub`) its boolean. Returns the resulting heap.
///
/// The ctx heap is supplied (`Some(base)`) only when the called resource has a
/// precondition resource (two-state, e.g. `@ensures`); self-framed resources
/// (`@requires`, predicates) are context-free (`None`). The verifier currently
/// ignores it, so it is bookkeeping until ctx heaps become live.
fn emit_resource_combine(
    b: &Builder<'_>,
    sink: &mut Sink,
    sign: vmir::Sign,
    resource: vmir::MemberId,
    base: HeapVal,
    args: Vec<Val>,
) -> HeapVal {
    let ctx_heap = b.is_ctx_resource(resource).then_some(base);
    sink.emit_resource_combine(
        base,
        sign,
        ResourceCall {
            resource,
            ctx_heap,
            args,
        },
        vmir::write(),
    )
}
