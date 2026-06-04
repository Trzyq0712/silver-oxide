//! Lower a `typed::Method` body into a `vmir::Method` (a flat
//! `Vec<MethodInst>`). Straight-line only.

use std::collections::HashMap;

use lasso::Spur;

use crate::translate::pure_exp::{self, Sink};
use crate::translate::resource::{self, SpatialMode};
use crate::translate::{Builder, TranslationError, lower_type};
use crate::viper::typed;
use crate::vmir::{
    self, HeapInst, HeapVal, Inst, InstExt, InstKind, MethodCtx, PureInst, ResourceCall, Type, Val,
};

pub(crate) fn lower_method(
    b: &Builder<'_>,
    m: &typed::Method,
    body: &typed::StmtBlock,
) -> Result<vmir::Method, TranslationError> {
    let mut sink = Sink::<MethodCtx>::new(0, 0);
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
    // Heap delta produced by this method's `@requires` resource call,
    // forwarded as the `@ensures` resource's ctx_heap (since `@ensures`
    // declares `requires: Some(@requires)`). `HeapVal::Empty` when the
    // method has no precondition.
    let mut pre_heap: HeapVal = HeapVal::Empty;

    // Inhale this method's own precondition: call self@requires, add delta,
    // assume bool. The `@requires` resource has no precondition itself, so
    // its ctx_heap is `HeapVal::Empty`.
    if let Some(&req_id) = b.method_requires.get(&m.name.0) {
        let (h_pre, b_pre) =
            emit_resource_call(&mut sink, req_id, HeapVal::Empty, param_vals.clone());
        let h_new = sink.emit_heap(HeapInst::Add(current_heap, h_pre));
        sink.emit_ext(InstExt::Assume(b_pre));
        current_heap = h_new;
        pre_heap = h_pre;
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

    // Exhale this method's own postcondition: call self@ensures, sub delta,
    // assert bool. Its ctx_heap is the requires delta (`pre_heap`).
    if let Some(&ens_id) = b.method_ensures.get(&m.name.0) {
        let mut ens_args = param_vals;
        ens_args.extend(ret_vals);
        let (h_post, b_post) = emit_resource_call(&mut sink, ens_id, pre_heap, ens_args);
        let _h_new = sink.emit_heap(HeapInst::Sub(current_heap, h_post));
        sink.emit_ext(InstExt::Assert(b_post));
    }

    Ok(vmir::Method { insts: sink.insts })
}

fn lower_stmt(
    b: &Builder<'_>,
    env: &mut HashMap<Spur, Val>,
    sink: &mut Sink<MethodCtx>,
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
            let name = match &lhss[0] {
                typed::AssignLhs::Var(n) => n.0,
                typed::AssignLhs::Field(_, _) => {
                    return Err(TranslationError::Unsupported("field lvalue"));
                }
            };
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
            env.insert(name, v);
            Ok(current_heap)
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
        S::Fold(_) => Err(TranslationError::Unsupported("fold")),
        S::Unfold(_) => Err(TranslationError::Unsupported("unfold")),
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
                sink.emit_ext(InstExt::Assert(v));
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
                sink.emit_ext(InstExt::Assume(v));
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
                sink.emit_ext(InstExt::Assume(v));
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
                sink.emit_ext(InstExt::Assert(v));
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
    sink: &mut Sink<MethodCtx>,
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
                let delta = resource::field_acc_delta(b, sink, v.clone(), f.0, vmir::write())?;
                heap = sink.emit_heap(HeapInst::Add(heap, delta));
            }
            Ok(heap)
        }
        typed::StarOrFields::Star => Err(TranslationError::Unsupported("new(*)")),
    }
}

fn lower_method_call(
    b: &Builder<'_>,
    env: &mut HashMap<Spur, Val>,
    sink: &mut Sink<MethodCtx>,
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
    // Callee's requires delta; forwarded as ctx_heap to the callee's
    // ensures (whose `Resource.requires` is the requires resource).
    let mut callee_pre_heap: HeapVal = HeapVal::Empty;

    // Exhale precondition (if present): call m@requires, sub delta, assert
    // bool. `@requires` has no precondition itself → ctx_heap is empty.
    if let Some(&req_id) = b.method_requires.get(&call.name.0) {
        let (h_pre, b_pre) = emit_resource_call(sink, req_id, HeapVal::Empty, args.clone());
        let h_new = sink.emit_heap(HeapInst::Sub(heap, h_pre));
        sink.emit_ext(InstExt::Assert(b_pre));
        heap = h_new;
        callee_pre_heap = h_pre;
    }

    // Allocate fresh return values BEFORE the post-condition inhale.
    let mut ret_vals: Vec<Val> = Vec::with_capacity(ret_names.len());
    for (spur, ty) in ret_names.iter().zip(ret_types.iter()) {
        let v = sink.emit_pure(ty.clone(), PureInst::Fresh);
        env.insert(*spur, v.clone());
        ret_vals.push(v);
    }

    // Inhale postcondition (if present): call m@ensures, add delta, assume
    // bool. ctx_heap is the requires delta.
    if let Some(&ens_id) = b.method_ensures.get(&call.name.0) {
        let mut ens_args = args.clone();
        ens_args.extend(ret_vals.iter().cloned());
        let (h_post, b_post) = emit_resource_call(sink, ens_id, callee_pre_heap, ens_args);
        let h_new = sink.emit_heap(HeapInst::Add(heap, h_post));
        sink.emit_ext(InstExt::Assume(b_post));
        heap = h_new;
    }

    Ok(heap)
}

/// Emit a `ResourceCall` instruction that produces both a `HeapVal::Temp` and
/// a `Val::Temp`. Returns the produced pair. Method-body only — resource
/// bodies cannot reach this code path because `Sink<ResourceCtx>` has no
/// `MethodInstExt` to construct.
fn emit_resource_call(
    sink: &mut Sink<MethodCtx>,
    resource: vmir::MemberId,
    ctx_heap: HeapVal,
    args: Vec<Val>,
) -> (HeapVal, Val) {
    let h = sink.next_heap_temp();
    let v = sink.next_val_temp();
    let pc = sink.pc.clone();
    sink.insts.push(Inst::new(
        pc,
        InstKind::Ext(InstExt::ResourceCall(ResourceCall {
            resource,
            ctx_heap,
            args,
        })),
    ));
    (h, v)
}
