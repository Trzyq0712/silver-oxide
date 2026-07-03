//! Lower `typed::TypedPureExp<Ext>` into VMIR `PureInst` chains.

use std::collections::HashMap;

use lasso::Spur;

use crate::translate::sink::{PcKind, Sink};
use crate::translate::{Builder, TranslationError};
use crate::viper::typed;
use crate::vmir::{
    self, FALSE, HeapInst, HeapVal, Literal, Polarity, PureInst, ResourceCall, TRUE, Val,
};

/// Earlier heap states an `old(...)` expression can read from, in a method
/// body. `baseline` is the post-requires-inhale heap (target of unlabeled
/// `old`); `labeled` maps each `label L` to the heap captured at that point.
pub(crate) struct OldHeaps<'a> {
    pub baseline: HeapVal,
    pub labeled: &'a HashMap<Spur, HeapVal>,
}

/// Heaps a pure expression reads from. `value` is used by field derefs and
/// heap-dependent functions; `perm` is used by `perm(loc)`. They differ only on
/// `exhale`, where value reads use the pre-exhale heap but `perm` tracks the
/// running (subtracted) heap; elsewhere both are the same heap. `old`, when
/// present, lets `old(...)` reach back to earlier heap states (method bodies
/// only); `None` outside a method body.
#[derive(Clone, Copy)]
pub(crate) struct HeapCtx<'a> {
    pub value: HeapVal,
    pub perm: HeapVal,
    pub old: Option<&'a OldHeaps<'a>>,
    /// The function result `Val`, available only while lowering a function
    /// postcondition (`FuncEnsuresExt::Result`); `None` everywhere else. Held by
    /// reference so `HeapCtx` stays `Copy` (`Val` is not `Copy`).
    pub result: Option<&'a Val>,
}

impl<'a> HeapCtx<'a> {
    /// Both reads from `heap`, with `old` reachable (method-body lowering).
    pub(crate) fn same_with_old(heap: HeapVal, old: &'a OldHeaps<'a>) -> Self {
        Self {
            value: heap,
            perm: heap,
            old: Some(old),
            result: None,
        }
    }
}

/// Lower a predicate-with-perm (`P(args)` + permission) into a self-framed
/// `ResourceCall` plus the lowered permission `Val`. Shared by `unfolding`
/// expressions and method-body `fold`/`unfold` statements.
pub(crate) fn lower_pred_call<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    hctx: HeapCtx<'_>,
    pwp: &typed::PredicateWithPerm<Ext>,
) -> Result<(ResourceCall, Val), TranslationError> {
    let pred_id = *b.name_map.get(&pwp.pred_call.name.0).ok_or_else(|| {
        TranslationError::UnknownIdent(b.interner.resolve(&pwp.pred_call.name.0).to_string())
    })?;
    let mut args = Vec::with_capacity(pwp.pred_call.args.len());
    for a in &pwp.pred_call.args {
        args.push(lower(b, env, sink, hctx, a)?);
    }
    let perm = lower(b, env, sink, hctx, &pwp.perm)?;
    let call = ResourceCall {
        resource: pred_id,
        args,
    };
    Ok((call, perm))
}

pub(crate) fn lower<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    hctx: HeapCtx<'_>,
    exp: &typed::TypedPureExp<Ext>,
) -> Result<Val, TranslationError> {
    use typed::PureExpKind as P;
    let ty = b.lower_type(&exp.ty);
    match &*exp.exp {
        P::Ident(id) => env
            .get(&id.0)
            .cloned()
            .ok_or_else(|| TranslationError::UnknownIdent(b.interner.resolve(&id.0).to_string())),
        P::Const(lit) => {
            let lit = lower_literal(lit)?;
            // An Int literal used in a Real (permission) context becomes the
            // equivalent Real literal directly — no `real(..)` cast needed.
            match lit {
                Literal::Int(n) if ty == vmir::Type::Real => {
                    Ok(Val::Literal(Literal::Real(num::BigRational::from(n))))
                }
                _ => Ok(Val::Literal(lit)),
            }
        }
        P::Unary(op, x) => {
            let v = lower(b, env, sink, hctx, x)?;
            match op {
                // !v  =  v ? false : true
                typed::UnOp::Not => Ok(sink.emit_pure(ty, PureInst::Ternary(v, FALSE, TRUE))),
                // -v  =  0 - v
                typed::UnOp::Neg => Ok(sink.emit_pure(
                    ty.clone(),
                    PureInst::Binary(vmir::BinOp::Minus, zero_literal(&ty), v),
                )),
                typed::UnOp::Cardinality => Err(TranslationError::Unsupported("cardinality")),
            }
        }
        P::Binary(op, l, r) => lower_binary(b, env, sink, hctx, ty, op, l, r),
        P::Ternary { if_, then, else_ } => {
            let c = lower(b, env, sink, hctx, if_)?;
            let t = sink.with_cond(c.clone(), Polarity::Positive, PcKind::Branch, |sink| {
                lower(b, env, sink, hctx, then)
            })?;
            let e = sink.with_cond(c.clone(), Polarity::Negative, PcKind::Branch, |sink| {
                lower(b, env, sink, hctx, else_)
            })?;
            Ok(sink.emit_pure(ty, PureInst::Ternary(c, t, e)))
        }
        // A domain function call (pure, heap-free). Lowered as a polymorphic VMIR
        // function application (one `FuncId` for the function — no monomorphic
        // copy). `type_args` is the **full** instantiation in the function's own
        // type-parameter order, recovered from the concrete arg/result types, so
        // the verifier reads it verbatim (no reconstruction).
        P::DomainFunctionCall(call) => {
            let arg_tys: Vec<&typed::Type> = call.args.iter().map(|a| &a.ty).collect();
            let type_args = b.call_type_args(call.name.0, &arg_tys, &exp.ty);
            let mut args = Vec::with_capacity(call.args.len());
            for a in &call.args {
                args.push(lower(b, env, sink, hctx, a)?);
            }
            let function = *b.name_map.get(&call.name.0).ok_or_else(|| {
                TranslationError::UnknownIdent(b.interner.resolve(&call.name.0).to_string())
            })?;
            Ok(sink.emit_pure(
                ty,
                PureInst::FunctionCall(vmir::FunctionCall {
                    function,
                    type_args,
                    args: args.into(),
                }),
            ))
        }
        // A constructor lowers to the semantic `AdtCons`; its type arguments are
        // its result type (`exp.ty`), the variant tag from `ctor_tag`.
        P::AdtConstructor(call) => {
            let mut args = Vec::with_capacity(call.args.len());
            for a in &call.args {
                args.push(lower(b, env, sink, hctx, a)?);
            }
            let &(adt_spur, variant) = b.adt.ctor_tag.get(&call.name.0).ok_or_else(|| {
                TranslationError::UnknownIdent(b.interner.resolve(&call.name.0).to_string())
            })?;
            let adt = b.name_map[&adt_spur];
            let type_args = adt_type_args(b, &exp.ty);
            Ok(sink.emit_pure(
                ty,
                PureInst::AdtCons {
                    adt,
                    type_args,
                    variant,
                    args,
                },
            ))
        }
        P::LetIn { .. } => Err(TranslationError::Unsupported("let-in")),
        P::Ascribe(_, _) => Err(TranslationError::Unsupported("ascribe")),
        P::AdtDestructor(base, field) => {
            // `e.f` ⇒ `AdtProj{adt, variant, field}(e)`. The verifier's
            // projection reduction folds it when `e` is a known constructor.
            // Type args come from the scrutinee's type (`base.ty`).
            let type_args = adt_type_args(b, &base.ty);
            let base_v = lower(b, env, sink, hctx, base)?;
            let &(adt, variant, field) = b.adt.dtor_sem.get(&field.0).ok_or_else(|| {
                TranslationError::UnknownIdent(b.interner.resolve(&field.0).to_string())
            })?;
            Ok(sink.emit_pure(
                ty,
                PureInst::AdtProj {
                    adt,
                    type_args,
                    variant,
                    field,
                    base: base_v,
                },
            ))
        }
        P::AdtDiscriminator(base, variant) => {
            // `e.is<Ctor>` ⇒ `AdtTag{adt}(e) == tag_index`. The verifier's tag
            // reduction folds this to a literal when `e` is a known constructor.
            // Type args come from the scrutinee's type (`base.ty`).
            let type_args = adt_type_args(b, &base.ty);
            let base_v = lower(b, env, sink, hctx, base)?;
            let &(adt_spur, tag) = b.adt.ctor_tag.get(&variant.0).ok_or_else(|| {
                TranslationError::UnknownIdent(b.interner.resolve(&variant.0).to_string())
            })?;
            let adt = b.name_map[&adt_spur];
            let tag_call = sink.emit_pure(
                vmir::Type::Int,
                PureInst::AdtTag {
                    adt,
                    type_args,
                    base: base_v,
                },
            );
            let idx = Val::Literal(Literal::Int(num::BigInt::from(tag)));
            Ok(sink.emit_pure(
                vmir::Type::Bool,
                PureInst::Binary(vmir::BinOp::Eq, tag_call, idx),
            ))
        }
        P::Ext(ext) => Ext::lower_ext(b, env, sink, hctx, ty, ext),
    }
}

/// The type arguments of an ADT/domain-typed expression — its head's type
/// parameters at this use site. `Domain(_, args)` → lower each; any other type
/// (a non-generic / non-ADT result) → empty.
fn adt_type_args(b: &Builder<'_>, ty: &typed::Type) -> Vec<vmir::Type> {
    match ty {
        typed::Type::Domain(_, args) => args.iter().map(|t| b.lower_type(t)).collect(),
        _ => Vec::new(),
    }
}

/// The single fold kept during lowering: a division of literals in a `Real`
/// (permission) context becomes one `Real` fraction literal, so `1/2` is a
/// literal rather than a `real(1) / real(2)` division. No other arithmetic is
/// folded — e.g. `1/2 + 1/3` stays a real addition for the e-graph to handle.
fn fold_real_div(op: &typed::BinOp, l: &Literal, r: &Literal, ty: &vmir::Type) -> Option<Literal> {
    use num::BigRational;
    if !matches!(op, typed::BinOp::Div) || *ty != vmir::Type::Real {
        return None;
    }
    let rat = |lit: &Literal| -> Option<BigRational> {
        match lit {
            Literal::Int(n) => Some(BigRational::from(n.clone())),
            Literal::Real(x) => Some(x.clone()),
            _ => None,
        }
    };
    Some(Literal::Real(rat(l)? / rat(r)?))
}

/// Wrap `v` in `real(..)` when an `Int` operand is used where a `Real` is
/// expected, keeping every operation's e-graph operands homogeneous.
fn real_cast_if(sink: &mut Sink, v: Val, operand_ty: &vmir::Type, target_ty: &vmir::Type) -> Val {
    if *target_ty == vmir::Type::Real && *operand_ty == vmir::Type::Int {
        sink.emit_pure(vmir::Type::Real, PureInst::RealCast(v))
    } else {
        v
    }
}

fn lower_binary<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    hctx: HeapCtx<'_>,
    ty: vmir::Type,
    op: &typed::BinOp,
    l: &typed::TypedPureExp<Ext>,
    r: &typed::TypedPureExp<Ext>,
) -> Result<Val, TranslationError> {
    use typed::BinOp as B;
    use vmir::BinOp as V;
    let lv = lower(b, env, sink, hctx, l)?;
    // Short-circuiting boolean ops only evaluate `r` on the path where `l`
    // takes the guarding value, so `r` is lowered under that guard.
    match op {
        B::And => {
            // l && r  =  l ? r : false
            let rv = sink.with_cond(lv.clone(), Polarity::Positive, PcKind::Branch, |sink| {
                lower(b, env, sink, hctx, r)
            })?;
            return Ok(sink.emit_pure(ty, PureInst::Ternary(lv, rv, FALSE)));
        }
        B::Or => {
            // l || r  =  l ? true : r
            let rv = sink.with_cond(lv.clone(), Polarity::Negative, PcKind::Branch, |sink| {
                lower(b, env, sink, hctx, r)
            })?;
            return Ok(sink.emit_pure(ty, PureInst::Ternary(lv, TRUE, rv)));
        }
        B::Implies => {
            // l ==> r  =  l ? r : true
            let rv = sink.with_cond(lv.clone(), Polarity::Positive, PcKind::Branch, |sink| {
                lower(b, env, sink, hctx, r)
            })?;
            return Ok(sink.emit_pure(ty, PureInst::Ternary(lv, rv, TRUE)));
        }
        _ => {}
    }
    // Strict ops: both operands always evaluate, so `r` is lowered under the
    // outer path condition unchanged.
    let rv = lower(b, env, sink, hctx, r)?;
    // Only fold a literal division in a `Real` context to its fraction (`1/2`);
    // all other literal arithmetic stays symbolic for the e-graph.
    if let (Val::Literal(la), Val::Literal(lb)) = (&lv, &rv) {
        if let Some(folded) = fold_real_div(op, la, lb, &ty) {
            return Ok(Val::Literal(folded));
        }
    }
    // Homogenize: a `Real`-result arithmetic op with an `Int` operand gets that
    // operand wrapped in `real(..)` so the e-graph operands share a type.
    let lv = real_cast_if(sink, lv, &b.lower_type(&l.ty), &ty);
    let rv = real_cast_if(sink, rv, &b.lower_type(&r.ty), &ty);
    Ok(match op {
        B::Plus => sink.emit_pure(ty, PureInst::Binary(V::Plus, lv, rv)),
        B::Minus => sink.emit_pure(ty, PureInst::Binary(V::Minus, lv, rv)),
        B::Mult => sink.emit_pure(ty, PureInst::Binary(V::Mult, lv, rv)),
        // The divisor≠0 obligation is checked in the current value heap.
        B::Div => sink.with_heap(hctx.value, |sink| {
            sink.emit_pure_guarded(ty, PureInst::Binary(V::Div, lv, rv))
        }),
        B::Mod => sink.with_heap(hctx.value, |sink| {
            sink.emit_pure_guarded(ty, PureInst::Binary(V::Mod, lv, rv))
        }),
        B::Eq => sink.emit_pure(ty, PureInst::Binary(V::Eq, lv, rv)),
        B::Lt => sink.emit_pure(ty, PureInst::Binary(V::Lt, lv, rv)),
        // Desugarings:
        B::Neq => {
            let eq = sink.emit_pure(vmir::Type::Bool, PureInst::Binary(V::Eq, lv, rv));
            sink.emit_pure(ty, PureInst::Ternary(eq, FALSE, TRUE))
        }
        B::Le => {
            // l <= r  <=>  !(r < l)
            let gt = sink.emit_pure(vmir::Type::Bool, PureInst::Binary(V::Lt, rv, lv));
            sink.emit_pure(ty, PureInst::Ternary(gt, FALSE, TRUE))
        }
        B::Gt => sink.emit_pure(ty, PureInst::Binary(V::Lt, rv, lv)),
        B::Ge => {
            // l >= r  <=>  !(l < r)
            let lt = sink.emit_pure(vmir::Type::Bool, PureInst::Binary(V::Lt, lv, rv));
            sink.emit_pure(ty, PureInst::Ternary(lt, FALSE, TRUE))
        }
        B::And | B::Or | B::Implies => unreachable!("handled above"),
        B::Iff => sink.emit_pure(ty, PureInst::Binary(V::Eq, lv, rv)),
        B::In | B::Union | B::SetMinus | B::Intersection | B::Subset | B::Concat | B::Range => {
            return Err(TranslationError::Unsupported("collection operator"));
        }
    })
}

/// Type-appropriate zero used to desugar arithmetic negation `-v` as
/// `Binary(Minus, 0, v)`. Non-numeric types panic; upstream typechecking
/// rejects them before lowering.
pub(crate) fn zero_literal(ty: &vmir::Type) -> Val {
    match ty {
        vmir::Type::Int => Val::Literal(Literal::Int(num::BigInt::from(0))),
        vmir::Type::Real => Val::Literal(Literal::Real(num::BigInt::from(0).into())),
        other => panic!("Neg on non-numeric type {other:?}"),
    }
}

pub(crate) fn lower_literal(lit: &typed::Literal) -> Result<Literal, TranslationError> {
    match lit {
        typed::Literal::Bool(b) => Ok(Literal::Bool(*b)),
        typed::Literal::Int(n) => Ok(Literal::Int(n.clone())),
        typed::Literal::Real(r) => Ok(Literal::Real(r.clone())),
        typed::Literal::Null => Ok(Literal::Null),
        typed::Literal::Wildcard => Err(TranslationError::Unsupported("wildcard literal")),
    }
}

/// Per-context lowering of pure-expression extensions (`old`, `result`,
/// `perm`, etc.). `hctx` carries the value/perm heaps; `ty` is the expression's
/// result type.
/// Lower a Silver `function` application to a VMIR `FunctionCall` (monomorphic,
/// no `type_args`). Calls are always pure: a **heap-dependent** callee (one
/// whose `requires` grants permission) receives the snapshot of its `#requires`
/// resource — built here from the current value heap by `PureInst::Snap`, which
/// implicitly checks the precondition (footprint sufficiency + resource bool) —
/// as an extra trailing argument. A **heap-free** callee's precondition is
/// instead asserted as a boolean contract call.
fn lower_func_app<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    hctx: HeapCtx<'_>,
    ty: vmir::Type,
    call: &typed::Call<Ext>,
) -> Result<Val, TranslationError> {
    let mut args = Vec::with_capacity(call.args.len());
    for a in &call.args {
        args.push(lower(b, env, sink, hctx, a)?);
    }
    let func = *b.name_map.get(&call.name.0).ok_or_else(|| {
        TranslationError::UnknownIdent(b.interner.resolve(&call.name.0).to_string())
    })?;
    let contracts = b.contracts.get(&call.name.0);
    let requires = contracts.and_then(|c| c.requires);
    let ensures = contracts.and_then(|c| c.ensures);
    let heap_dep = contracts.is_some_and(|c| c.heap_dep);
    // Use-side precondition, and the call's actual argument list.
    let mut call_args = args.clone();
    let mut snap = None;
    if heap_dep {
        // Narrow the current value heap to the callee's precondition snapshot.
        // `Snap` implicitly asserts the precondition under the running pc.
        let req_id = requires.expect("heap-dep implies a requires");
        let s = sink.emit_pure_guarded(
            vmir::Type::Snap(req_id),
            PureInst::Snap {
                resource: req_id,
                args: args.clone(),
                heap: hctx.value,
            },
        );
        call_args.push(s.clone());
        snap = Some(s);
    } else if let Some(req_id) = requires {
        // Heap-free: assert `f#requires(args)` before the call.
        let check = call_contract(sink, req_id, args.clone());
        sink.emit_assert(check);
    }
    let ret = sink.emit_pure(
        ty,
        PureInst::FunctionCall(vmir::FunctionCall {
            function: func,
            type_args: Vec::new(),
            args: call_args.into(),
        }),
    );
    // Use-side postcondition: assume `f#ensures(args, ret[, snap])` after the
    // call.
    if let Some(ens_id) = ensures {
        args.push(ret.clone());
        args.extend(snap);
        let check = call_contract(sink, ens_id, args);
        sink.emit_assume(check);
    }
    Ok(ret)
}

/// Lower a heap-reading node (`e.f`, a `function` call, `unfolding`). Shared by
/// every heap-bearing context's `lower_ext`.
pub(crate) fn lower_heap_node<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    hctx: HeapCtx<'_>,
    ty: vmir::Type,
    node: &typed::HeapNode<Ext>,
) -> Result<Val, TranslationError> {
    use typed::HeapNode as H;
    match node {
        H::Field(base, id) => {
            let base = lower(b, env, sink, hctx, base)?;
            let addr = crate::translate::resource::field_addr(b, sink, base, id.0)?;
            Ok(sink.emit_pure_guarded(ty, PureInst::Deref(hctx.value, addr)))
        }
        // A heap-dependent Silver `function` — not generic yet, so no type args.
        H::FunctionCall(call) => lower_func_app(b, env, sink, hctx, ty, call),
        H::Unfolding(pwp, body) => {
            // `unfolding acc(P(args), perm) in body`: a scoped unfold. Emit an
            // `Unfold`, evaluate `body` against the unfolded heap, then discard it
            // (the surrounding expression keeps reading the original `hctx`).
            let (call, perm) = lower_pred_call(b, env, sink, hctx, pwp)?;
            let h = sink.emit_heap_guarded(HeapInst::Unfold {
                base: hctx.value,
                call,
                perm,
            });
            let inner = HeapCtx {
                value: h,
                perm: h,
                ..hctx
            };
            lower(b, env, sink, inner, body)
        }
    }
}

pub(crate) trait PureExt: Sized + Clone + std::fmt::Debug {
    fn lower_ext(
        b: &Builder<'_>,
        env: &HashMap<Spur, Val>,
        sink: &mut Sink,
        hctx: HeapCtx<'_>,
        ty: vmir::Type,
        ext: &Self,
    ) -> Result<Val, TranslationError>;
}

impl PureExt for ! {
    fn lower_ext(
        _b: &Builder<'_>,
        _env: &HashMap<Spur, Val>,
        _sink: &mut Sink,
        _hctx: HeapCtx<'_>,
        _ty: vmir::Type,
        ext: &Self,
    ) -> Result<Val, TranslationError> {
        match *ext {}
    }
}

impl PureExt for typed::HeapExt {
    fn lower_ext(
        b: &Builder<'_>,
        env: &HashMap<Spur, Val>,
        sink: &mut Sink,
        hctx: HeapCtx<'_>,
        ty: vmir::Type,
        ext: &Self,
    ) -> Result<Val, TranslationError> {
        match ext {
            typed::HeapExt::Heap(node) => lower_heap_node(b, env, sink, hctx, ty, node),
        }
    }
}

impl PureExt for typed::MethodEnsuresExt {
    fn lower_ext(
        b: &Builder<'_>,
        env: &HashMap<Spur, Val>,
        sink: &mut Sink,
        hctx: HeapCtx<'_>,
        ty: vmir::Type,
        ext: &Self,
    ) -> Result<Val, TranslationError> {
        match ext {
            typed::MethodEnsuresExt::Heap(node) => lower_heap_node(b, env, sink, hctx, ty, node),
            // old(e): re-read `e` against the method pre-state. For a two-state
            // ensures that heap is the one its entry `FromSnap` reconstructs
            // from the trailing snapshot parameter, supplied as the `old`
            // baseline by `lower_spatial_ensures`. Ensures-`old` is always
            // unlabeled (`old[L]` is a type error). A self-framed ensures has no
            // pre-state (`hctx.old == None`): `old` there needs a `requires` to
            // frame it.
            typed::MethodEnsuresExt::Old(inner) => {
                let old = hctx.old.ok_or(TranslationError::Unsupported(
                    "`old` in method ensures needs a precondition framing it",
                ))?;
                let heap = old.baseline;
                lower(
                    b,
                    env,
                    sink,
                    HeapCtx {
                        value: heap,
                        perm: heap,
                        ..hctx
                    },
                    inner,
                )
            }
        }
    }
}

impl PureExt for typed::MethodBodyExt {
    fn lower_ext(
        b: &Builder<'_>,
        env: &HashMap<Spur, Val>,
        sink: &mut Sink,
        hctx: HeapCtx<'_>,
        ty: vmir::Type,
        ext: &Self,
    ) -> Result<Val, TranslationError> {
        match ext {
            typed::MethodBodyExt::Heap(node) => lower_heap_node(b, env, sink, hctx, ty, node),
            // old(e) / old[L](e): re-read `e` against an earlier heap. Unlabeled
            // → the post-requires-inhale baseline; labeled → the heap captured
            // at `label L`. The `old` context is carried along so nested `old`s
            // still resolve.
            typed::MethodBodyExt::Old(label, inner) => {
                let old = hctx
                    .old
                    .ok_or(TranslationError::Unsupported("`old` outside method body"))?;
                let heap = match label {
                    None => old.baseline,
                    Some(l) => *old.labeled.get(l).ok_or_else(|| {
                        TranslationError::UnknownIdent(b.interner.resolve(l).to_string())
                    })?,
                };
                lower(
                    b,
                    env,
                    sink,
                    HeapCtx {
                        value: heap,
                        perm: heap,
                        ..hctx
                    },
                    inner,
                )
            }
            // perm(loc): query the permission held at `loc` in the perm heap.
            typed::MethodBodyExt::Perm(res) => {
                let addr =
                    crate::translate::resource::lower_resource_addr(b, env, sink, hctx, res)?;
                Ok(sink.emit_pure(ty, PureInst::Perm(hctx.perm, addr)))
            }
        }
    }
}

impl PureExt for typed::FuncEnsuresExt {
    fn lower_ext(
        b: &Builder<'_>,
        env: &HashMap<Spur, Val>,
        sink: &mut Sink,
        hctx: HeapCtx<'_>,
        ty: vmir::Type,
        ext: &Self,
    ) -> Result<Val, TranslationError> {
        match ext {
            typed::FuncEnsuresExt::Heap(node) => lower_heap_node(b, env, sink, hctx, ty, node),
            // `result`: the function's return value, supplied by the ensures
            // function's caller in the last parameter slot.
            typed::FuncEnsuresExt::Result => hctx.result.cloned().ok_or(
                TranslationError::Unsupported("`result` outside a function postcondition"),
            ),
            // A function is single-state: `old(e)` reads the same (only) heap the
            // postcondition is framed by, so it re-reads `e` against the current
            // context.
            typed::FuncEnsuresExt::Old(inner) => lower(b, env, sink, hctx, inner),
        }
    }
}

/// The contract functions to stitch around a function body: `assume
/// requires(params)` at entry, `assert ensures(params ++ [body_result])` at
/// exit. Each is `None` when the function omits that clause; `params` are the
/// function's parameter `Val`s (`Temp(0..n_params)`). For a heap-dependent
/// function `requires` is `None` (the precondition is assumed implicitly by
/// the entry `FromSnap`) and `snap` is its snapshot parameter, appended after
/// the result in the exit `ensures` call.
pub(crate) struct FnContract {
    pub requires: Option<vmir::MemberId>,
    pub ensures: Option<vmir::MemberId>,
    pub params: Vec<Val>,
    pub snap: Option<Val>,
}

/// The entry `FromSnap` of a heap-dependent function (or ensures-function)
/// body: reconstruct the precondition heap from the snapshot parameter `snap`
/// of `resource(args)`. The produced heap becomes the body's value/perm heap.
pub(crate) struct SnapEntry {
    pub resource: vmir::MemberId,
    pub args: Vec<Val>,
    pub snap: Val,
}

/// Emit a heap-free boolean contract call `func(args)` and return its `Val`.
fn call_contract(sink: &mut Sink, func: vmir::MemberId, args: Vec<Val>) -> Val {
    sink.emit_pure(
        vmir::Type::Bool,
        PureInst::FunctionCall(vmir::FunctionCall {
            function: func,
            type_args: Vec::new(),
            args: args.into(),
        }),
    )
}

/// Lower a pure expression into a standalone [`vmir::FunctionBody`] (function
/// body / contract-function definition). `val_base` is the first free pure-temp
/// counter (params, plus `result`/snapshot slots for a postcondition /
/// heap-dependent function, occupy the lower temps); `heap` is the context heap
/// the body reads from (`HeapVal::Empty` for a heap-free body); `result` is
/// `Some` only for a postcondition function. When `snap_entry` is `Some`, the
/// body opens with its `FromSnap` — reconstructing the precondition heap from
/// the snapshot parameter (implicitly assuming the resource bool) — and that
/// heap replaces `heap` as the body's value/perm heap. When `contract` is
/// `Some`, the body **assumes** `requires(params)` at entry and **asserts**
/// `ensures(params ++ [body_result] ++ [snap])` at exit.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lower_function_body<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    exp: &typed::TypedPureExp<Ext>,
    val_base: usize,
    heap: HeapVal,
    result: Option<Val>,
    contract: Option<FnContract>,
    snap_entry: Option<SnapEntry>,
) -> Result<vmir::FunctionBody, TranslationError> {
    let mut sink = Sink::new(val_base, 0);
    // A heap-dependent body reads the heap reconstructed from its snapshot
    // parameter; a heap-free body reads the inert `heap` (`Empty`).
    let heap = match snap_entry {
        Some(SnapEntry {
            resource,
            args,
            snap,
        }) => sink.emit_heap(HeapInst::FromSnap {
            resource,
            args,
            snap,
        }),
        None => heap,
    };
    let hctx = HeapCtx {
        value: heap,
        perm: heap,
        old: None,
        result: result.as_ref(),
    };
    // Entry: assume the precondition. (Heap-dependent bodies skip this — the
    // `FromSnap` above assumes the requires resource's bool implicitly.)
    if let Some(FnContract {
        requires: Some(req),
        params,
        ..
    }) = &contract
    {
        let check = call_contract(&mut sink, *req, params.clone());
        sink.emit_assume(check);
    }
    let res = lower(b, env, &mut sink, hctx, exp)?;
    // Exit: assert the postcondition on the actual body result (plus the
    // snapshot parameter for a heap-dependent function).
    if let Some(FnContract {
        ensures: Some(ens),
        params,
        snap,
        ..
    }) = &contract
    {
        let mut args = params.clone();
        args.push(res.clone());
        args.extend(snap.clone());
        let check = call_contract(&mut sink, *ens, args);
        sink.emit_assert(check);
    }
    Ok(vmir::FunctionBody {
        insts: sink.insts,
        res,
    })
}
