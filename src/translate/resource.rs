//! Lower `typed::SpatialExp` into a `vmir::ResourceBody`.

use std::collections::HashMap;

use lasso::Spur;

use crate::translate::pure_exp::{self, HeapCtx, OldHeaps, PureExt, Sink};
use crate::translate::{Builder, TranslationError, lower_type};
use crate::viper::typed;
use crate::vmir::{
    self, Acc, FALSE, FunctionCall, HeapInst, HeapVal, Polarity, PureInst, TRUE, Type, Val, none,
};

/// Direction and heap semantics of a spatial lowering.
///
/// - `Inhale`: `acc`s are **added** to the accumulation heap; both value and
///   `perm` reads track that growing heap (also the mode for resource bodies).
/// - `Exhale { value_heap }`: `acc`s are **subtracted** (left-to-right), so a
///   later `perm` observes the reduced heap; `perm` reads thus track the
///   shrinking accumulation heap, while value reads use the fixed pre-exhale
///   `value_heap`.
#[derive(Clone, Copy)]
pub(crate) enum SpatialMode {
    Inhale,
    Exhale { value_heap: HeapVal },
}

impl SpatialMode {
    /// Heaps to read sub-expressions from, given the current accumulation heap.
    /// `perm` always tracks `acc_heap`; values track it on inhale but use the
    /// fixed pre-exhale heap on exhale. `old` (method bodies only) is carried
    /// through so `old(...)` sub-expressions can reach earlier heaps.
    fn heap_ctx<'a>(self, acc_heap: HeapVal, old: Option<&'a OldHeaps<'a>>) -> HeapCtx<'a> {
        match self {
            SpatialMode::Inhale => HeapCtx {
                value: acc_heap,
                perm: acc_heap,
                old,
            },
            SpatialMode::Exhale { value_heap } => HeapCtx {
                value: value_heap,
                perm: acc_heap,
                old,
            },
        }
    }
}

/// Lower a resource body. `initial_heap` is the body's starting heap
/// reference; pass `HeapVal::Empty` when the owning `Resource.requires`
/// is `None`, and `HeapVal::Temp(0)` (with `heap_base = 1`) once the
/// resource has its own precondition resource. `heap_base` is the first
/// heap counter the body's emitted heap insts will use.
pub(crate) fn lower_spatial_never(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    exp: &typed::SpatialExp<!>,
    val_base: usize,
    initial_heap: HeapVal,
    heap_base: usize,
) -> Result<vmir::ResourceBody, TranslationError> {
    let mut sink = Sink::new(val_base, heap_base);
    let (h, bv) = lower_spatial(
        b,
        env,
        &mut sink,
        initial_heap,
        SpatialMode::Inhale,
        None,
        None,
        exp,
    )?;
    Ok(vmir::ResourceBody {
        insts: sink.insts,
        res: (h, bv.unwrap_or(TRUE)),
    })
}

pub(crate) fn lower_spatial_ensures(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    exp: &typed::SpatialExp<typed::MethodEnsuresExt>,
    val_base: usize,
    initial_heap: HeapVal,
    heap_base: usize,
) -> Result<vmir::ResourceBody, TranslationError> {
    let mut sink = Sink::new(val_base, heap_base);
    let (h, bv) = lower_spatial(
        b,
        env,
        &mut sink,
        initial_heap,
        SpatialMode::Inhale,
        None,
        None,
        exp,
    )?;
    Ok(vmir::ResourceBody {
        insts: sink.insts,
        res: (h, bv.unwrap_or(TRUE)),
    })
}

/// Lower a `SpatialExp` into a heap delta and an optional boolean.
///
/// `None` means the spatial expression carries no logical content beyond its
/// heap chunks — i.e. the boolean is trivially `true`. Returning `Option`
/// instead of always emitting a `Pure` ternary lets us collapse
/// `acc(...) && acc(...)` and similar all-permission expressions to just the
/// heap delta with no boolean witness.
/// `guard` is the active branch condition (a `Bool` `Val`) under which the
/// spatial expression is reached, or `None` at the top level. The branch is
/// encoded into permission fractions rather than into a heap multiplexer: every
/// `acc`'s permission is gated `guard ? perm : none`, and chunks are added to a
/// single monotonic heap timeline (no `HeapInst::Ternary`). The agreement axiom
/// in the verifier keeps values from mutually-exclusive branches isolated,
/// since their fractions are never both positive.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lower_spatial<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    acc_heap: HeapVal,
    mode: SpatialMode,
    old: Option<&OldHeaps>,
    guard: Option<Val>,
    exp: &typed::SpatialExp<Ext>,
) -> Result<(HeapVal, Option<Val>), TranslationError> {
    use typed::SpatialExpKind as S;
    // Heaps to read heap-dependent sub-expressions from at this point.
    let hctx = mode.heap_ctx(acc_heap, old);
    match &*exp.0 {
        S::Acc(res, perm) => {
            let delta = lower_acc(b, env, sink, hctx, guard, res, perm)?;
            // Inhale adds the chunk; exhale subtracts it (so a later `perm`
            // observes the reduced heap). The add/sub is unconditional — the
            // branch lives in the (gated) permission fraction.
            let h_out = match mode {
                SpatialMode::Inhale => sink.emit_heap(HeapInst::Add(acc_heap, delta)),
                SpatialMode::Exhale { .. } => sink.emit_heap(HeapInst::Sub(acc_heap, delta)),
            };
            Ok((h_out, None))
        }
        S::Conj(l, r) => {
            let (h_mid, b_l) = lower_spatial(b, env, sink, acc_heap, mode, old, guard.clone(), l)?;
            let (h_out, b_r) = lower_spatial(b, env, sink, h_mid, mode, old, guard, r)?;

            let b_sum = match (b_l, b_r) {
                (None, None) => None,
                (Some(v), None) | (None, Some(v)) => Some(v),
                (Some(vl), Some(vr)) => {
                    Some(sink.emit_pure(Type::Bool, PureInst::Ternary(vl, vr, FALSE)))
                }
            };

            Ok((h_out, b_sum))
        }
        S::Implies(cond, body) => {
            let c = pure_exp::lower(b, env, sink, hctx, cond)?;
            let g = conj(sink, guard, c.clone());
            // Body chunks are gated by `g` and added onto the same running heap;
            // the result heap is simply the body's. `with_cond` keeps the path
            // condition so the body's `acc`/deref side conditions discharge.
            let (h_out, b_b) = sink.with_cond(c.clone(), Polarity::Positive, |sink| {
                lower_spatial(b, env, sink, acc_heap, mode, old, Some(g), body)
            })?;
            // c ==> b_b  =  c ? b_b : true. When body has no boolean, the
            // whole implication is trivially true.
            let bv = b_b.map(|v| sink.emit_pure(Type::Bool, PureInst::Ternary(c, v, TRUE)));
            Ok((h_out, bv))
        }
        S::Ternary { if_, then, else_ } => {
            let c = pure_exp::lower(b, env, sink, hctx, if_)?;
            let g_then = conj(sink, guard.clone(), c.clone());
            let not_c = negate(sink, c.clone());
            let g_else = conj(sink, guard, not_c);
            // Both arms add their gated chunks to the same timeline, in order:
            // then onto `acc_heap`, else onto the then-result. No heap ternary.
            let (h_mid, b_t) = sink.with_cond(c.clone(), Polarity::Positive, |sink| {
                lower_spatial(b, env, sink, acc_heap, mode, old, Some(g_then), then)
            })?;
            let (h_out, b_e) = sink.with_cond(c.clone(), Polarity::Negative, |sink| {
                lower_spatial(b, env, sink, h_mid, mode, old, Some(g_else), else_)
            })?;
            let bv = match (b_t, b_e) {
                (None, None) => None,
                (Some(vt), None) => {
                    Some(sink.emit_pure(Type::Bool, PureInst::Ternary(c, vt, TRUE)))
                }
                (None, Some(ve)) => {
                    Some(sink.emit_pure(Type::Bool, PureInst::Ternary(c, TRUE, ve)))
                }
                (Some(vt), Some(ve)) => {
                    Some(sink.emit_pure(Type::Bool, PureInst::Ternary(c, vt, ve)))
                }
            };
            Ok((h_out, bv))
        }
        S::Pure(p) => {
            let v = pure_exp::lower(b, env, sink, hctx, p)?;
            Ok((acc_heap, Some(v)))
        }
    }
}

/// `guard && c` as a pure ternary `guard ? c : false` (or just `c` at the top
/// level). Used to combine nested branch conditions for permission gating.
fn conj(sink: &mut Sink, guard: Option<Val>, c: Val) -> Val {
    match guard {
        None => c,
        Some(g) => sink.emit_pure(Type::Bool, PureInst::Ternary(g, c, FALSE)),
    }
}

/// `!c` as a pure ternary `c ? false : true`.
fn negate(sink: &mut Sink, c: Val) -> Val {
    sink.emit_pure(Type::Bool, PureInst::Ternary(c, FALSE, TRUE))
}

/// Gate a permission amount by the active branch guard: `guard ? perm : none`
/// (or `perm` unguarded). A dead branch contributes `none` (0) permission.
fn gate_perm(sink: &mut Sink, guard: Option<Val>, perm: Val) -> Val {
    match guard {
        None => perm,
        Some(g) => sink.emit_pure(Type::Real, PureInst::Ternary(g, perm, none())),
    }
}

fn lower_acc<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    hctx: HeapCtx<'_>,
    guard: Option<Val>,
    res: &typed::ResourceExp<Ext>,
    perm: &typed::TypedPureExp<Ext>,
) -> Result<HeapVal, TranslationError> {
    let perm_val = pure_exp::lower(b, env, sink, hctx, perm)?;
    let perm_val = gate_perm(sink, guard, perm_val);
    let addr = lower_resource_addr(b, env, sink, hctx, res)?;
    Ok(sink.emit_heap(HeapInst::Acc(Acc {
        loc: addr,
        perm: perm_val,
    })))
}

/// Lower a `ResourceExp` to its address: the `@addr` function applied to the
/// resource's base/arguments (`field@addr(base)` or `pred@addr(args)`). The
/// `@addr` call is heap-independent. Shared by `acc`, `perm`, and `new`.
pub(crate) fn lower_resource_addr<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    hctx: HeapCtx<'_>,
    res: &typed::ResourceExp<Ext>,
) -> Result<Val, TranslationError> {
    use typed::ResourceExpKind as R;
    match &*res.0 {
        R::Field(base, fname) => {
            let base_val = pure_exp::lower(b, env, sink, hctx, base)?;
            let &addr_fn = b.field_addr.get(&fname.0).ok_or_else(|| {
                TranslationError::UnknownIdent(b.interner.resolve(&fname.0).to_string())
            })?;
            let field_ty = b
                .globals
                .resolve(fname.0)
                .and_then(|s| s.as_field().cloned())
                .ok_or_else(|| {
                    TranslationError::UnknownIdent(b.interner.resolve(&fname.0).to_string())
                })?;
            let ret_ty = Type::Addr(Box::new(lower_type(&field_ty)));
            Ok(sink.emit_pure(
                ret_ty,
                PureInst::FunctionCall(
                    HeapVal::Empty,
                    FunctionCall {
                        function: addr_fn,
                        args: vec![base_val],
                    },
                ),
            ))
        }
        R::PredicateCall(call) => {
            let &addr_fn = b.pred_addr.get(&call.name.0).ok_or_else(|| {
                TranslationError::UnknownIdent(b.interner.resolve(&call.name.0).to_string())
            })?;
            let &snap_id = b
                .pred_snap
                .get(&call.name.0)
                .expect("predicate snap missing");
            let mut args = Vec::with_capacity(call.args.len());
            for a in &call.args {
                args.push(pure_exp::lower(b, env, sink, hctx, a)?);
            }
            let ret_ty = Type::Addr(Box::new(Type::Domain(snap_id)));
            Ok(sink.emit_pure(
                ret_ty,
                PureInst::FunctionCall(
                    HeapVal::Empty,
                    FunctionCall {
                        function: addr_fn,
                        args,
                    },
                ),
            ))
        }
    }
}

/// Lower an assertion used by source-level `assert`/`assume` into a single
/// boolean over `heap` (returns `None` when trivially true). Permission is
/// **not** moved: each `acc(loc, p)` becomes the boolean `perm(loc) >= p`.
pub(crate) fn lower_assertion_bool<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    heap: HeapVal,
    old: Option<&OldHeaps>,
    exp: &typed::SpatialExp<Ext>,
) -> Result<Option<Val>, TranslationError> {
    use typed::SpatialExpKind as S;
    let hctx = HeapCtx {
        value: heap,
        perm: heap,
        old,
    };
    match &*exp.0 {
        // acc(loc, p)  ==>  perm(loc) >= p  ==  not(perm(loc) < p)
        S::Acc(res, perm) => {
            let p = pure_exp::lower(b, env, sink, hctx, perm)?;
            let addr = lower_resource_addr(b, env, sink, hctx, res)?;
            let held = sink.emit_pure(Type::Real, PureInst::Perm(heap, addr));
            let lt = sink.emit_pure(Type::Bool, PureInst::Binary(vmir::BinOp::Lt, held, p));
            Ok(Some(
                sink.emit_pure(Type::Bool, PureInst::Ternary(lt, FALSE, TRUE)),
            ))
        }
        S::Conj(l, r) => {
            let bl = lower_assertion_bool(b, env, sink, heap, old, l)?;
            let br = lower_assertion_bool(b, env, sink, heap, old, r)?;
            Ok(match (bl, br) {
                (None, None) => None,
                (Some(v), None) | (None, Some(v)) => Some(v),
                // l && r  =  l ? r : false
                (Some(vl), Some(vr)) => {
                    Some(sink.emit_pure(Type::Bool, PureInst::Ternary(vl, vr, FALSE)))
                }
            })
        }
        S::Implies(cond, body) => {
            let c = pure_exp::lower(b, env, sink, hctx, cond)?;
            let bb = sink.with_cond(c.clone(), Polarity::Positive, |sink| {
                lower_assertion_bool(b, env, sink, heap, old, body)
            })?;
            // c ==> bb  =  c ? bb : true
            Ok(bb.map(|v| sink.emit_pure(Type::Bool, PureInst::Ternary(c, v, TRUE))))
        }
        S::Ternary { if_, then, else_ } => {
            let c = pure_exp::lower(b, env, sink, hctx, if_)?;
            let bt = sink.with_cond(c.clone(), Polarity::Positive, |sink| {
                lower_assertion_bool(b, env, sink, heap, old, then)
            })?;
            let be = sink.with_cond(c.clone(), Polarity::Negative, |sink| {
                lower_assertion_bool(b, env, sink, heap, old, else_)
            })?;
            Ok(match (bt, be) {
                (None, None) => None,
                (Some(vt), None) => {
                    Some(sink.emit_pure(Type::Bool, PureInst::Ternary(c, vt, TRUE)))
                }
                (None, Some(ve)) => {
                    Some(sink.emit_pure(Type::Bool, PureInst::Ternary(c, TRUE, ve)))
                }
                (Some(vt), Some(ve)) => {
                    Some(sink.emit_pure(Type::Bool, PureInst::Ternary(c, vt, ve)))
                }
            })
        }
        S::Pure(p) => Ok(Some(pure_exp::lower(b, env, sink, hctx, p)?)),
    }
}

/// Emit the single-chunk heap delta for `acc(base.fname, perm)`: the field's
/// `@addr` function applied to `base`, followed by a `HeapInst::Acc`. Returns
/// the produced delta heap. Shared by `lower_acc` and `new(...)` lowering.
pub(crate) fn field_acc_delta(
    b: &Builder<'_>,
    sink: &mut Sink,
    base: Val,
    fname: Spur,
    perm: Val,
) -> Result<HeapVal, TranslationError> {
    let &addr_fn = b
        .field_addr
        .get(&fname)
        .ok_or_else(|| TranslationError::UnknownIdent(b.interner.resolve(&fname).to_string()))?;
    let field_ty = b
        .globals
        .resolve(fname)
        .and_then(|s| s.as_field().cloned())
        .ok_or_else(|| TranslationError::UnknownIdent(b.interner.resolve(&fname).to_string()))?;
    let ret_ty = Type::Addr(Box::new(lower_type(&field_ty)));
    let addr = sink.emit_pure(
        ret_ty,
        PureInst::FunctionCall(
            HeapVal::Empty,
            FunctionCall {
                function: addr_fn,
                args: vec![base],
            },
        ),
    );
    Ok(sink.emit_heap(HeapInst::Acc(Acc { loc: addr, perm })))
}
