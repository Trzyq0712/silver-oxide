//! Lower `typed::SpatialExp` into a `vmir::ResourceBody`.

use std::collections::HashMap;

use lasso::Spur;

use crate::viper::typed;
use crate::translate::pure_exp::{self, HeapCtx, PureExt, Sink};
use crate::translate::{Builder, TranslationError, lower_type};
use crate::vmir::{
    self, Acc, FALSE, FunctionCall, HeapInst, HeapVal, InstContext, Polarity, PureInst, ResourceCtx,
    TRUE, Type, Val,
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
    /// fixed pre-exhale heap on exhale.
    fn heap_ctx(self, acc_heap: HeapVal) -> HeapCtx {
        match self {
            SpatialMode::Inhale => HeapCtx::same(acc_heap),
            SpatialMode::Exhale { value_heap } => HeapCtx {
                value: value_heap,
                perm: acc_heap,
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
    let mut sink = Sink::<ResourceCtx>::new(val_base, heap_base);
    let (h, bv) = lower_spatial(b, env, &mut sink, initial_heap, SpatialMode::Inhale, exp)?;
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
    let mut sink = Sink::<ResourceCtx>::new(val_base, heap_base);
    let (h, bv) = lower_spatial(b, env, &mut sink, initial_heap, SpatialMode::Inhale, exp)?;
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
pub(crate) fn lower_spatial<C: InstContext, Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink<C>,
    acc_heap: HeapVal,
    mode: SpatialMode,
    exp: &typed::SpatialExp<Ext>,
) -> Result<(HeapVal, Option<Val>), TranslationError> {
    use typed::SpatialExpKind as S;
    // Heaps to read heap-dependent sub-expressions from at this point.
    let hctx = mode.heap_ctx(acc_heap);
    match &*exp.0 {
        S::Acc(res, perm) => {
            let delta = lower_acc(b, env, sink, hctx, res, perm)?;
            // Inhale adds the chunk; exhale subtracts it (so a later `perm`
            // observes the reduced heap).
            let h_out = match mode {
                SpatialMode::Inhale => sink.emit_heap(HeapInst::Add(acc_heap, delta)),
                SpatialMode::Exhale { .. } => sink.emit_heap(HeapInst::Sub(acc_heap, delta)),
            };
            Ok((h_out, None))
        }
        S::Conj(l, r) => {
            let (h_mid, b_l) = lower_spatial(b, env, sink, acc_heap, mode, l)?;
            let (h_out, b_r) = lower_spatial(b, env, sink, h_mid, mode, r)?;

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
            let (h_b, b_b) = sink.with_cond(c.clone(), Polarity::Positive, |sink| {
                lower_spatial(b, env, sink, acc_heap, mode, body)
            })?;
            let h = sink.emit_heap(HeapInst::Ternary(c.clone(), h_b, acc_heap));
            // c ==> b_b  =  c ? b_b : true. When body has no boolean, the
            // whole implication is trivially true.
            let bv = b_b.map(|v| sink.emit_pure(Type::Bool, PureInst::Ternary(c, v, TRUE)));
            Ok((h, bv))
        }
        S::Ternary { if_, then, else_ } => {
            let c = pure_exp::lower(b, env, sink, hctx, if_)?;
            let (h_t, b_t) = sink.with_cond(c.clone(), Polarity::Positive, |sink| {
                lower_spatial(b, env, sink, acc_heap, mode, then)
            })?;
            let (h_e, b_e) = sink.with_cond(c.clone(), Polarity::Negative, |sink| {
                lower_spatial(b, env, sink, acc_heap, mode, else_)
            })?;
            let h = sink.emit_heap(HeapInst::Ternary(c.clone(), h_t, h_e));
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
            Ok((h, bv))
        }
        S::Pure(p) => {
            let v = pure_exp::lower(b, env, sink, hctx, p)?;
            Ok((acc_heap, Some(v)))
        }
    }
}

fn lower_acc<C: InstContext, Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink<C>,
    hctx: HeapCtx,
    res: &typed::ResourceExp<Ext>,
    perm: &typed::TypedPureExp<Ext>,
) -> Result<HeapVal, TranslationError> {
    use typed::ResourceExpKind as R;
    let perm_val = pure_exp::lower(b, env, sink, hctx, perm)?;
    match &*res.0 {
        R::Field(base, fname) => {
            let base_val = pure_exp::lower(b, env, sink, hctx, base)?;
            field_acc_delta(b, sink, base_val, fname.0, perm_val)
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
            let addr = sink.emit_pure(
                ret_ty,
                PureInst::FunctionCall(
                    HeapVal::Empty,
                    FunctionCall {
                        function: addr_fn,
                        args,
                    },
                ),
            );
            Ok(sink.emit_heap(HeapInst::Acc(Acc {
                loc: addr,
                perm: perm_val,
            })))
        }
    }
}

/// Emit the single-chunk heap delta for `acc(base.fname, perm)`: the field's
/// `@addr` function applied to `base`, followed by a `HeapInst::Acc`. Returns
/// the produced delta heap. Shared by `lower_acc` and `new(...)` lowering.
pub(crate) fn field_acc_delta<C: InstContext>(
    b: &Builder<'_>,
    sink: &mut Sink<C>,
    base: Val,
    fname: Spur,
    perm: Val,
) -> Result<HeapVal, TranslationError> {
    let &addr_fn = b.field_addr.get(&fname).ok_or_else(|| {
        TranslationError::UnknownIdent(b.interner.resolve(&fname).to_string())
    })?;
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

