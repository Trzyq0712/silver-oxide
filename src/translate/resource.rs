//! Lower `typed::SpatialExp` into a `vmir::ResourceBody`.

use std::collections::HashMap;

use lasso::Spur;

use crate::translate::pure_exp::{self, HeapCtx, OldHeaps, PcKind, PureExt, Sink};
use crate::translate::{Builder, TranslationError, lower_type};
use crate::viper::typed;
use crate::vmir::{
    self, FALSE, HeapInst, HeapVal, Polarity, PureInst, Sign, TRUE, Type, Val, none,
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
    pre_state: Option<HeapVal>,
) -> Result<vmir::ResourceBody, TranslationError> {
    let mut sink = Sink::new(val_base, heap_base);
    // `old(e)` in the postcondition reads the method pre-state. For a two-state
    // (`Ctx`) resource that heap is the caller-supplied ctx slot `HeapVal::Temp(0)`;
    // bind it as the (unlabeled) `old` baseline. A self-framed ensures has no
    // pre-state, so `old` is rejected at lowering (see `MethodEnsuresExt`).
    let labeled: HashMap<Spur, HeapVal> = HashMap::new();
    let old = pre_state.map(|baseline| OldHeaps {
        baseline,
        labeled: &labeled,
    });
    let (h, bv) = lower_spatial(
        b,
        env,
        &mut sink,
        initial_heap,
        SpatialMode::Inhale,
        old.as_ref(),
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
///
/// A branch is encoded into permission fractions rather than a heap multiplexer:
/// the enclosing `with_cond` path condition gates every `acc`'s permission (see
/// `gate_perm_by_pc`) and chunks are added to a single monotonic heap timeline
/// (no `HeapInst::Ternary`). The verifier's agreement axiom keeps values from
/// mutually-exclusive branches isolated, since their fractions are never both
/// positive.
pub(crate) fn lower_spatial<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    acc_heap: HeapVal,
    mode: SpatialMode,
    old: Option<&OldHeaps>,
    exp: &typed::SpatialExp<Ext>,
) -> Result<(HeapVal, Option<Val>), TranslationError> {
    use typed::SpatialExpKind as S;
    // Heaps to read heap-dependent sub-expressions from at this point.
    let hctx = mode.heap_ctx(acc_heap, old);
    match &*exp.0 {
        S::Acc(res, perm) => {
            let (loc, perm) = lower_acc(b, env, sink, hctx, res, perm)?;
            // Inhale adds the chunk; exhale subtracts it (so a later `perm`
            // observes the reduced heap).
            let sign = match mode {
                SpatialMode::Inhale => Sign::Add,
                SpatialMode::Exhale { .. } => Sign::Sub,
            };
            let inst = HeapInst::Combine {
                base: acc_heap,
                sign,
                loc,
                perm,
            };
            // Always carry the path condition: an `acc` has a permission ≥ 0
            // side condition that must be discharged under the conditions
            // reaching it (and an inhale produces a pc-gated assumption). E.g.
            // in `p >= none && acc(x.f, p)` the threaded `p >= none` is what
            // makes `p >= 0` provable.
            let h_out = sink.emit_heap_guarded(inst);
            Ok((h_out, None))
        }
        S::Conj(l, r) => {
            let (h_mid, b_l) = lower_spatial(b, env, sink, acc_heap, mode, old, l)?;
            // `A && B`: by short-circuit semantics B is only reached when A
            // holds, so A's boolean is part of B's path condition. Threading it
            // lets B's side conditions (e.g. an `acc` permission ≥ 0) assume the
            // facts of A — e.g. `p >= none && acc(x.f, p)` discharges `p >= 0`.
            let (h_out, b_r) = match b_l.clone() {
                Some(v) => sink.with_cond(v, Polarity::Positive, PcKind::Fact, |sink| {
                    lower_spatial(b, env, sink, h_mid, mode, old, r)
                })?,
                None => lower_spatial(b, env, sink, h_mid, mode, old, r)?,
            };

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
            // `with_cond` pushes `c` onto the path condition; that stack is both
            // the body's side-condition guard and the source of the permission
            // gating (see `gate_perm_by_pc`), so no separate guard value is built.
            let (h_out, b_b) =
                sink.with_cond(c.clone(), Polarity::Positive, PcKind::Branch, |sink| {
                    lower_spatial(b, env, sink, acc_heap, mode, old, body)
                })?;
            // c ==> b_b  =  c ? b_b : true. When body has no boolean, the
            // whole implication is trivially true.
            let bv = b_b.map(|v| sink.emit_pure(Type::Bool, PureInst::Ternary(c, v, TRUE)));
            Ok((h_out, bv))
        }
        S::Ternary { if_, then, else_ } => {
            let c = pure_exp::lower(b, env, sink, hctx, if_)?;
            // Both arms add their gated chunks to the same timeline, in order:
            // then onto `acc_heap`, else onto the then-result. No heap ternary;
            // the else arm's negative polarity is applied by flipping ternary
            // branches in `gate_perm_by_pc`, not by materializing `!c`.
            let (h_mid, b_t) =
                sink.with_cond(c.clone(), Polarity::Positive, PcKind::Branch, |sink| {
                    lower_spatial(b, env, sink, acc_heap, mode, old, then)
                })?;
            let (h_out, b_e) =
                sink.with_cond(c.clone(), Polarity::Negative, PcKind::Branch, |sink| {
                    lower_spatial(b, env, sink, h_mid, mode, old, else_)
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

/// Gate a permission amount by the current path condition: each branch literal
/// wraps `perm` in a ternary, with `none` (0) on the *dead* side. A positive
/// literal `b` yields `b ? perm : none`; a negative literal (the else arm)
/// yields `b ? none : perm` — flipped branches instead of a materialized `!b`.
/// The empty path condition (top level) returns `perm` unchanged.
pub(crate) fn gate_perm_by_pc(sink: &mut Sink, perm: Val) -> Val {
    let mut v = perm;
    // Only *branch* conditions gate permissions: a separating-conjunction
    // `Fact` is an assertion (abort if false), so its `acc` keeps the bare
    // permission. Innermost literal first, so the outermost guard ends outermost.
    for (lit, pol) in sink.branch_conds().into_iter().rev() {
        let (then_, else_) = match pol {
            Polarity::Positive => (v, none()),
            Polarity::Negative => (none(), v),
        };
        v = sink.emit_pure(Type::Real, PureInst::Ternary(lit, then_, else_));
    }
    v
}

/// Gate a written *value* by the current branch path condition, keeping the
/// prior value `old` on the dead side: each branch literal wraps the value in a
/// `lit ? val : old` (positive) or `lit ? old : val` (negative). Used for a
/// field assignment inside an `if` arm, where the heap is a single timeline (no
/// heap ternary) so the *value* must carry the branch instead of the chunk. The
/// empty top-level pc returns `val` unchanged.
pub(crate) fn gate_value_by_pc(sink: &mut Sink, val: Val, old: Val, ty: Type) -> Val {
    let mut v = val;
    for (lit, pol) in sink.branch_conds().into_iter().rev() {
        let (then_, else_) = match pol {
            Polarity::Positive => (v, old.clone()),
            Polarity::Negative => (old.clone(), v),
        };
        v = sink.emit_pure(ty.clone(), PureInst::Ternary(lit, then_, else_));
    }
    v
}

/// Lower `acc(res, perm)` to its location and (pc-gated) permission amount. The
/// caller emits the `HeapInst::Combine` that adds/subtracts the chunk.
fn lower_acc<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink,
    hctx: HeapCtx<'_>,
    res: &typed::ResourceExp<Ext>,
    perm: &typed::TypedPureExp<Ext>,
) -> Result<(Val, Val), TranslationError> {
    let perm_val = pure_exp::lower(b, env, sink, hctx, perm)?;
    let perm_val = gate_perm_by_pc(sink, perm_val);
    let addr = lower_resource_addr(b, env, sink, hctx, res)?;
    Ok((addr, perm_val))
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
            field_addr(b, sink, base_val, fname.0)
        }
        R::PredicateCall(call) => {
            // The predicate's address location IS the predicate itself: its id is
            // the `LocId`; the verifier synthesizes the signature via
            // `Resource::derive_location`. No `@addr` decl exists.
            let &pred_id = b.name_map.get(&call.name.0).ok_or_else(|| {
                TranslationError::UnknownIdent(b.interner.resolve(&call.name.0).to_string())
            })?;
            let mut args = Vec::with_capacity(call.args.len());
            for a in &call.args {
                args.push(pure_exp::lower(b, env, sink, hctx, a)?);
            }
            let ret_ty = Type::Addr(Box::new(Type::Snap(pred_id)));
            Ok(sink.emit_pure(ret_ty, PureInst::Location(pred_id, args)))
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
            let bb = sink.with_cond(c.clone(), Polarity::Positive, PcKind::Branch, |sink| {
                lower_assertion_bool(b, env, sink, heap, old, body)
            })?;
            // c ==> bb  =  c ? bb : true
            Ok(bb.map(|v| sink.emit_pure(Type::Bool, PureInst::Ternary(c, v, TRUE))))
        }
        S::Ternary { if_, then, else_ } => {
            let c = pure_exp::lower(b, env, sink, hctx, if_)?;
            let bt = sink.with_cond(c.clone(), Polarity::Positive, PcKind::Branch, |sink| {
                lower_assertion_bool(b, env, sink, heap, old, then)
            })?;
            let be = sink.with_cond(c.clone(), Polarity::Negative, PcKind::Branch, |sink| {
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

/// Emit `field@addr(base)`: the field's heap-independent `@addr` function
/// applied to the receiver, typed `Addr<field_ty>`. Shared by every site that
/// needs a field location (`acc`, `perm`, `new`, field assignment).
pub(crate) fn field_addr(
    b: &Builder<'_>,
    sink: &mut Sink,
    base: Val,
    fname: Spur,
) -> Result<Val, TranslationError> {
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
    Ok(sink.emit_pure(ret_ty, PureInst::Location(addr_fn, vec![base])))
}

/// Lower `acc(base.fname, perm)` to its `(loc, perm)`: the field's `@addr`
/// function applied to `base`, paired with the permission amount. The caller
/// emits the `HeapInst::Combine`. Shared by `new(...)` lowering.
pub(crate) fn field_acc(
    b: &Builder<'_>,
    sink: &mut Sink,
    base: Val,
    fname: Spur,
    perm: Val,
) -> Result<(Val, Val), TranslationError> {
    let addr = field_addr(b, sink, base, fname)?;
    Ok((addr, perm))
}
