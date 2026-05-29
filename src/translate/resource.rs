//! Lower `final_ast::SpatialExp` into a `vmir::ResourceBody`.

use std::collections::HashMap;

use lasso::Spur;

use crate::silver::final_ast;
use crate::translate::pure_exp::{self, PureExt, Sink};
use crate::translate::{Builder, TranslationError};
use crate::vmir::{
    self, Acc, FALSE, FunctionCall, HeapInst, HeapVal, PureInst, ResourceCtx, TRUE, Type, Val,
};

/// Lower a resource body. `initial_heap` is the body's starting heap
/// reference; pass `HeapVal::Empty` when the owning `Resource.requires`
/// is `None`, and `HeapVal::Temp(0)` (with `heap_base = 1`) once the
/// resource has its own precondition resource. `heap_base` is the first
/// heap counter the body's emitted heap insts will use.
pub(crate) fn lower_spatial_never(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    exp: &final_ast::SpatialExp<!>,
    val_base: usize,
    initial_heap: HeapVal,
    heap_base: usize,
) -> Result<vmir::ResourceBody, TranslationError> {
    let mut sink = Sink::<ResourceCtx>::new(val_base, heap_base);
    let (h, bv) = lower_spatial::<!>(b, env, &mut sink, initial_heap, exp)?;
    Ok(vmir::ResourceBody {
        insts: sink.insts,
        res: (h, bv.unwrap_or(TRUE)),
    })
}

pub(crate) fn lower_spatial_ensures(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    exp: &final_ast::SpatialExp<final_ast::MethodEnsuresExt>,
    val_base: usize,
    initial_heap: HeapVal,
    heap_base: usize,
) -> Result<vmir::ResourceBody, TranslationError> {
    let mut sink = Sink::<ResourceCtx>::new(val_base, heap_base);
    let (h, bv) =
        lower_spatial::<final_ast::MethodEnsuresExt>(b, env, &mut sink, initial_heap, exp)?;
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
pub(crate) fn lower_spatial<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink<ResourceCtx>,
    heap: HeapVal,
    exp: &final_ast::SpatialExp<Ext>,
) -> Result<(HeapVal, Option<Val>), TranslationError> {
    use final_ast::SpatialExpKind as S;
    match &*exp.0 {
        S::Acc(res, perm) => {
            let delta = lower_acc(b, env, sink, heap, res, perm)?;
            let h_out = sink.emit_heap(HeapInst::Add(heap, delta));
            Ok((h_out, None))
        }
        S::Conj(l, r) => {
            let (h_mid, b_l) = lower_spatial(b, env, sink, heap, l)?;
            let (h_out, b_r) = lower_spatial(b, env, sink, h_mid, r)?;

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
            let c = pure_exp::lower(b, env, sink, heap, cond)?;
            let (h_b, b_b) = lower_spatial(b, env, sink, heap, body)?;
            let h = sink.emit_heap(HeapInst::Ternary(c.clone(), h_b, heap));
            // c ==> b_b  =  c ? b_b : true. When body has no boolean, the
            // whole implication is trivially true.
            let bv = b_b.map(|v| sink.emit_pure(Type::Bool, PureInst::Ternary(c, v, TRUE)));
            Ok((h, bv))
        }
        S::Ternary { if_, then, else_ } => {
            let c = pure_exp::lower(b, env, sink, heap, if_)?;
            let (h_t, b_t) = lower_spatial(b, env, sink, heap, then)?;
            let (h_e, b_e) = lower_spatial(b, env, sink, heap, else_)?;
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
            let v = pure_exp::lower(b, env, sink, heap, p)?;
            Ok((heap, Some(v)))
        }
    }
}

fn lower_acc<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink<ResourceCtx>,
    heap: HeapVal,
    res: &final_ast::ResourceExp<Ext>,
    perm: &final_ast::TypedPureExp<Ext>,
) -> Result<HeapVal, TranslationError> {
    use final_ast::ResourceExpKind as R;
    let perm_val = pure_exp::lower(b, env, sink, heap, perm)?;
    match &*res.0 {
        R::Field(base, fname) => {
            let base_val = pure_exp::lower(b, env, sink, heap, base)?;
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
            let ret_ty = Type::Addr(Box::new(silver_type_to_vmir(&field_ty)));
            let addr = sink.emit_pure(
                ret_ty,
                PureInst::FunctionCall(
                    HeapVal::Empty,
                    FunctionCall {
                        function: addr_fn,
                        args: vec![base_val],
                    },
                ),
            );
            Ok(sink.emit_heap(HeapInst::Acc(Acc {
                loc: addr,
                perm: perm_val,
            })))
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
                args.push(pure_exp::lower(b, env, sink, heap, a)?);
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

/// Bridge from `silver::Type` (used by `silver::Globals`) to `vmir::Type`.
fn silver_type_to_vmir(ty: &crate::silver::Type) -> vmir::Type {
    use crate::silver::Type as S;
    match ty {
        S::Bool => vmir::Type::Bool,
        S::Int => vmir::Type::Int,
        S::Real => vmir::Type::Real,
        S::Ref => vmir::Type::Ref,
        S::Generic(_) | S::Domain(_, _) => vmir::Type::Ref,
    }
}
