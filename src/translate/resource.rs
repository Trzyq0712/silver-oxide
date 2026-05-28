//! Lower `final_ast::SpatialExp` into a `vmir::ResourceBody`.

use std::collections::HashMap;

use lasso::Spur;

use crate::silver::final_ast;
use crate::translate::pure_exp::{self, PureExt, Sink};
use crate::translate::{Builder, TranslationError};
use crate::vmir::{
    self, Acc, FALSE, FunctionCall, HeapInst, HeapVal, PureInst, ResourceCtx, TRUE, Type, Val,
};

pub(crate) fn lower_spatial_never(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    exp: &final_ast::SpatialExp<!>,
    val_base: usize,
) -> Result<vmir::ResourceBody, TranslationError> {
    let mut sink = Sink::<ResourceCtx>::new(val_base);
    let (h, bv) = lower_spatial::<!>(b, env, &mut sink, exp)?;
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
) -> Result<vmir::ResourceBody, TranslationError> {
    let mut sink = Sink::<ResourceCtx>::new(val_base);
    let (h, bv) = lower_spatial::<final_ast::MethodEnsuresExt>(b, env, &mut sink, exp)?;
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
    exp: &final_ast::SpatialExp<Ext>,
) -> Result<(HeapVal, Option<Val>), TranslationError> {
    use final_ast::SpatialExpKind as S;
    match &*exp.0 {
        S::Acc(res, perm) => {
            let h = lower_acc(b, env, sink, res, perm)?;
            Ok((h, None))
        }
        S::Conj(l, r) => {
            let (h_l, b_l) = lower_spatial(b, env, sink, l)?;
            let (h_r, b_r) = lower_spatial(b, env, sink, r)?;
            let h_sum = sink.emit_heap(HeapInst::Add(h_l, h_r));
            let b_sum = match (b_l, b_r) {
                (None, None) => None,
                (Some(v), None) | (None, Some(v)) => Some(v),
                // b_l && b_r  =  b_l ? b_r : false
                (Some(vl), Some(vr)) => {
                    Some(sink.emit_pure(Type::Bool, PureInst::Ternary(vl, vr, FALSE)))
                }
            };
            Ok((h_sum, b_sum))
        }
        S::Implies(cond, body) => {
            let c = pure_exp::lower(b, env, sink, cond)?;
            let (h_b, b_b) = lower_spatial(b, env, sink, body)?;
            let h = sink.emit_heap(HeapInst::Ternary(c.clone(), h_b, HeapVal::Empty));
            // c ==> b_b  =  c ? b_b : true. When body has no boolean, the
            // whole implication is trivially true.
            let bv = b_b.map(|v| sink.emit_pure(Type::Bool, PureInst::Ternary(c, v, TRUE)));
            Ok((h, bv))
        }
        S::Ternary { if_, then, else_ } => {
            let c = pure_exp::lower(b, env, sink, if_)?;
            let (h_t, b_t) = lower_spatial(b, env, sink, then)?;
            let (h_e, b_e) = lower_spatial(b, env, sink, else_)?;
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
            let v = pure_exp::lower(b, env, sink, p)?;
            Ok((HeapVal::Empty, Some(v)))
        }
    }
}

fn lower_acc<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink<ResourceCtx>,
    res: &final_ast::ResourceExp<Ext>,
    perm: &final_ast::TypedPureExp<Ext>,
) -> Result<HeapVal, TranslationError> {
    use final_ast::ResourceExpKind as R;
    let perm_val = lower_perm(b, env, sink, perm)?;
    match &*res.0 {
        R::Field(base, fname) => {
            let base_val = pure_exp::lower(b, env, sink, base)?;
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
                args.push(pure_exp::lower(b, env, sink, a)?);
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

fn lower_perm<Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink<ResourceCtx>,
    perm: &final_ast::TypedPureExp<Ext>,
) -> Result<Val, TranslationError> {
    pure_exp::lower(b, env, sink, perm)
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
