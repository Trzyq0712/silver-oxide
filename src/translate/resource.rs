//! Lower `typed::ResourceExp` (the addressable resources `e.f` / `P(args)`) to
//! its VMIR address `Val`. An address is an ordinary heap-independent function
//! call (`field@addr(base)` / the predicate's own id applied to its args).

use std::collections::HashMap;

use lasso::Spur;

use crate::translate::pure_exp::{self, HeapCtx, PureExt};
use crate::translate::sink::Sink;
use crate::translate::{TranslationContext, TranslationError};
use crate::viper::typed;
use crate::vmir::{self, PureInst, Type, Val};

/// Lower a `ResourceExp` to its address: the `@addr` function applied to the
/// resource's base/arguments (`field@addr(base)` or `pred@addr(args)`). The
/// `@addr` call is heap-independent. Shared by `acc`, `perm`, and `new`.
pub(crate) fn lower_resource_addr<Ext: PureExt>(
    b: &TranslationContext<'_>,
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
            // The predicate's address type: group = its interned tag, value = its
            // snapshot, unbounded permission cap. The address is an ordinary call
            // to the predicate's address function (its own id).
            let group = b.group_tag(call.name.0);
            let ret_ty = Type::addr(group, Type::Snap(pred_id), vmir::Bound::Unbounded);
            Ok(sink.emit_pure(
                ret_ty,
                PureInst::FunctionCall(vmir::FunctionCall {
                    function: pred_id,
                    type_args: Vec::new(),
                    args: args.into(),
                    // A predicate `@addr`, not a Silver `function`.
                    export: false,
                }),
            ))
        }
    }
}

/// Emit `field@addr(base)`: the field's heap-independent `@addr` function
/// applied to the receiver, typed `Addr<field_ty>`. Shared by every site that
/// needs a field location (`acc`, `perm`, `new`, field assignment).
pub(crate) fn field_addr(
    b: &TranslationContext<'_>,
    sink: &mut Sink,
    base: Val,
    fname: Spur,
) -> Result<Val, TranslationError> {
    // The field's address type: group = the field's interned tag, value = the
    // field's (already lowered) value type, bound = full permission `1/1`.
    let group = b.group_tag(fname);
    let value =
        b.field_types.get(&fname).cloned().ok_or_else(|| {
            TranslationError::UnknownIdent(b.interner.resolve(&fname).to_string())
        })?;
    let bound = vmir::Bound::Bounded(num::BigRational::from(num::BigInt::from(1)));
    let ret_ty = Type::addr(group, value, bound);
    // The field's address is an ordinary call to its address function (declared by
    // `declare_field_accessor` under the field's bare name).
    let field_id = *b
        .name_map
        .get(&fname)
        .ok_or_else(|| TranslationError::UnknownIdent(b.interner.resolve(&fname).to_string()))?;
    Ok(sink.emit_pure(
        ret_ty,
        PureInst::FunctionCall(vmir::FunctionCall {
            function: field_id,
            type_args: Vec::new(),
            args: vec![base].into(),
            // A field `@addr`, not a Silver `function`.
            export: false,
        }),
    ))
}

/// Lower `acc(base.fname, perm)` to its `(loc, perm)`: the field's `@addr`
/// function applied to `base`, paired with the permission amount. The caller
/// emits the `HeapInst::Add`. Shared by `new(...)` lowering.
pub(crate) fn field_acc(
    b: &TranslationContext<'_>,
    sink: &mut Sink,
    base: Val,
    fname: Spur,
    perm: Val,
) -> Result<(Val, Val), TranslationError> {
    let addr = field_addr(b, sink, base, fname)?;
    Ok((addr, perm))
}
