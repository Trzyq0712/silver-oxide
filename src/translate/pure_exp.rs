//! Lower `typed::TypedPureExp<Ext>` into VMIR `PureInst` chains.

use std::collections::HashMap;

use lasso::Spur;

use crate::viper::typed;
use crate::translate::{Builder, TranslationError, lower_type};
use crate::vmir::{
    self, FALSE, FunctionCall, HeapInst, HeapVal, Inst, InstContext, InstKind, Literal, PathConds,
    Polarity, PureInst, TRUE, Val,
};

/// A mutable sink for emitted instructions plus the running counters,
/// parameterised by the body's `InstContext`. The choice of `C` controls
/// which extension variants the caller is allowed to construct.
pub(crate) struct Sink<C: InstContext> {
    pub insts: Vec<Inst<C>>,
    pub val_base: usize,
    pub val_count: usize,
    pub heap_count: usize,
    /// Running path condition of the lowering point. Sidecond instructions
    /// are emitted gated by this; branch arms push/pop guards via `with_cond`.
    pub pc: PathConds,
}

impl<C: InstContext> Sink<C> {
    pub fn new(val_base: usize, heap_base: usize) -> Self {
        Self {
            insts: Vec::new(),
            val_base,
            val_count: 0,
            heap_count: heap_base,
            pc: PathConds::default(),
        }
    }

    /// Run `f` with `(cond, pol)` pushed onto the path condition, popping it
    /// afterwards. The pop runs even when `f` returns `Err`, keeping the
    /// guard stack balanced.
    pub(crate) fn with_cond<R>(
        &mut self,
        cond: Val,
        pol: Polarity,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.pc.conds.push((cond, pol));
        let r = f(self);
        self.pc.conds.pop();
        r
    }

    pub fn next_val_temp(&mut self) -> Val {
        let id = self.val_base + self.val_count;
        self.val_count += 1;
        Val::Temp(id)
    }

    pub fn next_heap_temp(&mut self) -> HeapVal {
        let id = self.heap_count;
        self.heap_count += 1;
        HeapVal::Temp(id)
    }

    /// Path condition to attach to `kind`: the running guard for sidecond
    /// instructions, empty for total ones (so `Inst::new`'s debug-assert
    /// never trips and the IR stays flat where no guard is needed).
    fn pc_for(&self, kind: &InstKind<C>) -> PathConds {
        if kind.uses_pc() {
            self.pc.clone()
        } else {
            PathConds::default()
        }
    }

    pub fn emit_pure(&mut self, ty: vmir::Type, inst: PureInst<C::PureExt>) -> Val {
        let v = self.next_val_temp();
        let kind = InstKind::Pure(ty, inst);
        let pc = self.pc_for(&kind);
        self.insts.push(Inst::new(pc, kind));
        v
    }

    pub fn emit_heap(&mut self, inst: HeapInst<C::HeapExt>) -> HeapVal {
        let h = self.next_heap_temp();
        let kind = InstKind::Heap(inst);
        let pc = self.pc_for(&kind);
        self.insts.push(Inst::new(pc, kind));
        h
    }

    /// Push an instruction-kind extension. For `Sink<ResourceCtx>` the
    /// parameter type is `!`, so this method is uncallable.
    pub fn emit_ext(&mut self, ext: C::InstExt) {
        let kind = InstKind::Ext(ext);
        let pc = self.pc_for(&kind);
        self.insts.push(Inst::new(pc, kind));
    }
}

/// Heaps a pure expression reads from. `value` is used by field derefs and
/// heap-dependent functions; `perm` is used by `perm(loc)`. They differ only on
/// `exhale`, where value reads use the pre-exhale heap but `perm` tracks the
/// running (subtracted) heap; elsewhere both are the same heap.
#[derive(Clone, Copy)]
pub(crate) struct HeapCtx {
    pub value: HeapVal,
    pub perm: HeapVal,
}

impl HeapCtx {
    /// Both reads from the same heap (the common case).
    pub(crate) fn same(heap: HeapVal) -> Self {
        Self {
            value: heap,
            perm: heap,
        }
    }
}

pub(crate) fn lower<C: InstContext, Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink<C>,
    hctx: HeapCtx,
    exp: &typed::TypedPureExp<Ext>,
) -> Result<Val, TranslationError> {
    use typed::PureExpKind as P;
    let ty = lower_type(&exp.ty);
    match &*exp.exp {
        P::Ident(id) => env
            .get(&id.0)
            .cloned()
            .ok_or_else(|| TranslationError::UnknownIdent(b.interner.resolve(&id.0).to_string())),
        P::Const(lit) => Ok(Val::Literal(lower_literal(lit)?)),
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
            let t = sink
                .with_cond(c.clone(), Polarity::Positive, |sink| lower(b, env, sink, hctx, then))?;
            let e = sink
                .with_cond(c.clone(), Polarity::Negative, |sink| lower(b, env, sink, hctx, else_))?;
            Ok(sink.emit_pure(ty, PureInst::Ternary(c, t, e)))
        }
        P::Field(base, id) => {
            let base = lower(b, env, sink, hctx, base)?;
            let &field_fn = b.field_addr.get(&id.0).ok_or_else(|| {
                TranslationError::UnknownIdent(b.interner.resolve(&id.0).to_string())
            })?;
            let addr_ty = vmir::Type::Addr(Box::new(ty.clone()));
            let field_addr = sink.emit_pure(
                addr_ty,
                PureInst::FunctionCall(
                    HeapVal::Empty,
                    FunctionCall {
                        function: field_fn,
                        args: vec![base],
                    },
                ),
            );
            Ok(sink.emit_pure(ty, PureInst::Deref(hctx.value, field_addr)))
        }
        P::Unfolding(_, _) => Err(TranslationError::Unsupported("unfolding")),
        P::FunctionCall(_) => Err(TranslationError::Unsupported("function call")),
        P::LetIn { .. } => Err(TranslationError::Unsupported("let-in")),
        P::Ascribe(_, _) => Err(TranslationError::Unsupported("ascribe")),
        P::AdtDestructor(_, _) => Err(TranslationError::Unsupported("ADT destructor")),
        P::AdtDiscriminator(_, _) => Err(TranslationError::Unsupported("ADT discriminator")),
        P::Ext(ext) => Ext::lower_ext(b, env, sink, hctx, ty, ext),
    }
}

fn lower_binary<C: InstContext, Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink<C>,
    hctx: HeapCtx,
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
            let rv = sink
                .with_cond(lv.clone(), Polarity::Positive, |sink| lower(b, env, sink, hctx, r))?;
            return Ok(sink.emit_pure(ty, PureInst::Ternary(lv, rv, FALSE)));
        }
        B::Or => {
            // l || r  =  l ? true : r
            let rv = sink
                .with_cond(lv.clone(), Polarity::Negative, |sink| lower(b, env, sink, hctx, r))?;
            return Ok(sink.emit_pure(ty, PureInst::Ternary(lv, TRUE, rv)));
        }
        B::Implies => {
            // l ==> r  =  l ? r : true
            let rv = sink
                .with_cond(lv.clone(), Polarity::Positive, |sink| lower(b, env, sink, hctx, r))?;
            return Ok(sink.emit_pure(ty, PureInst::Ternary(lv, rv, TRUE)));
        }
        _ => {}
    }
    // Strict ops: both operands always evaluate, so `r` is lowered under the
    // outer path condition unchanged.
    let rv = lower(b, env, sink, hctx, r)?;
    Ok(match op {
        B::Plus => sink.emit_pure(ty, PureInst::Binary(V::Plus, lv, rv)),
        B::Minus => sink.emit_pure(ty, PureInst::Binary(V::Minus, lv, rv)),
        B::Mult => sink.emit_pure(ty, PureInst::Binary(V::Mult, lv, rv)),
        B::Div => sink.emit_pure(ty, PureInst::Binary(V::Div, lv, rv)),
        B::Mod => sink.emit_pure(ty, PureInst::Binary(V::Mod, lv, rv)),
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
pub(crate) trait PureExt: Sized + Clone + std::fmt::Debug {
    fn lower_ext<C: InstContext>(
        b: &Builder<'_>,
        env: &HashMap<Spur, Val>,
        sink: &mut Sink<C>,
        hctx: HeapCtx,
        ty: vmir::Type,
        ext: &Self,
    ) -> Result<Val, TranslationError>;
}

impl PureExt for ! {
    fn lower_ext<C: InstContext>(
        _b: &Builder<'_>,
        _env: &HashMap<Spur, Val>,
        _sink: &mut Sink<C>,
        _hctx: HeapCtx,
        _ty: vmir::Type,
        ext: &Self,
    ) -> Result<Val, TranslationError> {
        match *ext {}
    }
}

impl PureExt for typed::MethodEnsuresExt {
    fn lower_ext<C: InstContext>(
        _b: &Builder<'_>,
        _env: &HashMap<Spur, Val>,
        _sink: &mut Sink<C>,
        _hctx: HeapCtx,
        _ty: vmir::Type,
        _ext: &Self,
    ) -> Result<Val, TranslationError> {
        Err(TranslationError::Unsupported("`old` in method ensures"))
    }
}

impl PureExt for typed::MethodBodyExt {
    fn lower_ext<C: InstContext>(
        b: &Builder<'_>,
        env: &HashMap<Spur, Val>,
        sink: &mut Sink<C>,
        hctx: HeapCtx,
        ty: vmir::Type,
        ext: &Self,
    ) -> Result<Val, TranslationError> {
        use crate::viper::typed::ResourceExpKind as R;
        match ext {
            typed::MethodBodyExt::Old(..) => {
                Err(TranslationError::Unsupported("`old` in method body"))
            }
            // perm(loc): query the permission held at `loc` in the perm heap.
            typed::MethodBodyExt::Perm(res) => {
                let addr = match &*res.0 {
                    R::Field(base, fname) => {
                        let base_val = lower(b, env, sink, hctx, base)?;
                        let &addr_fn = b.field_addr.get(&fname.0).ok_or_else(|| {
                            TranslationError::UnknownIdent(b.interner.resolve(&fname.0).to_string())
                        })?;
                        let field_ty = b
                            .globals
                            .resolve(fname.0)
                            .and_then(|s| s.as_field().cloned())
                            .ok_or_else(|| {
                                TranslationError::UnknownIdent(
                                    b.interner.resolve(&fname.0).to_string(),
                                )
                            })?;
                        let ret_ty = vmir::Type::Addr(Box::new(lower_type(&field_ty)));
                        sink.emit_pure(
                            ret_ty,
                            PureInst::FunctionCall(
                                HeapVal::Empty,
                                FunctionCall {
                                    function: addr_fn,
                                    args: vec![base_val],
                                },
                            ),
                        )
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
                            args.push(lower(b, env, sink, hctx, a)?);
                        }
                        let ret_ty = vmir::Type::Addr(Box::new(vmir::Type::Domain(snap_id)));
                        sink.emit_pure(
                            ret_ty,
                            PureInst::FunctionCall(
                                HeapVal::Empty,
                                FunctionCall {
                                    function: addr_fn,
                                    args,
                                },
                            ),
                        )
                    }
                };
                let pe = C::perm_pure_ext(hctx.perm, addr)
                    .ok_or(TranslationError::Unsupported("perm in this context"))?;
                Ok(sink.emit_pure(ty, PureInst::Ext(pe)))
            }
        }
    }
}
