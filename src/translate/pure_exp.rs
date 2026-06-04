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

/// Fold a binary **arithmetic** op over two constant literals into a single
/// literal, at translation time. The result type drives Real-vs-Int math (so a
/// `Real`-typed `4/2` over Int literals folds to `Real(2)`). Returns `None` for
/// non-arithmetic ops (comparisons are left to the e-graph) or type mismatches.
fn fold_arith_literals(op: &typed::BinOp, l: &Literal, r: &Literal, ty: &vmir::Type) -> Option<Literal> {
    use num::BigRational;
    use typed::BinOp as B;
    let rat = |lit: &Literal| -> Option<BigRational> {
        match lit {
            Literal::Int(n) => Some(BigRational::from(n.clone())),
            Literal::Real(x) => Some(x.clone()),
            _ => None,
        }
    };
    match ty {
        vmir::Type::Real => {
            let (a, b) = (rat(l)?, rat(r)?);
            let v = match op {
                B::Plus => a + b,
                B::Minus => a - b,
                B::Mult => a * b,
                B::Div => a / b,
                _ => return None,
            };
            Some(Literal::Real(v))
        }
        vmir::Type::Int => {
            let (Literal::Int(a), Literal::Int(b)) = (l, r) else {
                return None;
            };
            let v = match op {
                B::Plus => a + b,
                B::Minus => a - b,
                B::Mult => a * b,
                B::Div => a / b,
                B::Mod => a % b,
                _ => return None,
            };
            Some(Literal::Int(v))
        }
        _ => None,
    }
}

/// Wrap `v` in `real(..)` when an `Int` operand is used where a `Real` is
/// expected, keeping every operation's e-graph operands homogeneous.
fn real_cast_if<C: InstContext>(
    sink: &mut Sink<C>,
    v: Val,
    operand_ty: &vmir::Type,
    target_ty: &vmir::Type,
) -> Val {
    if *target_ty == vmir::Type::Real && *operand_ty == vmir::Type::Int {
        sink.emit_pure(vmir::Type::Real, PureInst::RealCast(v))
    } else {
        v
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
    // Const-fold literal arithmetic at translation time, e.g. `4/2 => 2/1`
    // (one Real literal instead of `real(4) / real(2)`).
    if let (Val::Literal(la), Val::Literal(lb)) = (&lv, &rv) {
        if let Some(folded) = fold_arith_literals(op, la, lb, &ty) {
            return Ok(Val::Literal(folded));
        }
    }
    // Homogenize: a `Real`-result arithmetic op with an `Int` operand gets that
    // operand wrapped in `real(..)` so the e-graph operands share a type.
    let lv = real_cast_if(sink, lv, &lower_type(&l.ty), &ty);
    let rv = real_cast_if(sink, rv, &lower_type(&r.ty), &ty);
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
        match ext {
            typed::MethodBodyExt::Old(..) => {
                Err(TranslationError::Unsupported("`old` in method body"))
            }
            // perm(loc): query the permission held at `loc` in the perm heap.
            typed::MethodBodyExt::Perm(res) => {
                let addr =
                    crate::translate::resource::lower_resource_addr(b, env, sink, hctx, res)?;
                let pe = C::perm_pure_ext(hctx.perm, addr)
                    .ok_or(TranslationError::Unsupported("perm in this context"))?;
                Ok(sink.emit_pure(ty, PureInst::Ext(pe)))
            }
        }
    }
}
