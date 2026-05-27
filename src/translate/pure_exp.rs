//! Lower `final_ast::TypedPureExp<Ext>` into VMIR `PureInst` chains.

use std::collections::HashMap;

use lasso::Spur;

use crate::silver::final_ast;
use crate::translate::{Builder, TranslationError, lower_type};
use crate::vmir::{
    self, Context, FALSE, HeapInst, HeapVal, Inst, InstKind, Literal, PathCond, PureInst, TRUE,
    UnOp, Val,
};

/// A mutable sink for emitted instructions plus the running counters,
/// parameterised by the body's `Context`. The choice of `C` controls which
/// extension variants the caller is allowed to construct.
pub(crate) struct Sink<C: Context> {
    pub insts: Vec<Inst<C::HeapExt, C::InstExt, C::HeapValExt>>,
    pub val_base: usize,
    pub val_count: usize,
    pub heap_count: usize,
}

impl<C: Context> Sink<C> {
    pub fn new(val_base: usize) -> Self {
        Self {
            insts: Vec::new(),
            val_base,
            val_count: 0,
            heap_count: 0,
        }
    }

    pub fn next_val_temp(&mut self) -> Val {
        let id = self.val_base + self.val_count;
        self.val_count += 1;
        Val::Temp(id)
    }

    pub fn next_heap_temp(&mut self) -> HeapVal<C::HeapValExt> {
        let id = self.heap_count;
        self.heap_count += 1;
        HeapVal::Temp(id)
    }

    pub fn emit_pure(&mut self, ty: vmir::Type, inst: PureInst<C::HeapValExt>) -> Val {
        let v = self.next_val_temp();
        self.insts.push(Inst {
            pc: PathCond::default(),
            kind: InstKind::Pure(ty, inst),
        });
        v
    }

    /// Push a heap instruction. `HeapInst<C::HeapExt, C::HeapValExt>`
    /// constrains which variants are constructible: in `Sink<ResourceCtx>`
    /// the `Ext` arm is uninhabited (`!`); in `Sink<MethodCtx>` the
    /// `HeapVal::CtxHeap` operand is uninhabited.
    pub fn emit_heap(
        &mut self,
        inst: HeapInst<C::HeapExt, C::HeapValExt>,
    ) -> HeapVal<C::HeapValExt> {
        let h = self.next_heap_temp();
        self.insts.push(Inst {
            pc: PathCond::default(),
            kind: InstKind::Heap(inst),
        });
        h
    }

    /// Push an instruction-kind extension. For `Sink<ResourceCtx>` the
    /// parameter type is `!`, so this method is uncallable.
    pub fn emit_ext(&mut self, ext: C::InstExt) {
        self.insts.push(Inst {
            pc: PathCond::default(),
            kind: InstKind::Ext(ext),
        });
    }
}

pub(crate) fn lower<C: Context, Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink<C>,
    exp: &final_ast::TypedPureExp<Ext>,
) -> Result<Val, TranslationError> {
    use final_ast::PureExpKind as P;
    let ty = lower_type(&exp.ty);
    match &*exp.exp {
        P::Ident(id) => env
            .get(&id.0)
            .cloned()
            .ok_or_else(|| TranslationError::UnknownIdent(b.interner.resolve(&id.0).to_string())),
        P::Const(lit) => Ok(Val::Literal(lower_literal(lit)?)),
        P::Unary(op, x) => {
            let v = lower(b, env, sink, x)?;
            let vop = match op {
                final_ast::UnOp::Not => UnOp::Not,
                final_ast::UnOp::Neg => UnOp::Neg,
                final_ast::UnOp::Cardinality => {
                    return Err(TranslationError::Unsupported("cardinality"));
                }
            };
            Ok(sink.emit_pure(ty, PureInst::Unary(vop, v)))
        }
        P::Binary(op, l, r) => lower_binary(b, env, sink, ty, op, l, r),
        P::Ternary { if_, then, else_ } => {
            let c = lower(b, env, sink, if_)?;
            let t = lower(b, env, sink, then)?;
            let e = lower(b, env, sink, else_)?;
            Ok(sink.emit_pure(ty, PureInst::Ternary(c, t, e)))
        }
        P::Ext(ext) => Ext::lower_ext(b, env, sink, ext),
        P::Unfolding(_, _) => Err(TranslationError::Unsupported("unfolding")),
        P::FunctionCall(_) => Err(TranslationError::Unsupported("function call")),
        P::LetIn { .. } => Err(TranslationError::Unsupported("let-in")),
        P::Ascribe(_, _) => Err(TranslationError::Unsupported("ascribe")),
        P::AdtDestructor(_, _) => Err(TranslationError::Unsupported("ADT destructor")),
        P::AdtDiscriminator(_, _) => Err(TranslationError::Unsupported("ADT discriminator")),
    }
}

fn lower_binary<C: Context, Ext: PureExt>(
    b: &Builder<'_>,
    env: &HashMap<Spur, Val>,
    sink: &mut Sink<C>,
    ty: vmir::Type,
    op: &final_ast::BinOp,
    l: &final_ast::TypedPureExp<Ext>,
    r: &final_ast::TypedPureExp<Ext>,
) -> Result<Val, TranslationError> {
    use final_ast::BinOp as B;
    use vmir::BinOp as V;
    let lv = lower(b, env, sink, l)?;
    let rv = lower(b, env, sink, r)?;
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
            sink.emit_pure(ty, PureInst::Unary(UnOp::Not, eq))
        }
        B::Le => {
            // l <= r  <=>  !(r < l)
            let gt = sink.emit_pure(vmir::Type::Bool, PureInst::Binary(V::Lt, rv, lv));
            sink.emit_pure(ty, PureInst::Unary(UnOp::Not, gt))
        }
        B::Gt => sink.emit_pure(ty, PureInst::Binary(V::Lt, rv, lv)),
        B::Ge => {
            // l >= r  <=>  !(l < r)
            let lt = sink.emit_pure(vmir::Type::Bool, PureInst::Binary(V::Lt, lv, rv));
            sink.emit_pure(ty, PureInst::Unary(UnOp::Not, lt))
        }
        B::And => sink.emit_pure(ty, PureInst::Ternary(lv, rv, FALSE)),
        B::Or => sink.emit_pure(ty, PureInst::Ternary(lv, TRUE, rv)),
        B::Implies => sink.emit_pure(ty, PureInst::Ternary(lv, rv, TRUE)),
        B::Iff => sink.emit_pure(ty, PureInst::Binary(V::Eq, lv, rv)),
        B::In | B::Union | B::SetMinus | B::Intersection | B::Subset | B::Concat | B::Range => {
            return Err(TranslationError::Unsupported("collection operator"));
        }
    })
}

pub(crate) fn lower_literal(lit: &final_ast::Literal) -> Result<Literal, TranslationError> {
    match lit {
        final_ast::Literal::Bool(b) => Ok(Literal::Bool(*b)),
        final_ast::Literal::Int(n) => Ok(Literal::Int(n.clone())),
        final_ast::Literal::Real(r) => Ok(Literal::Real(r.clone())),
        final_ast::Literal::Null => Ok(Literal::Null),
        final_ast::Literal::Wildcard => Err(TranslationError::Unsupported("wildcard literal")),
    }
}

/// Per-context lowering of pure-expression extensions (`old`, `result`,
/// `perm`, etc.). All currently unsupported in this minimal cut.
pub(crate) trait PureExt: Sized + Clone + std::fmt::Debug {
    fn lower_ext<C: Context>(
        b: &Builder<'_>,
        env: &HashMap<Spur, Val>,
        sink: &mut Sink<C>,
        ext: &Self,
    ) -> Result<Val, TranslationError>;
}

impl PureExt for ! {
    fn lower_ext<C: Context>(
        _b: &Builder<'_>,
        _env: &HashMap<Spur, Val>,
        _sink: &mut Sink<C>,
        ext: &Self,
    ) -> Result<Val, TranslationError> {
        match *ext {}
    }
}

impl PureExt for final_ast::MethodEnsuresExt {
    fn lower_ext<C: Context>(
        _b: &Builder<'_>,
        _env: &HashMap<Spur, Val>,
        _sink: &mut Sink<C>,
        _ext: &Self,
    ) -> Result<Val, TranslationError> {
        Err(TranslationError::Unsupported("`old` in method ensures"))
    }
}

impl PureExt for final_ast::MethodBodyExt {
    fn lower_ext<C: Context>(
        _b: &Builder<'_>,
        _env: &HashMap<Spur, Val>,
        _sink: &mut Sink<C>,
        _ext: &Self,
    ) -> Result<Val, TranslationError> {
        Err(TranslationError::Unsupported(
            "`old`/`perm` in method body",
        ))
    }
}
