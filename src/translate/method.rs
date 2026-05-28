//! Lower a `final_ast::Method` body into a `vmir::Method` (a flat
//! `Vec<MethodInst>`). Straight-line only.

use std::collections::HashMap;

use lasso::Spur;

use crate::silver::final_ast;
use crate::translate::pure_exp::{self, Sink};
use crate::translate::{Builder, TranslationError, lower_type};
use crate::vmir::{
    self, HeapInst, HeapVal, Inst, InstExt, InstKind, MethodCtx, PathConds, PureInst, ResourceCall,
    Val,
};

pub(crate) fn lower_method(
    b: &Builder<'_>,
    m: &final_ast::Method,
    body: &final_ast::StmtBlock,
) -> Result<vmir::Method, TranslationError> {
    let mut sink = Sink::<MethodCtx>::new(0);
    let mut env: HashMap<Spur, Val> = HashMap::new();

    // Emit fresh values for params and rets inline. The method has no
    // signature on the VMIR side — params/rets are just initial Fresh insts.
    let mut param_vals: Vec<Val> = Vec::with_capacity(m.params.len());
    for p in &m.params {
        let v = sink.emit_pure(lower_type(&p.ty), PureInst::Fresh);
        env.insert(p.name.0, v.clone());
        param_vals.push(v);
    }
    let mut ret_vals: Vec<Val> = Vec::with_capacity(m.rets.len());
    for r in &m.rets {
        let v = sink.emit_pure(lower_type(&r.ty), PureInst::Fresh);
        env.insert(r.name.0, v.clone());
        ret_vals.push(v);
    }

    let mut current_heap: HeapVal = HeapVal::Empty;
    // Captures the heap delta produced by the method's `@requires`
    // resource. The `@ensures` resource is evaluated against this heap so
    // its body can refer to entry-state values (e.g. via `old(...)`).
    let mut pre_heap: HeapVal = HeapVal::Empty;

    // Inhale this method's own precondition: call self@requires, add delta,
    // assume bool.
    if let Some(&req_id) = b.method_requires.get(&m.name.0) {
        let (h_pre, b_pre) =
            emit_resource_call(&mut sink, req_id, current_heap, param_vals.clone());
        let h_new = sink.emit_heap(HeapInst::Add(current_heap, h_pre));
        sink.emit_ext(InstExt::Assume(b_pre));
        current_heap = h_new;
        pre_heap = h_pre;
    }

    for stmt in &body.0 {
        current_heap = lower_stmt(b, &mut env, &mut sink, current_heap, stmt)?;
    }

    // Exhale this method's own postcondition: call self@ensures with the
    // precondition's heap as ctx (so old/CtxDeref see entry-state values),
    // sub delta, assert bool.
    if let Some(&ens_id) = b.method_ensures.get(&m.name.0) {
        let mut ens_args = param_vals;
        ens_args.extend(ret_vals);
        let (h_post, b_post) = emit_resource_call(&mut sink, ens_id, pre_heap, ens_args);
        let _h_new = sink.emit_heap(HeapInst::Sub(current_heap, h_post));
        sink.emit_ext(InstExt::Assert(b_post));
    }

    Ok(vmir::Method { insts: sink.insts })
}

fn lower_stmt(
    b: &Builder<'_>,
    env: &mut HashMap<Spur, Val>,
    sink: &mut Sink<MethodCtx>,
    current_heap: HeapVal,
    stmt: &final_ast::Statement,
) -> Result<HeapVal, TranslationError> {
    use final_ast::Statement as S;
    match stmt {
        S::Var(idents, None) => {
            for id in idents {
                let ty = lower_type(&id.ty);
                let v = sink.emit_pure(ty, PureInst::Fresh);
                env.insert(id.name.0, v);
            }
            Ok(current_heap)
        }
        S::Var(idents, Some(final_ast::AssignRhs::Exp(pure))) => {
            if idents.len() != 1 {
                return Err(TranslationError::Unsupported("multi-LHS var := exp"));
            }
            let v = pure_exp::lower(b, env, sink, pure)?;
            env.insert(idents[0].name.0, v);
            Ok(current_heap)
        }
        S::Var(idents, Some(final_ast::AssignRhs::MethodCall(call))) => {
            let ret_names: Vec<Spur> = idents.iter().map(|i| i.name.0).collect();
            let ret_types: Vec<vmir::Type> = idents.iter().map(|i| lower_type(&i.ty)).collect();
            lower_method_call(b, env, sink, current_heap, call, &ret_names, &ret_types)
        }
        S::Assign(lhss, final_ast::AssignRhs::MethodCall(call)) => {
            let mut ret_names = Vec::with_capacity(lhss.len());
            for lhs in lhss {
                match lhs {
                    final_ast::AssignLhs::Var(name) => ret_names.push(name.0),
                    final_ast::AssignLhs::Field(_, _) => {
                        return Err(TranslationError::Unsupported("field lvalue"));
                    }
                }
            }
            let ret_types: Vec<vmir::Type> = ret_names
                .iter()
                .map(|spur| {
                    env.get(spur)
                        .map(|_| ())
                        .ok_or_else(|| {
                            TranslationError::UnknownIdent(b.interner.resolve(spur).to_string())
                        })
                        // type is recovered from env via name lookup, but env stores Val.
                        // For Phase 2 minimal scope, accept that the LHS variables have been
                        // declared earlier with `var` and assume their types match the
                        // callee's return signature. We use Fresh-typed Int as a placeholder
                        // only when we cannot resolve — better solution lands with proper type
                        // tracking in the env.
                        .map(|_| vmir::Type::Int)
                })
                .collect::<Result<_, _>>()?;
            lower_method_call(b, env, sink, current_heap, call, &ret_names, &ret_types)
        }
        S::Assign(lhss, final_ast::AssignRhs::Exp(pure)) => {
            if lhss.len() != 1 {
                return Err(TranslationError::Unsupported("multi-LHS assign := exp"));
            }
            let name = match &lhss[0] {
                final_ast::AssignLhs::Var(n) => n.0,
                final_ast::AssignLhs::Field(_, _) => {
                    return Err(TranslationError::Unsupported("field lvalue"));
                }
            };
            let v = pure_exp::lower(b, env, sink, pure)?;
            env.insert(name, v);
            Ok(current_heap)
        }
        S::Assign(_, final_ast::AssignRhs::New(_))
        | S::Var(_, Some(final_ast::AssignRhs::New(_))) => {
            Err(TranslationError::Unsupported("new(...)"))
        }
        S::If(_, _, _) => Err(TranslationError::Unsupported("if statement")),
        S::Block(_) => Err(TranslationError::Unsupported("nested block")),
        S::Fold(_) => Err(TranslationError::Unsupported("fold")),
        S::Unfold(_) => Err(TranslationError::Unsupported("unfold")),
        S::Assume(_) => Err(TranslationError::Unsupported("source-level assume")),
        S::Assert(_) => Err(TranslationError::Unsupported("source-level assert")),
        S::Inhale(_) => Err(TranslationError::Unsupported("inhale")),
        S::Exhale(_) => Err(TranslationError::Unsupported("exhale")),
    }
}

fn lower_method_call(
    b: &Builder<'_>,
    env: &mut HashMap<Spur, Val>,
    sink: &mut Sink<MethodCtx>,
    current_heap: HeapVal,
    call: &final_ast::Call<final_ast::MethodBodyExt>,
    ret_names: &[Spur],
    ret_types: &[vmir::Type],
) -> Result<HeapVal, TranslationError> {
    // Lower argument expressions.
    let mut args: Vec<Val> = Vec::with_capacity(call.args.len());
    for a in &call.args {
        args.push(pure_exp::lower(b, env, sink, a)?);
    }

    let mut heap = current_heap;

    // Exhale precondition (if present): call m@requires, sub delta, assert bool.
    if let Some(&req_id) = b.method_requires.get(&call.name.0) {
        let (h_pre, b_pre) = emit_resource_call(sink, req_id, heap, args.clone());
        let h_new = sink.emit_heap(HeapInst::Sub(heap, h_pre));
        sink.emit_ext(InstExt::Assert(b_pre));
        heap = h_new;
    }

    // Allocate fresh return values BEFORE the post-condition inhale.
    let mut ret_vals: Vec<Val> = Vec::with_capacity(ret_names.len());
    for (spur, ty) in ret_names.iter().zip(ret_types.iter()) {
        let v = sink.emit_pure(ty.clone(), PureInst::Fresh);
        env.insert(*spur, v.clone());
        ret_vals.push(v);
    }

    // Inhale postcondition (if present): call m@ensures, add delta, assume bool.
    if let Some(&ens_id) = b.method_ensures.get(&call.name.0) {
        let mut ens_args = args.clone();
        ens_args.extend(ret_vals.iter().cloned());
        let (h_post, b_post) = emit_resource_call(sink, ens_id, heap, ens_args);
        let h_new = sink.emit_heap(HeapInst::Add(heap, h_post));
        sink.emit_ext(InstExt::Assume(b_post));
        heap = h_new;
    }

    Ok(heap)
}

/// Emit a `ResourceCall` instruction that produces both a `HeapVal::Temp` and
/// a `Val::Temp`. Returns the produced pair. Method-body only — resource
/// bodies cannot reach this code path because `Sink<ResourceCtx>` has no
/// `MethodInstExt` to construct.
fn emit_resource_call(
    sink: &mut Sink<MethodCtx>,
    resource: vmir::MemberId,
    ctx_heap: HeapVal,
    args: Vec<Val>,
) -> (HeapVal, Val) {
    let h = sink.next_heap_temp();
    let v = sink.next_val_temp();
    sink.insts.push(Inst {
        pc: PathConds::default(),
        kind: InstKind::Ext(InstExt::ResourceCall(ResourceCall {
            resource,
            ctx_heap,
            args,
        })),
    });
    (h, v)
}
