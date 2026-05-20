use lasso::Spur;
use rusttyc::types::{Arity, Partial, Variant};
use rusttyc::{Constructable, TcErr, TcKey, TypeChecker, VarlessTypeChecker};
use std::collections::HashMap;

use crate::silver::{
    self,
    final_ast::{
        self, BinOp, Call, FuncEnsuresExt, Ident, Literal, MethodBodyExt, MethodEnsuresExt,
        PredicateWithPerm, PureExpKind, ResourceExp, ResourceExpKind, SpatialExp, SpatialExpKind,
        Type, TypedIdent, TypedPureExp, UnOp,
    },
    globals::Globals,
    interner::Interner,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SilverTcType {
    Bool,
    Int,
    Real,
    Ref,
    Numeric, // supertype of Int and Real
    Top,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TcTypeErr(pub String);

impl std::fmt::Display for TcTypeErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Type error: {}", self.0)
    }
}

impl std::error::Error for TcTypeErr {}

impl Variant for SilverTcType {
    type Err = TcTypeErr;

    fn arity(&self) -> Arity {
        Arity::Fixed(0)
    }

    fn top() -> Self {
        SilverTcType::Top
    }

    fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err> {
        use SilverTcType::*;
        let variant = match (lhs.variant, rhs.variant) {
            (Top, x) | (x, Top) => x,
            (Numeric, Numeric) => Numeric,
            (Numeric, x @ (Int | Real)) | (x @ (Int | Real), Numeric) => x,
            (Bool, Bool) => Bool,
            (Ref, Ref) => Ref,
            (Int, Int) => Int,
            (Real, Real) => Real,
            (t1, t2) => {
                return Err(TcTypeErr(format!("Cannot unify {:?} and {:?}", t1, t2)));
            }
        };
        Ok(Partial {
            variant,
            least_arity: 0,
        })
    }
}

impl Constructable for SilverTcType {
    type Type = Type;

    fn construct(
        &self,
        _children: &[Self::Type],
    ) -> Result<Self::Type, <Self as rusttyc::ContextSensitiveVariant>::Err> {
        Ok(match self {
            SilverTcType::Bool => Type::Bool,
            SilverTcType::Int => Type::Int,
            // Unconstrained numerics default to Real
            SilverTcType::Real | SilverTcType::Numeric => Type::Real,
            SilverTcType::Ref => Type::Ref,
            SilverTcType::Top => {
                return Err(TcTypeErr("Cannot construct abstract type".to_string()));
            }
        })
    }
}

fn type_to_tc(ty: &Type) -> SilverTcType {
    match ty {
        Type::Bool => SilverTcType::Bool,
        Type::Int => SilverTcType::Int,
        Type::Real => SilverTcType::Real,
        Type::Ref => SilverTcType::Ref,
        Type::Collection(_) | Type::Domain(..) => SilverTcType::Top,
    }
}

#[derive(Debug, Clone)]
pub enum TypeError {
    TypeMismatch {
        expected: SilverTcType,
        found: SilverTcType,
        context: &'static str,
    },
    UndefinedVariable(String),
    PredicateInPureContext(String),
    PermissionInPureContext,
    WrongArgCount {
        name: String,
        expected: usize,
        found: usize,
    },
    FieldBaseNotRef,
    IllegalOldUsage,
    IllegalLabeledOldUsage,
    IllegalResultUsage,
    Tc(TcErr<SilverTcType>),
    Other(String),
}

impl From<TcErr<SilverTcType>> for TypeError {
    fn from(e: TcErr<SilverTcType>) -> Self {
        TypeError::Tc(e)
    }
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::TypeMismatch {
                expected,
                found,
                context,
            } => {
                write!(
                    f,
                    "Type mismatch in {context}: expected {expected:?}, found {found:?}"
                )
            }
            TypeError::UndefinedVariable(name) => write!(f, "Undefined variable: {name}"),
            TypeError::PredicateInPureContext(name) => {
                write!(f, "Predicate `{name}` used in pure expression context")
            }
            TypeError::PermissionInPureContext => write!(f, "`perm` not allowed here"),
            TypeError::WrongArgCount {
                name,
                expected,
                found,
            } => {
                write!(f, "`{name}` expects {expected} args, got {found}")
            }
            TypeError::FieldBaseNotRef => write!(f, "Field access base must have type Ref"),
            TypeError::IllegalOldUsage => write!(f, "`old` not allowed in this context"),
            TypeError::IllegalLabeledOldUsage => {
                write!(f, "labeled `old` not allowed in this context")
            }
            TypeError::IllegalResultUsage => write!(f, "`result` not allowed in this context"),
            TypeError::Tc(e) => write!(f, "Constraint error: {e:?}"),
            TypeError::Other(msg) => write!(f, "{msg}"),
        }
    }
}

type SilverTc = VarlessTypeChecker<SilverTcType>;
type TypeTable = HashMap<TcKey, Type>;

/// Per-declaration context. Params/return vars/`var` locals all carry concrete
/// declared types, so each top-level expression is self-contained and is checked
/// with its own fresh rusttyc `TypeChecker`. Each AST node's key is stored in its
/// `silver::Exp.ty` (`Infer(key)`), so the build phase reads it back directly —
/// no node→key side table.
struct TcCtx<'g> {
    globals: &'g Globals,
    interner: &'g Interner,
    /// Declared-type environment for params, return vars and `var` locals.
    /// Persists across the declaration's expressions.
    locals: HashMap<Spur, Type>,
    result_ty: Option<Type>,

    // ---- fresh per top-level expression (see `check`) ----
    tc: SilverTc,
    /// `let`-binders local to the current expression: their key in this checker.
    let_bindings: HashMap<Spur, TcKey>,
    /// `None` during the infer phase, `Some` during the build phase. When set,
    /// `impose_*` are no-ops and node types are read from the table.
    table: Option<TypeTable>,
}

impl<'g> TcCtx<'g> {
    fn new(globals: &'g Globals, interner: &'g Interner) -> Self {
        Self {
            globals,
            interner,
            locals: HashMap::new(),
            result_ty: None,
            tc: TypeChecker::new(),
            let_bindings: HashMap::new(),
            table: None,
        }
    }

    fn fresh_key(&mut self) -> TcKey {
        self.tc.new_term_key()
    }

    fn in_build(&self) -> bool {
        self.table.is_some()
    }

    fn impose_bound(&mut self, key: TcKey, ty: SilverTcType) -> Result<(), TypeError> {
        if self.in_build() {
            return Ok(());
        }
        self.tc
            .impose(key.concretizes_explicit(ty))
            .map_err(TypeError::from)
    }

    fn impose_equate(&mut self, k1: TcKey, k2: TcKey) -> Result<(), TypeError> {
        if self.in_build() {
            return Ok(());
        }
        self.tc.impose(k1.equate_with(k2)).map_err(TypeError::from)
    }

    fn impose_meet(&mut self, key: TcKey, l: TcKey, r: TcKey) -> Result<(), TypeError> {
        if self.in_build() {
            return Ok(());
        }
        self.tc
            .impose(key.is_sym_meet_of(l, r))
            .map_err(TypeError::from)
    }

    /// Register a declared local (param/ret/var/quantifier binder).
    fn add_local(&mut self, name: Spur, ty: Type) {
        self.locals.insert(name, ty);
    }

    /// Resolve a node's key to its concrete type during the build phase.
    fn resolved(&self, key: TcKey) -> Result<Type, TypeError> {
        self.table
            .as_ref()
            .and_then(|t| t.get(&key).cloned())
            .ok_or_else(|| TypeError::Other("unresolved type variable".to_string()))
    }

    /// Run `build` over one self-contained top-level expression: an infer pass
    /// (gather constraints, stamp `Infer(key)` into each node), solve, then a
    /// build pass (read each node's key + the solved table). Locals/`result_ty`
    /// persist across both passes.
    fn check<T>(
        &mut self,
        mut build: impl FnMut(&mut TcCtx<'g>) -> Result<T, TypeError>,
    ) -> Result<T, TypeError> {
        // Infer phase.
        self.tc = TypeChecker::new();
        self.let_bindings.clear();
        self.table = None;
        build(self)?;

        // Solve.
        let tc = std::mem::replace(&mut self.tc, TypeChecker::new());
        let table = tc.type_check().map_err(TypeError::from)?;

        // Build phase.
        self.table = Some(table);
        let out = build(self);
        self.table = None;
        out
    }

    /// Check a top-level pure expression. `expected` seeds the root key with the
    /// type demanded by the surrounding position (return type, param, `Ref`
    /// base, bool condition, ...), letting context concretize e.g. `5/2`.
    fn check_pure<Ext: PureExt>(
        &mut self,
        exp: &mut silver::Exp,
        expected: Option<SilverTcType>,
    ) -> Result<TypedPureExp<Ext>, TypeError> {
        self.check(|ctx| {
            let (typed, key) = lower_pure_exp::<Ext>(exp, ctx)?;
            if let Some(t) = expected.clone() {
                ctx.impose_bound(key, t)?;
            }
            Ok(typed)
        })
    }

    /// Check a top-level spatial assertion (and all its independent pure leaves)
    /// under a single fresh checker.
    fn check_spatial<Ext: PureExt>(
        &mut self,
        exp: &mut silver::Exp,
    ) -> Result<SpatialExp<Ext>, TypeError> {
        self.check(|ctx| lower_spatial_exp::<Ext>(exp, ctx))
    }
}

trait PureExt: Sized {
    fn lower_old(label: Option<Spur>, inner: TypedPureExp<Self>) -> Result<Self, TypeError>;
    fn lower_result() -> Result<Self, TypeError>;
    fn lower_perm(resource: ResourceExp<Self>) -> Result<Self, TypeError>;
}

impl PureExt for ! {
    fn lower_old(_label: Option<Spur>, _inner: TypedPureExp<!>) -> Result<!, TypeError> {
        Err(TypeError::IllegalOldUsage)
    }
    fn lower_result() -> Result<!, TypeError> {
        Err(TypeError::IllegalResultUsage)
    }
    fn lower_perm(_resource: ResourceExp<!>) -> Result<!, TypeError> {
        Err(TypeError::PermissionInPureContext)
    }
}

impl PureExt for FuncEnsuresExt {
    fn lower_old(
        label: Option<Spur>,
        inner: TypedPureExp<FuncEnsuresExt>,
    ) -> Result<FuncEnsuresExt, TypeError> {
        match label {
            Some(_) => Err(TypeError::IllegalLabeledOldUsage),
            None => Ok(FuncEnsuresExt::Old(inner)),
        }
    }
    fn lower_result() -> Result<FuncEnsuresExt, TypeError> {
        Ok(FuncEnsuresExt::Result)
    }
    fn lower_perm(_resource: ResourceExp<FuncEnsuresExt>) -> Result<FuncEnsuresExt, TypeError> {
        Err(TypeError::PermissionInPureContext)
    }
}

impl PureExt for MethodEnsuresExt {
    fn lower_old(
        label: Option<Spur>,
        inner: TypedPureExp<MethodEnsuresExt>,
    ) -> Result<MethodEnsuresExt, TypeError> {
        match label {
            Some(_) => Err(TypeError::IllegalLabeledOldUsage),
            None => Ok(MethodEnsuresExt::Old(inner)),
        }
    }
    fn lower_result() -> Result<MethodEnsuresExt, TypeError> {
        Err(TypeError::IllegalResultUsage)
    }
    fn lower_perm(_resource: ResourceExp<MethodEnsuresExt>) -> Result<MethodEnsuresExt, TypeError> {
        Err(TypeError::PermissionInPureContext)
    }
}

impl PureExt for MethodBodyExt {
    fn lower_old(
        label: Option<Spur>,
        inner: TypedPureExp<MethodBodyExt>,
    ) -> Result<MethodBodyExt, TypeError> {
        Ok(MethodBodyExt::Old(label, inner))
    }
    fn lower_result() -> Result<MethodBodyExt, TypeError> {
        Err(TypeError::IllegalResultUsage)
    }
    fn lower_perm(resource: ResourceExp<MethodBodyExt>) -> Result<MethodBodyExt, TypeError> {
        Ok(MethodBodyExt::Perm(resource))
    }
}

fn lower_type(ty: &silver::Type) -> Type {
    match ty {
        silver::Type::Bool => Type::Bool,
        silver::Type::Int => Type::Int,
        silver::Type::Real => Type::Real,
        silver::Type::Ref => Type::Ref,
        silver::Type::Generic(_) | silver::Type::Domain(..) => todo!("domain/generic types"),
    }
}

fn lower_ident(ident: &silver::Ident) -> Ident {
    Ident(ident.id())
}

fn write_perm<Ext: PureExt>() -> TypedPureExp<Ext> {
    TypedPureExp {
        ty: Type::Real,
        exp: Box::new(PureExpKind::Const(Literal::Real(num::BigRational::new(
            num::BigInt::from(1),
            num::BigInt::from(1),
        )))),
    }
}

fn is_numeric(t: &Type) -> bool {
    matches!(t, Type::Int | Type::Real)
}

/// Eager compatibility used to drive diagnostics in the solve pass. Numeric
/// types are mutually compatible here; rusttyc enforces the exact relation
/// (e.g. it still rejects mixing `Int` and `Real` under `+`).
fn compatible(a: &Type, b: &Type) -> bool {
    a == b || (is_numeric(a) && is_numeric(b))
}

/// Eager type guess for an operation over two compatible operands. Real wins
/// over Int; equal non-numeric types pass through. The authoritative type comes
/// from rusttyc on the lowering pass.
fn join(a: &Type, b: &Type) -> Type {
    if a == b { a.clone() } else { Type::Real }
}

/// Both operands must be numeric. Returns the eager joined numeric type.
fn require_numeric(l: &Type, r: &Type, ctx: &'static str) -> Result<Type, TypeError> {
    if is_numeric(l) && is_numeric(r) {
        Ok(join(l, r))
    } else {
        Err(TypeError::TypeMismatch {
            expected: SilverTcType::Numeric,
            found: type_to_tc(if is_numeric(l) { r } else { l }),
            context: ctx,
        })
    }
}

/// Lower each contract clause as its own self-contained spatial expression
/// (fresh checker) and conjoin them.
fn combine_spatial<Ext: PureExt>(
    exps: &mut [silver::Exp],
    ctx: &mut TcCtx,
) -> Result<Option<SpatialExp<Ext>>, TypeError> {
    let mut iter = exps.iter_mut();
    let first = match iter.next() {
        None => return Ok(None),
        Some(e) => ctx.check_spatial(e)?,
    };
    let combined = iter.try_fold(first, |acc, e| {
        let next = ctx.check_spatial(e)?;
        Ok::<_, TypeError>(SpatialExp(Box::new(SpatialExpKind::Conj(acc, next))))
    })?;
    Ok(Some(combined))
}

fn lower_pure_exp<Ext: PureExt>(
    exp: &mut silver::Exp,
    ctx: &mut TcCtx,
) -> Result<(TypedPureExp<Ext>, TcKey), TypeError> {
    // Infer phase: mint a key and stamp it into the node. Build phase: read the
    // key the infer phase stamped.
    let key = match &ctx.table {
        None => {
            let k = ctx.fresh_key();
            exp.ty = silver::InferenceType::Infer(k);
            k
        }
        Some(_) => match exp.ty {
            silver::InferenceType::Infer(k) => k,
            _ => return Err(TypeError::Other("expression was not inferred".to_string())),
        },
    };
    // Each `lower_pure_exp_kind` arm is responsible for constraining `key`.
    let (eager_ty, kind) = lower_pure_exp_kind::<Ext>(exp, ctx, key)?;
    // Build phase: take the rusttyc-resolved type; infer phase: the eager guess
    // (only used to drive constraints/diagnostics).
    let ty = if ctx.in_build() {
        ctx.resolved(key)?
    } else {
        eager_ty
    };
    Ok((
        TypedPureExp {
            ty,
            exp: Box::new(kind),
        },
        key,
    ))
}

fn lower_pure_exp_kind<Ext: PureExt>(
    exp: &mut silver::Exp,
    ctx: &mut TcCtx,
    key: TcKey,
) -> Result<(Type, PureExpKind<Ext>), TypeError> {
    use silver::ExpKind;

    match exp.kind.as_mut() {
        ExpKind::Const(c) => {
            let (ty, kind) = lower_const(c)?;
            ctx.impose_bound(key, type_to_tc(&ty))?;
            Ok((ty, kind))
        }

        ExpKind::Ident(ident) => {
            let spur = ident.id();
            let lowered = PureExpKind::Ident(lower_ident(ident));
            // `let`-binder: equate with the binder's key (same checker).
            if let Some(binder_key) = ctx.let_bindings.get(&spur).cloned() {
                ctx.impose_equate(key, binder_key)?;
                // Infer phase: placeholder — build phase uses ctx.resolved(key)
                return Ok((Type::Bool, lowered));
            }
            // Declared local/param/ret: concrete type, seed the key.
            let ty = ctx.locals.get(&spur).cloned().ok_or_else(|| {
                TypeError::UndefinedVariable(ctx.interner.resolve(&spur).to_string())
            })?;
            ctx.impose_bound(key, type_to_tc(&ty))?;
            Ok((ty, lowered))
        }

        ExpKind::Result => {
            let ty = ctx.result_ty.clone().ok_or(TypeError::IllegalResultUsage)?;
            ctx.impose_bound(key, type_to_tc(&ty))?;
            let ext = Ext::lower_result()?;
            Ok((ty, PureExpKind::Ext(ext)))
        }

        ExpKind::Old(label, inner) => {
            let (inner_exp, inner_key) = lower_pure_exp::<Ext>(inner, ctx)?;
            ctx.impose_equate(key, inner_key)?;
            let ty = inner_exp.ty.clone();
            let label_spur = label.as_ref().map(|l| l.id());
            let ext = Ext::lower_old(label_spur, inner_exp)?;
            Ok((ty, PureExpKind::Ext(ext)))
        }

        ExpKind::Ascribe(inner, ascribed_ty) => {
            let target_ty = lower_type(ascribed_ty);
            let (inner_exp, inner_key) = lower_pure_exp::<Ext>(inner, ctx)?;
            ctx.impose_bound(inner_key, type_to_tc(&target_ty))?;
            ctx.impose_bound(key, type_to_tc(&target_ty))?;
            Ok((
                target_ty.clone(),
                PureExpKind::Ascribe(inner_exp, target_ty),
            ))
        }

        ExpKind::UnOp(op, inner) => lower_unop::<Ext>(op, inner, ctx, key),

        ExpKind::BinOp(op, left, right) => lower_binop::<Ext>(op, left, right, ctx, key),

        ExpKind::Ternary(cond, then, else_) => {
            let (cond_exp, cond_key) = lower_pure_exp::<Ext>(cond, ctx)?;
            ctx.impose_bound(cond_key, SilverTcType::Bool)?;
            if cond_exp.ty != Type::Bool {
                return Err(TypeError::TypeMismatch {
                    expected: SilverTcType::Bool,
                    found: type_to_tc(&cond_exp.ty),
                    context: "ternary condition",
                });
            }
            let (then_exp, then_key) = lower_pure_exp::<Ext>(then, ctx)?;
            let (else_exp, else_key) = lower_pure_exp::<Ext>(else_, ctx)?;
            if !compatible(&then_exp.ty, &else_exp.ty) {
                return Err(TypeError::TypeMismatch {
                    expected: type_to_tc(&then_exp.ty),
                    found: type_to_tc(&else_exp.ty),
                    context: "ternary branches",
                });
            }
            let ty = join(&then_exp.ty, &else_exp.ty);
            ctx.impose_meet(key, then_key, else_key)?;
            Ok((
                ty,
                PureExpKind::Ternary {
                    if_: cond_exp,
                    then: then_exp,
                    else_: else_exp,
                },
            ))
        }

        ExpKind::LetIn(binder, value, body) => {
            let (value_exp, value_key) = lower_pure_exp::<Ext>(value, ctx)?;
            let binder_spur = binder.0.id();
            let prev = ctx.let_bindings.insert(binder_spur, value_key);
            let (body_exp, body_key) = lower_pure_exp::<Ext>(body, ctx)?;
            match prev {
                Some(p) => {
                    ctx.let_bindings.insert(binder_spur, p);
                }
                None => {
                    ctx.let_bindings.remove(&binder_spur);
                }
            }
            ctx.impose_equate(key, body_key)?;
            let ty = body_exp.ty.clone();
            Ok((
                ty,
                PureExpKind::LetIn {
                    binder: Ident(binder_spur),
                    value: value_exp,
                    exp: body_exp,
                },
            ))
        }

        ExpKind::Call(call) => lower_call::<Ext>(call, ctx, key),

        ExpKind::Field(base, field_name) => lower_field::<Ext>(base, field_name, ctx, key),

        ExpKind::HeapUpdate(silver::HeapUpdateOp::Unfold, acc_exp, body) => {
            let resource = lower_resource_exp::<Ext>(&mut acc_exp.loc, ctx)?;
            let (perm_exp, _) = lower_pure_exp::<Ext>(&mut acc_exp.perm, ctx)?;
            let pred_call = match *resource.0 {
                ResourceExpKind::PredicateCall(call) => call,
                ResourceExpKind::Field(..) => {
                    return Err(TypeError::Other("cannot unfold a field".to_string()));
                }
            };
            let (body_exp, body_key) = lower_pure_exp::<Ext>(body, ctx)?;
            ctx.impose_equate(key, body_key)?;
            let ty = body_exp.ty.clone();
            Ok((
                ty,
                PureExpKind::Unfolding(
                    PredicateWithPerm {
                        pred_call,
                        perm: perm_exp,
                    },
                    body_exp,
                ),
            ))
        }

        ExpKind::AdtDestructor(base, field) => {
            let (base_exp, _) = lower_pure_exp::<Ext>(base, ctx)?;
            ctx.impose_bound(key, SilverTcType::Bool)?;
            Ok((
                Type::Bool,
                PureExpKind::AdtDestructor(base_exp, Ident(field.id())),
            ))
        }

        ExpKind::AdtDiscriminator(base, variant) => {
            let (base_exp, _) = lower_pure_exp::<Ext>(base, ctx)?;
            ctx.impose_bound(key, SilverTcType::Bool)?;
            Ok((
                Type::Bool,
                PureExpKind::AdtDiscriminator(base_exp, Ident(variant.id())),
            ))
        }

        _ => Err(TypeError::Other(format!(
            "unsupported pure expression: {:?}",
            exp.kind
        ))),
    }
}

fn lower_const<Ext>(c: &silver::ConstKind) -> Result<(Type, PureExpKind<Ext>), TypeError> {
    let (ty, lit) = match c {
        silver::ConstKind::Bool(b) => (Type::Bool, Literal::Bool(*b)),
        silver::ConstKind::Int(i) => (Type::Int, Literal::Int(i.clone())),
        silver::ConstKind::Real(r) => (Type::Real, Literal::Real(r.clone())),
        silver::ConstKind::Null => (Type::Ref, Literal::Null),
        silver::ConstKind::Wildcard => (Type::Real, Literal::Wildcard),
        silver::ConstKind::Epsilon => (
            Type::Real,
            Literal::Real(num::BigRational::new(
                num::BigInt::from(0),
                num::BigInt::from(1),
            )),
        ),
    };
    Ok((ty, PureExpKind::Const(lit)))
}

fn lower_call<Ext: PureExt>(
    call: &mut silver::Call<silver::ExpCallKind>,
    ctx: &mut TcCtx,
    key: TcKey,
) -> Result<(Type, PureExpKind<Ext>), TypeError> {
    use silver::ExpCallKind;
    let call_name = call.name.id();
    let sym = ctx.globals.resolve(call_name).ok_or_else(|| {
        TypeError::UndefinedVariable(ctx.interner.resolve(&call_name).to_string())
    })?;

    match call.kind.as_ref().expect("call kind must be resolved") {
        ExpCallKind::Predicate => {
            let name = ctx.interner.resolve(&call_name).to_string();
            Err(TypeError::PredicateInPureContext(name))
        }
        ExpCallKind::Function | ExpCallKind::AdtConstructor => {
            let sig = sym.as_function().ok_or_else(|| {
                TypeError::Other(format!(
                    "{} is not a function",
                    ctx.interner.resolve(&call_name)
                ))
            })?;
            if sig.params.len() != call.args.len() {
                return Err(TypeError::WrongArgCount {
                    name: ctx.interner.resolve(&call_name).to_string(),
                    expected: sig.params.len(),
                    found: call.args.len(),
                });
            }
            let ret_ty = lower_type(&sig.ret);
            let expected_params: Vec<Type> = sig.params.iter().map(lower_type).collect();
            let mut lowered_args = Vec::with_capacity(call.args.len());
            for (arg, expected) in call.args.iter_mut().zip(expected_params.iter()) {
                let (arg_exp, arg_key) = lower_pure_exp::<Ext>(arg, ctx)?;
                if !compatible(&arg_exp.ty, expected) {
                    return Err(TypeError::TypeMismatch {
                        expected: type_to_tc(expected),
                        found: type_to_tc(&arg_exp.ty),
                        context: "function argument",
                    });
                }
                ctx.impose_bound(arg_key, type_to_tc(expected))?;
                lowered_args.push(arg_exp);
            }
            ctx.impose_bound(key, type_to_tc(&ret_ty))?;
            Ok((
                ret_ty,
                PureExpKind::FunctionCall(Call {
                    name: Ident(call_name),
                    args: lowered_args,
                }),
            ))
        }
        ExpCallKind::Macro => Err(TypeError::Other(
            "macro in expression (should have been inlined)".to_string(),
        )),
    }
}

fn lower_field<Ext: PureExt>(
    base: &mut silver::Exp,
    field_name: &silver::Ident,
    ctx: &mut TcCtx,
    key: TcKey,
) -> Result<(Type, PureExpKind<Ext>), TypeError> {
    let field_id = field_name.id();
    let sym = ctx.globals.resolve(field_id).ok_or_else(|| {
        TypeError::Other(format!(
            "unknown field: {}",
            ctx.interner.resolve(&field_id)
        ))
    })?;
    let field_ty = sym.as_field().ok_or_else(|| {
        TypeError::Other(format!(
            "{} is not a field",
            ctx.interner.resolve(&field_id)
        ))
    })?;
    let (base_exp, base_key) = lower_pure_exp::<Ext>(base, ctx)?;
    if base_exp.ty != Type::Ref {
        return Err(TypeError::FieldBaseNotRef);
    }
    ctx.impose_bound(base_key, SilverTcType::Ref)?;
    let ret_ty = lower_type(field_ty);
    ctx.impose_bound(key, type_to_tc(&ret_ty))?;
    Ok((
        ret_ty,
        PureExpKind::FunctionCall(Call {
            name: Ident(field_id),
            args: vec![base_exp],
        }),
    ))
}

fn lower_unop<Ext: PureExt>(
    op: &silver::UnOp,
    inner: &mut silver::Exp,
    ctx: &mut TcCtx,
    key: TcKey,
) -> Result<(Type, PureExpKind<Ext>), TypeError> {
    match op {
        silver::UnOp::Not => {
            let (inner_exp, inner_key) = lower_pure_exp::<Ext>(inner, ctx)?;
            if inner_exp.ty != Type::Bool {
                return Err(TypeError::TypeMismatch {
                    expected: SilverTcType::Bool,
                    found: type_to_tc(&inner_exp.ty),
                    context: "not operand",
                });
            }
            ctx.impose_bound(inner_key, SilverTcType::Bool)?;
            ctx.impose_bound(key, SilverTcType::Bool)?;
            Ok((Type::Bool, PureExpKind::Unary(UnOp::Not, inner_exp)))
        }
        silver::UnOp::Neg => {
            let (inner_exp, inner_key) = lower_pure_exp::<Ext>(inner, ctx)?;
            let ty = match inner_exp.ty {
                Type::Int => Type::Int,
                Type::Real => Type::Real,
                ref t => {
                    return Err(TypeError::TypeMismatch {
                        expected: SilverTcType::Numeric,
                        found: type_to_tc(t),
                        context: "negation operand",
                    });
                }
            };
            ctx.impose_bound(inner_key, SilverTcType::Numeric)?;
            ctx.impose_equate(key, inner_key)?;
            Ok((ty, PureExpKind::Unary(UnOp::Neg, inner_exp)))
        }
        silver::UnOp::Perm => {
            let resource = lower_resource_exp::<Ext>(inner, ctx)?;
            let ext = Ext::lower_perm(resource)?;
            ctx.impose_bound(key, SilverTcType::Real)?;
            Ok((Type::Real, PureExpKind::Ext(ext)))
        }
    }
}

fn lower_binop<Ext: PureExt>(
    op: &silver::BinOp,
    left: &mut silver::Exp,
    right: &mut silver::Exp,
    ctx: &mut TcCtx,
    key: TcKey,
) -> Result<(Type, PureExpKind<Ext>), TypeError> {
    use silver::BinOp as SBinOp;

    let (le, lk) = lower_pure_exp::<Ext>(left, ctx)?;
    let (re, rk) = lower_pure_exp::<Ext>(right, ctx)?;

    // Each arm fully constrains `key`; the eager `result_ty` is only a guess used
    // for diagnostics on the solve pass — the stored type comes from rusttyc.
    let (result_ty, fa_op) = match op {
        SBinOp::And | SBinOp::Or | SBinOp::Implies | SBinOp::Iff => {
            let name = bin_op_name(op);
            check_bool(&le.ty, &re.ty, name)?;
            ctx.impose_bound(lk, SilverTcType::Bool)?;
            ctx.impose_bound(rk, SilverTcType::Bool)?;
            ctx.impose_bound(key, SilverTcType::Bool)?;
            (Type::Bool, lower_bin_op(op))
        }
        SBinOp::Eq | SBinOp::Neq => {
            if !compatible(&le.ty, &re.ty) {
                return Err(TypeError::TypeMismatch {
                    expected: type_to_tc(&le.ty),
                    found: type_to_tc(&re.ty),
                    context: bin_op_name(op),
                });
            }
            ctx.impose_equate(lk, rk)?;
            ctx.impose_bound(key, SilverTcType::Bool)?;
            (Type::Bool, lower_bin_op(op))
        }
        SBinOp::Lt | SBinOp::Le | SBinOp::Gt | SBinOp::Ge => {
            require_numeric(&le.ty, &re.ty, bin_op_name(op))?;
            ctx.impose_bound(lk, SilverTcType::Numeric)?;
            ctx.impose_bound(rk, SilverTcType::Numeric)?;
            ctx.impose_equate(lk, rk)?;
            ctx.impose_bound(key, SilverTcType::Bool)?;
            (Type::Bool, lower_bin_op(op))
        }
        SBinOp::Plus | SBinOp::Minus | SBinOp::Mult | SBinOp::Mod => {
            let ty = require_numeric(&le.ty, &re.ty, bin_op_name(op))?;
            ctx.impose_bound(lk, SilverTcType::Numeric)?;
            ctx.impose_bound(rk, SilverTcType::Numeric)?;
            // result == meet(lhs, rhs): Int·Int = Int, Real·Real = Real.
            ctx.impose_meet(key, lk, rk)?;
            (ty, lower_bin_op(op))
        }
        SBinOp::Div => {
            // Real/perm division: result is abstract `Numeric`. Context may pin
            // it to Int or Real; if nothing does, it defaults to Real (via
            // `Constructable::construct`). Operands need not share a type.
            require_numeric(&le.ty, &re.ty, "/")?;
            ctx.impose_bound(lk, SilverTcType::Numeric)?;
            ctx.impose_bound(rk, SilverTcType::Numeric)?;
            ctx.impose_bound(key, SilverTcType::Numeric)?;
            (Type::Real, BinOp::Div)
        }
        _ => {
            return Err(TypeError::Other(format!(
                "unsupported binary operator: {op:?}"
            )));
        }
    };

    Ok((result_ty, PureExpKind::Binary(fa_op, le, re)))
}

fn bin_op_name(op: &silver::BinOp) -> &'static str {
    use silver::BinOp as S;
    match op {
        S::And => "&&",
        S::Or => "||",
        S::Implies => "==>",
        S::Iff => "<==>",
        S::Eq => "==",
        S::Neq => "!=",
        S::Lt => "<",
        S::Le => "<=",
        S::Gt => ">",
        S::Ge => ">=",
        S::Plus => "+",
        S::Minus => "-",
        S::Mult => "*",
        S::Div => "/",
        S::Mod => "%",
        _ => "<binop>",
    }
}

fn lower_bin_op(op: &silver::BinOp) -> BinOp {
    use silver::BinOp as S;
    match op {
        S::And => BinOp::And,
        S::Or => BinOp::Or,
        S::Implies => BinOp::Implies,
        S::Iff => BinOp::Iff,
        S::Eq => BinOp::Eq,
        S::Neq => BinOp::Neq,
        S::Lt => BinOp::Lt,
        S::Le => BinOp::Le,
        S::Gt => BinOp::Gt,
        S::Ge => BinOp::Ge,
        S::Plus => BinOp::Plus,
        S::Minus => BinOp::Minus,
        S::Mult => BinOp::Mult,
        S::Div => BinOp::Div,
        S::Mod => BinOp::Mod,
        other => panic!("unsupported binary operator: {other:?}"),
    }
}

fn check_bool(l: &Type, r: &Type, op: &'static str) -> Result<(), TypeError> {
    if *l != Type::Bool {
        return Err(TypeError::TypeMismatch {
            expected: SilverTcType::Bool,
            found: type_to_tc(l),
            context: op,
        });
    }
    if *r != Type::Bool {
        return Err(TypeError::TypeMismatch {
            expected: SilverTcType::Bool,
            found: type_to_tc(r),
            context: op,
        });
    }
    Ok(())
}

// ==========================================
// 8. lower_resource_exp
// ==========================================

fn lower_resource_exp<Ext: PureExt>(
    exp: &mut silver::Exp,
    ctx: &mut TcCtx,
) -> Result<ResourceExp<Ext>, TypeError> {
    match exp.kind.as_mut() {
        silver::ExpKind::Field(base, field_name) => {
            let field_id = field_name.id();
            let (base_exp, base_key) = lower_pure_exp::<Ext>(base, ctx)?;
            if base_exp.ty != Type::Ref {
                return Err(TypeError::FieldBaseNotRef);
            }
            ctx.impose_bound(base_key, SilverTcType::Ref)?;
            Ok(ResourceExp(Box::new(ResourceExpKind::Field(
                base_exp,
                Ident(field_id),
            ))))
        }
        silver::ExpKind::Call(call) => {
            let kind = call.kind.clone().expect("call kind resolved");
            match kind {
                silver::ExpCallKind::Predicate => lower_predicate_resource::<Ext>(call, ctx),
                _ => Err(TypeError::Other(
                    "resource position requires field or predicate call".to_string(),
                )),
            }
        }
        _ => Err(TypeError::Other(
            "resource position requires field or predicate call".to_string(),
        )),
    }
}

/// Lower a predicate call appearing in a resource position to a typed
/// `ResourceExpKind::PredicateCall`.
fn lower_predicate_resource<Ext: PureExt>(
    call: &mut silver::Call<silver::ExpCallKind>,
    ctx: &mut TcCtx,
) -> Result<ResourceExp<Ext>, TypeError> {
    let call_name = call.name.id();
    let sym = ctx.globals.resolve(call_name).ok_or_else(|| {
        TypeError::UndefinedVariable(ctx.interner.resolve(&call_name).to_string())
    })?;
    let sig = sym.as_predicate().ok_or_else(|| {
        TypeError::Other(format!(
            "{} is not a predicate",
            ctx.interner.resolve(&call_name)
        ))
    })?;
    if sig.params.len() != call.args.len() {
        return Err(TypeError::WrongArgCount {
            name: ctx.interner.resolve(&call_name).to_string(),
            expected: sig.params.len(),
            found: call.args.len(),
        });
    }
    let expected_params: Vec<Type> = sig.params.iter().map(lower_type).collect();
    let mut lowered_args = Vec::with_capacity(call.args.len());
    for (arg, expected) in call.args.iter_mut().zip(expected_params.iter()) {
        let (arg_exp, arg_key) = lower_pure_exp::<Ext>(arg, ctx)?;
        if !compatible(&arg_exp.ty, expected) {
            return Err(TypeError::TypeMismatch {
                expected: type_to_tc(expected),
                found: type_to_tc(&arg_exp.ty),
                context: "predicate argument",
            });
        }
        ctx.impose_bound(arg_key, type_to_tc(expected))?;
        lowered_args.push(arg_exp);
    }
    Ok(ResourceExp(Box::new(ResourceExpKind::PredicateCall(
        Call {
            name: Ident(call_name),
            args: lowered_args,
        },
    ))))
}

// ==========================================
// 9. lower_spatial_exp
// ==========================================

fn lower_spatial_exp<Ext: PureExt>(
    exp: &mut silver::Exp,
    ctx: &mut TcCtx,
) -> Result<SpatialExp<Ext>, TypeError> {
    use silver::ExpKind;

    // Bare predicate call: desugar to acc(pred(args), write). Checked before the
    // big match so we can take `call` mutably without re-borrowing `exp`.
    if let ExpKind::Call(call) = exp.kind.as_mut() {
        if matches!(call.kind, Some(silver::ExpCallKind::Predicate)) {
            let resource = lower_predicate_resource::<Ext>(call, ctx)?;
            return Ok(SpatialExp(Box::new(SpatialExpKind::Acc(
                resource,
                write_perm(),
            ))));
        }
    }

    match exp.kind.as_mut() {
        ExpKind::Acc(acc_exp) => {
            let resource = lower_resource_exp::<Ext>(&mut acc_exp.loc, ctx)?;
            let (perm_exp, perm_key) = lower_pure_exp::<Ext>(&mut acc_exp.perm, ctx)?;
            ctx.impose_bound(perm_key, SilverTcType::Numeric)?;
            Ok(SpatialExp(Box::new(SpatialExpKind::Acc(
                resource, perm_exp,
            ))))
        }

        ExpKind::BinOp(silver::BinOp::And, l, r) => {
            let ls = lower_spatial_exp::<Ext>(l, ctx)?;
            let rs = lower_spatial_exp::<Ext>(r, ctx)?;
            Ok(SpatialExp(Box::new(SpatialExpKind::Conj(ls, rs))))
        }

        ExpKind::BinOp(silver::BinOp::Implies, l, r) => {
            let (cond_exp, cond_key) = lower_pure_exp::<Ext>(l, ctx)?;
            ctx.impose_bound(cond_key, SilverTcType::Bool)?;
            if cond_exp.ty != Type::Bool {
                return Err(TypeError::TypeMismatch {
                    expected: SilverTcType::Bool,
                    found: type_to_tc(&cond_exp.ty),
                    context: "spatial implication condition",
                });
            }
            let rs = lower_spatial_exp::<Ext>(r, ctx)?;
            Ok(SpatialExp(Box::new(SpatialExpKind::Implies(cond_exp, rs))))
        }

        ExpKind::BinOp(silver::BinOp::InhaleExhale, l, r) => {
            let ls = lower_spatial_exp::<Ext>(l, ctx)?;
            let rs = lower_spatial_exp::<Ext>(r, ctx)?;
            Ok(SpatialExp(Box::new(SpatialExpKind::Conj(ls, rs))))
        }

        ExpKind::Ternary(cond, then, else_) => {
            let (cond_exp, cond_key) = lower_pure_exp::<Ext>(cond, ctx)?;
            ctx.impose_bound(cond_key, SilverTcType::Bool)?;
            if cond_exp.ty != Type::Bool {
                return Err(TypeError::TypeMismatch {
                    expected: SilverTcType::Bool,
                    found: type_to_tc(&cond_exp.ty),
                    context: "spatial ternary condition",
                });
            }
            let then_s = lower_spatial_exp::<Ext>(then, ctx)?;
            let else_s = lower_spatial_exp::<Ext>(else_, ctx)?;
            Ok(SpatialExp(Box::new(SpatialExpKind::Ternary {
                if_: cond_exp,
                then: then_s,
                else_: else_s,
            })))
        }

        _ => {
            let (pure_exp, pure_key) = lower_pure_exp::<Ext>(exp, ctx)?;
            ctx.impose_bound(pure_key, SilverTcType::Bool)?;
            if pure_exp.ty != Type::Bool {
                return Err(TypeError::TypeMismatch {
                    expected: SilverTcType::Bool,
                    found: type_to_tc(&pure_exp.ty),
                    context: "spatial expression (expected bool or resource)",
                });
            }
            Ok(SpatialExp(Box::new(SpatialExpKind::Pure(pure_exp))))
        }
    }
}

// ==========================================
// 10. Statement lowering
// ==========================================

fn lower_statement(
    stmt: &mut silver::Statement,
    ctx: &mut TcCtx,
) -> Result<final_ast::Statement, TypeError> {
    use silver::Statement as S;
    match stmt {
        S::Assume(e) => Ok(final_ast::Statement::Assume(ctx.check_spatial(e)?)),
        S::Assert(e) => Ok(final_ast::Statement::Assert(ctx.check_spatial(e)?)),
        S::Inhale(e) => Ok(final_ast::Statement::Inhale(ctx.check_spatial(e)?)),
        S::Exhale(e) => Ok(final_ast::Statement::Exhale(ctx.check_spatial(e)?)),

        S::Fold(acc) => Ok(final_ast::Statement::Fold(
            ctx.check(|c| lower_acc_to_pred_with_perm(acc, c))?,
        )),
        S::Unfold(acc) => Ok(final_ast::Statement::Unfold(
            ctx.check(|c| lower_acc_to_pred_with_perm(acc, c))?,
        )),

        S::Var(decls, init) => {
            let mut typed_decls = Vec::with_capacity(decls.len());
            for d in decls.iter() {
                let ty = lower_type(&d.ty);
                ctx.add_local(d.idn.0.id(), ty.clone());
                typed_decls.push(TypedIdent {
                    name: Ident(d.idn.0.id()),
                    ty,
                });
            }
            // A single declared type provides context for the initialiser.
            let seed = if decls.len() == 1 {
                Some(type_to_tc(&lower_type(&decls[0].ty)))
            } else {
                None
            };
            let lowered_rhs = init
                .as_mut()
                .map(|rhs| lower_assign_rhs(rhs, ctx, seed))
                .transpose()?;
            Ok(final_ast::Statement::Var(typed_decls, lowered_rhs))
        }

        S::Assign(lhs_list, rhs) => {
            let seed = if lhs_list.len() == 1 {
                assign_lhs_type(&lhs_list[0], ctx).map(|t| type_to_tc(&t))
            } else {
                None
            };
            let lowered_rhs = lower_assign_rhs(rhs, ctx, seed)?;
            let lowered_lhs = lhs_list
                .iter_mut()
                .map(|lhs| lower_assign_lhs(lhs, ctx))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(final_ast::Statement::Assign(lowered_lhs, lowered_rhs))
        }

        S::Block(block) => {
            let stmts = lower_stmt_block(&mut block.0, ctx)?;
            Ok(final_ast::Statement::Block(final_ast::StmtBlock(stmts)))
        }

        S::If(..) | S::While(..) | S::Goto(..) | S::Label(..) | S::Refute(..) => Err(
            TypeError::Other("statement not yet supported in initial scope".to_string()),
        ),
    }
}

/// Concrete type of an assignment target, used to seed the rhs checker.
fn assign_lhs_type(lhs: &silver::AssignLhs, ctx: &TcCtx) -> Option<Type> {
    match lhs {
        silver::AssignLhs::Ident(ident) => ctx.locals.get(&ident.id()).cloned(),
        silver::AssignLhs::Field(_, field) => ctx
            .globals
            .resolve(field.id())
            .and_then(|s| s.as_field().map(lower_type)),
    }
}

fn lower_acc_to_pred_with_perm<Ext: PureExt>(
    acc: &mut silver::AccExp,
    ctx: &mut TcCtx,
) -> Result<PredicateWithPerm<Ext>, TypeError> {
    let resource = lower_resource_exp::<Ext>(&mut acc.loc, ctx)?;
    let (perm_exp, perm_key) = lower_pure_exp::<Ext>(&mut acc.perm, ctx)?;
    ctx.impose_bound(perm_key, SilverTcType::Numeric)?;
    let pred_call = match *resource.0 {
        ResourceExpKind::PredicateCall(call) => call,
        ResourceExpKind::Field(..) => {
            return Err(TypeError::Other(
                "fold/unfold requires a predicate, not a field".to_string(),
            ));
        }
    };
    Ok(PredicateWithPerm {
        pred_call,
        perm: perm_exp,
    })
}

fn lower_assign_lhs(
    lhs: &mut silver::AssignLhs,
    ctx: &mut TcCtx,
) -> Result<final_ast::AssignLhs, TypeError> {
    match lhs {
        silver::AssignLhs::Ident(ident) => Ok(final_ast::AssignLhs::Var(Ident(ident.id()))),
        silver::AssignLhs::Field(base, field) => {
            let field_id = field.id();
            let base_exp = ctx.check_pure::<MethodBodyExt>(base, Some(SilverTcType::Ref))?;
            if base_exp.ty != Type::Ref {
                return Err(TypeError::FieldBaseNotRef);
            }
            Ok(final_ast::AssignLhs::Field(base_exp, Ident(field_id)))
        }
    }
}

fn lower_assign_rhs(
    rhs: &mut silver::AssignRhs,
    ctx: &mut TcCtx,
    seed: Option<SilverTcType>,
) -> Result<final_ast::AssignRhs, TypeError> {
    match rhs {
        silver::AssignRhs::Exp(e) => {
            let exp = ctx.check_pure::<MethodBodyExt>(e, seed)?;
            Ok(final_ast::AssignRhs::Exp(exp))
        }
        silver::AssignRhs::Call(call) => {
            let call_name = call.name.id();
            let mut lowered_args = Vec::with_capacity(call.args.len());
            for arg in call.args.iter_mut() {
                lowered_args.push(ctx.check_pure::<MethodBodyExt>(arg, None)?);
            }
            Ok(final_ast::AssignRhs::MethodCall(Call {
                name: Ident(call_name),
                args: lowered_args,
            }))
        }
        silver::AssignRhs::New(fields) => {
            let star_or_fields = match fields {
                silver::StarOrNames::Star => final_ast::StarOrFields::Star,
                silver::StarOrNames::Names(names) => {
                    final_ast::StarOrFields::Fields(names.iter().map(|n| Ident(n.id())).collect())
                }
            };
            Ok(final_ast::AssignRhs::New(star_or_fields))
        }
    }
}

fn lower_stmt_block(
    stmts: &mut [silver::Statement],
    ctx: &mut TcCtx,
) -> Result<Vec<final_ast::Statement>, TypeError> {
    stmts.iter_mut().map(|s| lower_statement(s, ctx)).collect()
}

// ==========================================
// 11. Declaration-level functions
// ==========================================

fn typecheck_field(field: &silver::Field) -> final_ast::Declaration {
    final_ast::Declaration::Field(final_ast::Field(TypedIdent {
        name: Ident(field.0.idn.0.id()),
        ty: lower_type(&field.0.ty),
    }))
}

fn collect_params(args: &[silver::ArgOrType]) -> Vec<TypedIdent> {
    args.iter()
        .filter_map(|p| {
            p.idn().map(|idn| TypedIdent {
                name: Ident(idn.0.id()),
                ty: lower_type(p.ty()),
            })
        })
        .collect()
}

fn add_arg_locals(ctx: &mut TcCtx, args: &[silver::ArgOrType]) {
    for arg in args {
        if let silver::ArgOrType::Arg(decl) = arg {
            ctx.add_local(decl.idn.0.id(), lower_type(&decl.ty));
        }
    }
}

fn typecheck_predicate(
    pred: &mut silver::Predicate,
    globals: &Globals,
    interner: &Interner,
) -> Result<final_ast::Declaration, TypeError> {
    let name = Ident(pred.signature.name.0.id());
    let params = collect_params(&pred.signature.args);

    let mut ctx = TcCtx::new(globals, interner);
    add_arg_locals(&mut ctx, &pred.signature.args);

    let body = pred
        .body
        .as_mut()
        .map(|b| ctx.check_spatial::<!>(&mut b.0))
        .transpose()?;

    Ok(final_ast::Declaration::Predicate(final_ast::Predicate {
        name,
        params,
        body,
    }))
}

fn typecheck_function(
    func: &mut silver::Function,
    globals: &Globals,
    interner: &Interner,
) -> Result<final_ast::Declaration, TypeError> {
    let name = Ident(func.signature.name.0.id());
    let params = collect_params(&func.signature.args);
    let ret_ty = func
        .signature
        .ret
        .first()
        .map(|r| lower_type(r.ty()))
        .unwrap_or(Type::Bool);

    let mut ctx = TcCtx::new(globals, interner);
    add_arg_locals(&mut ctx, &func.signature.args);

    let requires = combine_spatial::<!>(&mut func.contract.precondition, &mut ctx)?;

    // Return type provides context (forces e.g. `5/2` to the declared type).
    let body = func
        .body
        .as_mut()
        .map(|b| {
            let exp = ctx.check_pure::<!>(&mut b.0, Some(type_to_tc(&ret_ty)))?;
            if !compatible(&exp.ty, &ret_ty) {
                return Err(TypeError::TypeMismatch {
                    expected: type_to_tc(&ret_ty),
                    found: type_to_tc(&exp.ty),
                    context: "function body return type",
                });
            }
            Ok(exp)
        })
        .transpose()?;

    ctx.result_ty = Some(ret_ty.clone());
    let ensures = {
        let mut iter = func.contract.postcondition.iter_mut();
        match iter.next() {
            None => None,
            Some(e) => {
                let first = ctx.check_pure::<FuncEnsuresExt>(e, Some(SilverTcType::Bool))?;
                let combined = iter.try_fold(first, |acc, e| {
                    let next = ctx.check_pure::<FuncEnsuresExt>(e, Some(SilverTcType::Bool))?;
                    Ok::<_, TypeError>(TypedPureExp {
                        ty: Type::Bool,
                        exp: Box::new(PureExpKind::Binary(BinOp::And, acc, next)),
                    })
                })?;
                Some(combined)
            }
        }
    };

    Ok(final_ast::Declaration::Function(final_ast::Function {
        name,
        params,
        ret: ret_ty,
        requires,
        ensures,
        body,
    }))
}

fn typecheck_method(
    method: &mut silver::Method,
    globals: &Globals,
    interner: &Interner,
) -> Result<final_ast::Declaration, TypeError> {
    let name = Ident(method.signature.name.0.id());
    let params = collect_params(&method.signature.args);
    let rets = collect_params(&method.signature.ret);

    let mut ctx = TcCtx::new(globals, interner);
    add_arg_locals(&mut ctx, &method.signature.args);

    let requires = combine_spatial::<!>(&mut method.contract.precondition, &mut ctx)?;

    add_arg_locals(&mut ctx, &method.signature.ret);

    let ensures =
        combine_spatial::<MethodEnsuresExt>(&mut method.contract.postcondition, &mut ctx)?;

    let body = method
        .body
        .as_mut()
        .map(|b| lower_stmt_block(&mut b.0, &mut ctx))
        .transpose()?
        .map(final_ast::StmtBlock);

    Ok(final_ast::Declaration::Method(final_ast::Method {
        name,
        params,
        rets,
        requires,
        ensures,
        body,
    }))
}

// ==========================================
// 12. Entry point
// ==========================================

pub fn typecheck_program(
    program: &mut silver::Program,
    interner: &Interner,
    globals: &Globals,
) -> Result<final_ast::Program, Vec<TypeError>> {
    let mut decls = Vec::new();
    let mut errors = Vec::new();

    for decl in &mut program.0 {
        let result = match decl {
            silver::Declaration::Field(field) => Ok(Some(typecheck_field(field))),
            silver::Declaration::Predicate(pred) => {
                typecheck_predicate(pred, globals, interner).map(Some)
            }
            silver::Declaration::Function(func) => {
                typecheck_function(func, globals, interner).map(Some)
            }
            silver::Declaration::Method(method) => {
                typecheck_method(method, globals, interner).map(Some)
            }
            _ => Ok(None),
        };

        match result {
            Ok(Some(d)) => decls.push(d),
            Ok(None) => {}
            Err(e) => errors.push(e),
        }
    }

    if errors.is_empty() {
        Ok(final_ast::Program(decls))
    } else {
        Err(errors)
    }
}

// ==========================================
// 13. Tests
// ==========================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::silver::{
        call_resolver::resolve_call_kinds, globals::GlobalsCollector, interner::IdentCollector,
        r#macro::inline_macros, silver_parser, walk::AstWalkable,
    };

    fn run_pipeline(input: &str) -> Result<final_ast::Program, Vec<TypeError>> {
        let mut program = silver_parser::sil_program(input).expect("parse failed");
        let mut ident_collector = IdentCollector::default();
        program.walk_mut(&mut ident_collector);
        let interner = ident_collector.finalize();
        let mut globals_collector = GlobalsCollector::new(&interner);
        program.walk(&mut globals_collector);
        let globals = globals_collector.finalize().expect("globals error");
        resolve_call_kinds(&mut program, &interner, &globals).expect("call resolution failed");
        inline_macros(&mut program, &interner).expect("macro inline failed");
        typecheck_program(&mut program, &interner, &globals)
    }

    #[test]
    fn predicate_in_requires_desugars_to_acc() {
        let result = run_pipeline(
            r#"
predicate P(x: Ref)
method m(x: Ref)
  requires P(x)
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
        let prog = result.unwrap();
        let method = prog
            .0
            .iter()
            .find_map(|d| {
                if let final_ast::Declaration::Method(m) = d {
                    Some(m)
                } else {
                    None
                }
            })
            .expect("method not found");
        let req = method.requires.as_ref().expect("requires missing");
        assert!(
            matches!(req.0.as_ref(), final_ast::SpatialExpKind::Acc(_, _)),
            "P(x) in requires should desugar to acc, got: {:?}",
            req.0
        );
    }

    #[test]
    fn predicate_in_pure_function_body_is_error() {
        let result = run_pipeline(
            r#"
predicate P(x: Ref)
function f(x: Ref): Bool
{ P(x) }
"#,
        );
        assert!(
            result.as_ref().is_err_and(|errs| errs
                .iter()
                .any(|e| matches!(e, TypeError::PredicateInPureContext(_)))),
            "expected PredicateInPureContext error, got: {result:?}"
        );
    }

    #[test]
    fn result_in_function_body_is_error() {
        let result = run_pipeline(
            r#"
function f(x: Int): Int
{ result }
"#,
        );
        assert!(
            result.as_ref().is_err_and(|errs| errs
                .iter()
                .any(|e| matches!(e, TypeError::IllegalResultUsage))),
            "expected IllegalResultUsage, got: {result:?}"
        );
    }

    #[test]
    fn int_arithmetic_resolves_to_int() {
        let result = run_pipeline(
            r#"
function add(a: Int, b: Int): Int
{ a + b }
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
    }

    #[test]
    fn type_mismatch_in_arithmetic_is_error() {
        let result = run_pipeline(
            r#"
function bad(a: Int, b: Bool): Int
{ a + b }
"#,
        );
        assert!(
            result.as_ref().is_err_and(|errs| errs
                .iter()
                .any(|e| matches!(e, TypeError::TypeMismatch { .. }))),
            "expected TypeMismatch, got: {result:?}"
        );
    }

    #[test]
    fn undefined_variable_is_error() {
        let result = run_pipeline(
            r#"
function f(x: Int): Int
{ y }
"#,
        );
        assert!(
            result.as_ref().is_err_and(|errs| errs
                .iter()
                .any(|e| matches!(e, TypeError::UndefinedVariable(_)))),
            "expected UndefinedVariable, got: {result:?}"
        );
    }

    #[test]
    fn result_in_function_ensures_is_ok() {
        let result = run_pipeline(
            r#"
function f(x: Int): Int
  ensures result == x
{ x }
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
    }

    #[test]
    fn labeled_old_in_function_ensures_is_error() {
        let result = run_pipeline(
            r#"
function f(x: Int): Int
  ensures old[lbl](result) == x
{ x }
"#,
        );
        assert!(
            result.as_ref().is_err_and(|errs| errs
                .iter()
                .any(|e| matches!(e, TypeError::IllegalLabeledOldUsage))),
            "expected IllegalLabeledOldUsage, got: {result:?}"
        );
    }

    #[test]
    fn labeled_old_in_method_ensures_is_error() {
        let result = run_pipeline(
            r#"
method m(x: Int) returns (r: Int)
  ensures old[lbl](r) == x
"#,
        );
        assert!(
            result.as_ref().is_err_and(|errs| errs
                .iter()
                .any(|e| matches!(e, TypeError::IllegalLabeledOldUsage))),
            "expected IllegalLabeledOldUsage, got: {result:?}"
        );
    }
}
