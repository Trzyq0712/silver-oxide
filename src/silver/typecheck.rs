use lasso::Spur;
use rusttyc::types::{Arity, Partial, Variant};
use rusttyc::{Constructable, TcErr, TcKey, TypeChecker, VarlessTypeChecker};
use std::collections::{HashMap, HashSet};

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

// ==========================================
// 1. Type lattice
// ==========================================

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
        Type::Generic(_) | Type::Collection(_) | Type::Domain(..) => SilverTcType::Top,
    }
}

// ==========================================
// 2. Error types
// ==========================================

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
    UndefinedLabel(String),
    ShadowedName(String),
    WrongReturnCount { expected: usize, found: usize },
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
            TypeError::UndefinedLabel(name) => {
                write!(f, "label `{name}` is not defined in this method")
            }
            TypeError::ShadowedName(name) => {
                write!(f, "name `{name}` already declared in this scope")
            }
            TypeError::WrongReturnCount { expected, found } => {
                write!(f, "assignment expects {expected} target(s) on LHS, found {found}")
            }
            TypeError::Tc(e) => write!(f, "Constraint error: {e:?}"),
            TypeError::Other(msg) => write!(f, "{msg}"),
        }
    }
}

// ==========================================
// 3. Context types
// ==========================================

type TypeTable = HashMap<TcKey, Type>;

/// Persistent lexical environment for a declaration (function, method, or predicate).
/// Holds only scope data: `locals` grows incrementally as params and `var` stmts are
/// processed (so uses before declarations produce UndefinedVariable), and pre-collected
/// `labels` (checked for presence only, not position/dominance). Type inference state
/// lives in the ephemeral `ConstraintCtx` / `LoweringCtx`, never here.
struct LocalEnv<'g> {
    globals: &'g Globals,
    interner: &'g Interner,
    locals: HashMap<Spur, Type>,
    labels: HashSet<Spur>,
}

impl<'g> LocalEnv<'g> {
    fn new(globals: &'g Globals, interner: &'g Interner) -> Self {
        Self {
            globals,
            interner,
            locals: HashMap::new(),
            labels: HashSet::new(),
        }
    }

    fn add_local(&mut self, name: Spur, ty: Type) -> Result<(), TypeError> {
        let s = self.interner.resolve(&name).to_string();
        if self.globals.resolve(name).is_some() {
            return Err(TypeError::ShadowedName(s));
        }
        if self.locals.contains_key(&name) {
            return Err(TypeError::ShadowedName(s));
        }
        if self.labels.contains(&name) {
            return Err(TypeError::ShadowedName(s));
        }
        self.locals.insert(name, ty);
        Ok(())
    }

    fn add_label(&mut self, name: Spur) -> Result<(), TypeError> {
        let s = self.interner.resolve(&name).to_string();
        if self.locals.contains_key(&name) {
            return Err(TypeError::ShadowedName(s));
        }
        if self.labels.contains(&name) {
            return Err(TypeError::ShadowedName(s));
        }
        self.labels.insert(name);
        Ok(())
    }

    /// Typecheck a pure expression and lower it to `final_ast`.
    /// `result_ty` enables the `result` keyword (function postconditions); pass `None`
    /// for methods, predicates, and function bodies.
    fn typecheck_pure<Ext: PureExt>(
        &self,
        exp: &mut silver::Exp,
        expected: SilverTcType,
        result_ty: Option<Type>,
    ) -> Result<TypedPureExp<Ext>, TypeError> {
        let mut c = ConstraintCtx::new(self, result_ty);
        let root = c.constrain_pure(exp)?;
        c.tc.impose(root.concretizes_explicit(expected))?;
        let table = c.tc.type_check().map_err(TypeError::from)?;
        LoweringCtx::new(self, &table).lower_pure::<Ext>(exp)
    }

    /// Typecheck a spatial (assertion) expression and lower it to `final_ast`.
    fn typecheck_spatial<Ext: PureExt>(
        &self,
        exp: &mut silver::Exp,
    ) -> Result<SpatialExp<Ext>, TypeError> {
        let mut c = ConstraintCtx::new(self, None);
        c.constrain_spatial(exp)?;
        let table = c.tc.type_check().map_err(TypeError::from)?;
        LoweringCtx::new(self, &table).lower_spatial::<Ext>(exp)
    }

    /// Typecheck a `acc(pred(..), perm)` location used by fold/unfold.
    fn typecheck_pred_with_perm<Ext: PureExt>(
        &self,
        acc: &mut silver::AccExp,
    ) -> Result<PredicateWithPerm<Ext>, TypeError> {
        let mut c = ConstraintCtx::new(self, None);
        c.constrain_resource(&mut acc.loc)?;
        let pk = c.constrain_pure(&mut acc.perm)?;
        c.tc
            .impose(pk.concretizes_explicit(SilverTcType::Numeric))?;
        let table = c.tc.type_check().map_err(TypeError::from)?;

        let lowerer = LoweringCtx::new(self, &table);
        let resource = lowerer.lower_resource::<Ext>(&acc.loc)?;
        let perm = lowerer.lower_pure::<Ext>(&acc.perm)?;
        let pred_call = match *resource.0 {
            ResourceExpKind::PredicateCall(call) => call,
            ResourceExpKind::Field(..) => {
                return Err(TypeError::Other(
                    "fold/unfold requires a predicate, not a field".to_string(),
                ));
            }
        };
        Ok(PredicateWithPerm { pred_call, perm })
    }
}

/// Phase 1: constraint generation. Walks `silver::Exp`, stamps a fresh `TcKey` onto every
/// pure node (`exp.ty = Infer(key)`), and feeds rules into the `rusttyc` solver. Produces
/// no `final_ast`; that is the lowering phase's job.
struct ConstraintCtx<'a, 'g> {
    env: &'a LocalEnv<'g>,
    tc: VarlessTypeChecker<SilverTcType>,
    /// Let-binders and quantifier binders local to the expression being walked.
    let_bindings: HashMap<Spur, TcKey>,
    /// Return type for the enclosing function, enabling `result`; None otherwise.
    result_ty: Option<Type>,
}

impl<'a, 'g> ConstraintCtx<'a, 'g> {
    fn new(env: &'a LocalEnv<'g>, result_ty: Option<Type>) -> Self {
        Self {
            env,
            tc: TypeChecker::without_vars(),
            let_bindings: HashMap::new(),
            result_ty,
        }
    }
}

/// Phase 3: lowering. Reads the solved `TypeTable` and maps each `silver::Exp` into a
/// `final_ast` node in one immutable pass. Stateless w.r.t. binders: every node's type is
/// fetched from its stamped `TcKey`, so let/quantifier bindings need no bookkeeping here.
struct LoweringCtx<'a, 'g> {
    env: &'a LocalEnv<'g>,
    table: &'a TypeTable,
}

impl<'a, 'g> LoweringCtx<'a, 'g> {
    fn new(env: &'a LocalEnv<'g>, table: &'a TypeTable) -> Self {
        Self { env, table }
    }

    fn resolved_ty(&self, exp: &silver::Exp) -> Result<Type, TypeError> {
        match exp.ty {
            silver::InferenceType::Infer(k) => self
                .table
                .get(&k)
                .cloned()
                .ok_or_else(|| TypeError::Other("unresolved type variable".to_string())),
            _ => Err(TypeError::Other(
                "expression was not assigned a type key".to_string(),
            )),
        }
    }
}

// ==========================================
// 4. PureExt trait
// ==========================================

trait PureExt: Sized {
    fn lower_old(
        label: Option<Spur>,
        inner: TypedPureExp<Self>,
        known_labels: &HashSet<Spur>,
        interner: &Interner,
    ) -> Result<Self, TypeError>;
    fn lower_result() -> Result<Self, TypeError>;
    fn lower_perm(resource: ResourceExp<Self>) -> Result<Self, TypeError>;
}

impl PureExt for ! {
    fn lower_old(
        _label: Option<Spur>,
        _inner: TypedPureExp<!>,
        _known_labels: &HashSet<Spur>,
        _interner: &Interner,
    ) -> Result<!, TypeError> {
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
        _known_labels: &HashSet<Spur>,
        _interner: &Interner,
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
        _known_labels: &HashSet<Spur>,
        _interner: &Interner,
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
        known_labels: &HashSet<Spur>,
        interner: &Interner,
    ) -> Result<MethodBodyExt, TypeError> {
        if let Some(lbl) = label {
            if !known_labels.contains(&lbl) {
                return Err(TypeError::UndefinedLabel(
                    interner.resolve(&lbl).to_string(),
                ));
            }
        }
        Ok(MethodBodyExt::Old(label, inner))
    }
    fn lower_result() -> Result<MethodBodyExt, TypeError> {
        Err(TypeError::IllegalResultUsage)
    }
    fn lower_perm(resource: ResourceExp<MethodBodyExt>) -> Result<MethodBodyExt, TypeError> {
        Ok(MethodBodyExt::Perm(resource))
    }
}

// ==========================================
// 5. Type translation helpers
// ==========================================

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

// ==========================================
// 6. Contract helpers
// ==========================================

fn combine_spatial<Ext: PureExt>(
    exps: &mut [silver::Exp],
    ctx: &LocalEnv,
) -> Result<Option<SpatialExp<Ext>>, TypeError> {
    let mut iter = exps.iter_mut();
    let first = match iter.next() {
        None => return Ok(None),
        Some(e) => ctx.typecheck_spatial(e)?,
    };
    let combined = iter.try_fold(first, |acc, e| {
        let next = ctx.typecheck_spatial(e)?;
        Ok::<_, TypeError>(SpatialExp(Box::new(SpatialExpKind::Conj(acc, next))))
    })?;
    Ok(Some(combined))
}

// ==========================================
// 7. Phase 1 — constraint generation
// ==========================================

impl<'a, 'g> ConstraintCtx<'a, 'g> {
    /// Walk a pure expression, stamp its node with a fresh key, impose its rules, and
    /// return that key so callers can relate it to their own.
    fn constrain_pure(&mut self, exp: &mut silver::Exp) -> Result<TcKey, TypeError> {
        use silver::ExpKind;

        let key = self.tc.new_term_key();
        exp.ty = silver::InferenceType::Infer(key);

        match exp.kind.as_mut() {
            ExpKind::Const(c) => {
                self.tc
                    .impose(key.concretizes_explicit(type_to_tc(&const_type(c))))?;
            }

            ExpKind::Ident(ident) => {
                let spur = ident.id();
                if let Some(&binder_key) = self.let_bindings.get(&spur) {
                    self.tc.impose(key.equate_with(binder_key))?;
                } else {
                    let ty = self.env.locals.get(&spur).cloned().ok_or_else(|| {
                        TypeError::UndefinedVariable(self.env.interner.resolve(&spur).to_string())
                    })?;
                    self.tc.impose(key.concretizes_explicit(type_to_tc(&ty)))?;
                }
            }

            ExpKind::Result => {
                let ty = self.result_ty.clone().ok_or(TypeError::IllegalResultUsage)?;
                self.tc.impose(key.concretizes_explicit(type_to_tc(&ty)))?;
            }

            ExpKind::Old(_label, inner) => {
                let inner_key = self.constrain_pure(inner)?;
                self.tc.impose(key.equate_with(inner_key))?;
            }

            ExpKind::Ascribe(inner, ascribed_ty) => {
                let target = type_to_tc(&Type::from(&*ascribed_ty));
                let inner_key = self.constrain_pure(inner)?;
                self.tc.impose(inner_key.concretizes_explicit(target.clone()))?;
                self.tc.impose(key.concretizes_explicit(target))?;
            }

            ExpKind::UnOp(op, inner) => self.constrain_unop(op, inner, key)?,

            ExpKind::BinOp(op, left, right) => self.constrain_binop(op, left, right, key)?,

            ExpKind::Ternary(cond, then, else_) => {
                let cond_key = self.constrain_pure(cond)?;
                self.tc.impose(cond_key.concretizes_explicit(SilverTcType::Bool))?;
                let then_key = self.constrain_pure(then)?;
                let else_key = self.constrain_pure(else_)?;
                self.tc.impose(key.is_sym_meet_of(then_key, else_key))?;
            }

            ExpKind::LetIn(binder, value, body) => {
                let value_key = self.constrain_pure(value)?;
                let binder_spur = binder.0.id();
                // Error if binder would shadow a currently in-scope name.
                // Sibling scopes are fine: after the body, binder_spur is removed/restored.
                if self.env.locals.contains_key(&binder_spur)
                    || self.let_bindings.contains_key(&binder_spur)
                {
                    return Err(TypeError::ShadowedName(
                        self.env.interner.resolve(&binder_spur).to_string(),
                    ));
                }
                self.let_bindings.insert(binder_spur, value_key);
                let body_key = self.constrain_pure(body)?;
                self.let_bindings.remove(&binder_spur);
                self.tc.impose(key.equate_with(body_key))?;
            }

            ExpKind::Call(call) => self.constrain_call(call, key)?,

            ExpKind::Field(base, field_name) => self.constrain_field(base, field_name, key)?,

            ExpKind::HeapUpdate(silver::HeapUpdateOp::Unfold, acc_exp, body) => {
                self.constrain_resource(&mut acc_exp.loc)?;
                self.constrain_pure(&mut acc_exp.perm)?;
                let body_key = self.constrain_pure(body)?;
                self.tc.impose(key.equate_with(body_key))?;
            }

            ExpKind::AdtDestructor(base, _field) => {
                self.constrain_pure(base)?;
                self.tc.impose(key.concretizes_explicit(SilverTcType::Bool))?;
            }

            ExpKind::AdtDiscriminator(base, _variant) => {
                self.constrain_pure(base)?;
                self.tc.impose(key.concretizes_explicit(SilverTcType::Bool))?;
            }

            ExpKind::Quantifier(_, bound_vars, _triggers, body) => {
                // Treat quantifier binders like let-binders: impose their declared type,
                // restore the previous bindings afterwards.
                let mut prev_bindings = Vec::with_capacity(bound_vars.len());
                for bv in bound_vars.iter() {
                    let ty = Type::from(&bv.ty);
                    let bk = self.tc.new_term_key();
                    self.tc.impose(bk.concretizes_explicit(type_to_tc(&ty)))?;
                    let prev = self.let_bindings.insert(bv.idn.0.id(), bk);
                    prev_bindings.push((bv.idn.0.id(), prev));
                }
                let body_key = self.constrain_pure(body)?;
                for (spur, prev) in prev_bindings {
                    match prev {
                        Some(p) => {
                            self.let_bindings.insert(spur, p);
                        }
                        None => {
                            self.let_bindings.remove(&spur);
                        }
                    }
                }
                self.tc.impose(body_key.concretizes_explicit(SilverTcType::Bool))?;
                self.tc.impose(key.concretizes_explicit(SilverTcType::Bool))?;
            }

            _ => {
                return Err(TypeError::Other(format!(
                    "unsupported pure expression: {:?}",
                    exp.kind
                )));
            }
        }

        Ok(key)
    }

    fn constrain_unop(
        &mut self,
        op: &silver::UnOp,
        inner: &mut silver::Exp,
        key: TcKey,
    ) -> Result<(), TypeError> {
        match op {
            silver::UnOp::Not => {
                let inner_key = self.constrain_pure(inner)?;
                self.tc.impose(inner_key.concretizes_explicit(SilverTcType::Bool))?;
                self.tc.impose(key.concretizes_explicit(SilverTcType::Bool))?;
            }
            silver::UnOp::Neg => {
                let inner_key = self.constrain_pure(inner)?;
                self.tc.impose(inner_key.concretizes_explicit(SilverTcType::Numeric))?;
                self.tc.impose(key.equate_with(inner_key))?;
            }
            silver::UnOp::Perm => {
                self.constrain_resource(inner)?;
                self.tc.impose(key.concretizes_explicit(SilverTcType::Real))?;
            }
        }
        Ok(())
    }

    fn constrain_binop(
        &mut self,
        op: &silver::BinOp,
        left: &mut silver::Exp,
        right: &mut silver::Exp,
        key: TcKey,
    ) -> Result<(), TypeError> {
        use silver::BinOp as SBinOp;

        let lk = self.constrain_pure(left)?;
        let rk = self.constrain_pure(right)?;

        match op {
            SBinOp::And | SBinOp::Or | SBinOp::Implies | SBinOp::Iff => {
                self.tc.impose(lk.concretizes_explicit(SilverTcType::Bool))?;
                self.tc.impose(rk.concretizes_explicit(SilverTcType::Bool))?;
                self.tc.impose(key.concretizes_explicit(SilverTcType::Bool))?;
            }
            SBinOp::Eq | SBinOp::Neq => {
                self.tc.impose(lk.equate_with(rk))?;
                self.tc.impose(key.concretizes_explicit(SilverTcType::Bool))?;
            }
            SBinOp::Lt | SBinOp::Le | SBinOp::Gt | SBinOp::Ge => {
                self.tc.impose(lk.concretizes_explicit(SilverTcType::Numeric))?;
                self.tc.impose(rk.concretizes_explicit(SilverTcType::Numeric))?;
                self.tc.impose(lk.equate_with(rk))?;
                self.tc.impose(key.concretizes_explicit(SilverTcType::Bool))?;
            }
            SBinOp::Plus | SBinOp::Minus | SBinOp::Mult | SBinOp::Mod => {
                self.tc.impose(lk.concretizes_explicit(SilverTcType::Numeric))?;
                self.tc.impose(rk.concretizes_explicit(SilverTcType::Numeric))?;
                self.tc.impose(key.is_sym_meet_of(lk, rk))?;
            }
            SBinOp::Div => {
                self.tc.impose(lk.concretizes_explicit(SilverTcType::Numeric))?;
                self.tc.impose(rk.concretizes_explicit(SilverTcType::Numeric))?;
                self.tc.impose(key.concretizes_explicit(SilverTcType::Numeric))?;
            }
            _ => {
                return Err(TypeError::Other(format!(
                    "unsupported binary operator: {op:?}"
                )));
            }
        }
        Ok(())
    }

    fn constrain_call(
        &mut self,
        call: &mut silver::Call<silver::ExpCallKind>,
        key: TcKey,
    ) -> Result<(), TypeError> {
        use silver::ExpCallKind;
        let call_name = call.name.id();
        let sym = self.env.globals.resolve(call_name).ok_or_else(|| {
            TypeError::UndefinedVariable(self.env.interner.resolve(&call_name).to_string())
        })?;

        match call.kind.as_ref().expect("call kind must be resolved") {
            ExpCallKind::Predicate => Err(TypeError::PredicateInPureContext(
                self.env.interner.resolve(&call_name).to_string(),
            )),
            ExpCallKind::Function | ExpCallKind::AdtConstructor => {
                let sig = sym.as_function().ok_or_else(|| {
                    TypeError::Other(format!(
                        "{} is not a function",
                        self.env.interner.resolve(&call_name)
                    ))
                })?;
                if sig.params.len() != call.args.len() {
                    return Err(TypeError::WrongArgCount {
                        name: self.env.interner.resolve(&call_name).to_string(),
                        expected: sig.params.len(),
                        found: call.args.len(),
                    });
                }
                let ret_ty = sig.ret.clone();
                let expected_params: Vec<Type> = sig.params.clone();
                for (arg, expected) in call.args.iter_mut().zip(expected_params.iter()) {
                    let arg_key = self.constrain_pure(arg)?;
                    self.tc.impose(arg_key.concretizes_explicit(type_to_tc(expected)))?;
                }
                self.tc.impose(key.concretizes_explicit(type_to_tc(&ret_ty)))?;
                Ok(())
            }
            ExpCallKind::Macro => Err(TypeError::Other(
                "macro in expression (should have been inlined)".to_string(),
            )),
        }
    }

    fn constrain_field(
        &mut self,
        base: &mut silver::Exp,
        field_name: &silver::Ident,
        key: TcKey,
    ) -> Result<(), TypeError> {
        let field_id = field_name.id();
        let sym = self.env.globals.resolve(field_id).ok_or_else(|| {
            TypeError::Other(format!(
                "unknown field: {}",
                self.env.interner.resolve(&field_id)
            ))
        })?;
        let field_ty = sym.as_field().ok_or_else(|| {
            TypeError::Other(format!(
                "{} is not a field",
                self.env.interner.resolve(&field_id)
            ))
        })?;
        let ret_ty = field_ty.clone();
        let base_key = self.constrain_pure(base)?;
        self.tc.impose(base_key.concretizes_explicit(SilverTcType::Ref))?;
        self.tc.impose(key.concretizes_explicit(type_to_tc(&ret_ty)))?;
        Ok(())
    }

    fn constrain_resource(&mut self, exp: &mut silver::Exp) -> Result<(), TypeError> {
        match exp.kind.as_mut() {
            silver::ExpKind::Field(base, _field_name) => {
                let base_key = self.constrain_pure(base)?;
                self.tc.impose(base_key.concretizes_explicit(SilverTcType::Ref))?;
                Ok(())
            }
            silver::ExpKind::Call(call) => match call.kind.as_ref().expect("call kind resolved") {
                silver::ExpCallKind::Predicate => self.constrain_predicate_resource(call),
                _ => Err(TypeError::Other(
                    "resource position requires field or predicate call".to_string(),
                )),
            },
            _ => Err(TypeError::Other(
                "resource position requires field or predicate call".to_string(),
            )),
        }
    }

    fn constrain_predicate_resource(
        &mut self,
        call: &mut silver::Call<silver::ExpCallKind>,
    ) -> Result<(), TypeError> {
        let call_name = call.name.id();
        let sym = self.env.globals.resolve(call_name).ok_or_else(|| {
            TypeError::UndefinedVariable(self.env.interner.resolve(&call_name).to_string())
        })?;
        let sig = sym.as_predicate().ok_or_else(|| {
            TypeError::Other(format!(
                "{} is not a predicate",
                self.env.interner.resolve(&call_name)
            ))
        })?;
        if sig.params.len() != call.args.len() {
            return Err(TypeError::WrongArgCount {
                name: self.env.interner.resolve(&call_name).to_string(),
                expected: sig.params.len(),
                found: call.args.len(),
            });
        }
        let expected_params: Vec<Type> = sig.params.clone();
        for (arg, expected) in call.args.iter_mut().zip(expected_params.iter()) {
            let arg_key = self.constrain_pure(arg)?;
            self.tc.impose(arg_key.concretizes_explicit(type_to_tc(expected)))?;
        }
        Ok(())
    }

    fn constrain_spatial(&mut self, exp: &mut silver::Exp) -> Result<(), TypeError> {
        use silver::ExpKind;

        // A bare predicate call in assertion position is shorthand for full permission.
        if let ExpKind::Call(call) = exp.kind.as_mut() {
            if matches!(call.kind, Some(silver::ExpCallKind::Predicate)) {
                return self.constrain_predicate_resource(call);
            }
        }

        match exp.kind.as_mut() {
            ExpKind::Acc(acc_exp) => {
                self.constrain_resource(&mut acc_exp.loc)?;
                let perm_key = self.constrain_pure(&mut acc_exp.perm)?;
                self.tc.impose(perm_key.concretizes_explicit(SilverTcType::Numeric))?;
                Ok(())
            }
            ExpKind::BinOp(silver::BinOp::And | silver::BinOp::InhaleExhale, l, r) => {
                self.constrain_spatial(l)?;
                self.constrain_spatial(r)
            }
            ExpKind::BinOp(silver::BinOp::Implies, l, r) => {
                let cond_key = self.constrain_pure(l)?;
                self.tc.impose(cond_key.concretizes_explicit(SilverTcType::Bool))?;
                self.constrain_spatial(r)
            }
            ExpKind::Ternary(cond, then, else_) => {
                let cond_key = self.constrain_pure(cond)?;
                self.tc.impose(cond_key.concretizes_explicit(SilverTcType::Bool))?;
                self.constrain_spatial(then)?;
                self.constrain_spatial(else_)
            }
            _ => {
                let pure_key = self.constrain_pure(exp)?;
                self.tc.impose(pure_key.concretizes_explicit(SilverTcType::Bool))?;
                Ok(())
            }
        }
    }
}

// ==========================================
// 8. Phase 3 — lowering to final_ast
// ==========================================

impl<'a, 'g> LoweringCtx<'a, 'g> {
    fn lower_pure<Ext: PureExt>(
        &self,
        exp: &silver::Exp,
    ) -> Result<TypedPureExp<Ext>, TypeError> {
        let ty = self.resolved_ty(exp)?;
        let kind = self.lower_pure_kind::<Ext>(exp)?;
        Ok(TypedPureExp {
            ty,
            exp: Box::new(kind),
        })
    }

    fn lower_pure_kind<Ext: PureExt>(
        &self,
        exp: &silver::Exp,
    ) -> Result<PureExpKind<Ext>, TypeError> {
        use silver::ExpKind;

        match &*exp.kind {
            ExpKind::Const(c) => Ok(PureExpKind::Const(lower_const_literal(c))),

            ExpKind::Ident(ident) => Ok(PureExpKind::Ident(lower_ident(ident))),

            ExpKind::Result => Ok(PureExpKind::Ext(Ext::lower_result()?)),

            ExpKind::Old(label, inner) => {
                let inner_exp = self.lower_pure::<Ext>(inner)?;
                let label_spur = label.as_ref().map(|l| l.id());
                let ext =
                    Ext::lower_old(label_spur, inner_exp, &self.env.labels, self.env.interner)?;
                Ok(PureExpKind::Ext(ext))
            }

            ExpKind::Ascribe(inner, ascribed_ty) => {
                let inner_exp = self.lower_pure::<Ext>(inner)?;
                Ok(PureExpKind::Ascribe(inner_exp, Type::from(ascribed_ty)))
            }

            ExpKind::UnOp(op, inner) => self.lower_unop::<Ext>(op, inner),

            ExpKind::BinOp(op, left, right) => {
                let le = self.lower_pure::<Ext>(left)?;
                let re = self.lower_pure::<Ext>(right)?;
                Ok(PureExpKind::Binary(lower_bin_op(op), le, re))
            }

            ExpKind::Ternary(cond, then, else_) => Ok(PureExpKind::Ternary {
                if_: self.lower_pure::<Ext>(cond)?,
                then: self.lower_pure::<Ext>(then)?,
                else_: self.lower_pure::<Ext>(else_)?,
            }),

            ExpKind::LetIn(binder, value, body) => Ok(PureExpKind::LetIn {
                binder: Ident(binder.0.id()),
                value: self.lower_pure::<Ext>(value)?,
                exp: self.lower_pure::<Ext>(body)?,
            }),

            ExpKind::Call(call) => self.lower_call::<Ext>(call),

            ExpKind::Field(base, field_name) => {
                let base_exp = self.lower_pure::<Ext>(base)?;
                Ok(PureExpKind::Field(base_exp, Ident(field_name.id())))
            }

            ExpKind::HeapUpdate(silver::HeapUpdateOp::Unfold, acc_exp, body) => {
                let resource = self.lower_resource::<Ext>(&acc_exp.loc)?;
                let perm = self.lower_pure::<Ext>(&acc_exp.perm)?;
                let pred_call = match *resource.0 {
                    ResourceExpKind::PredicateCall(call) => call,
                    ResourceExpKind::Field(..) => {
                        return Err(TypeError::Other("cannot unfold a field".to_string()));
                    }
                };
                let body_exp = self.lower_pure::<Ext>(body)?;
                Ok(PureExpKind::Unfolding(
                    PredicateWithPerm { pred_call, perm },
                    body_exp,
                ))
            }

            ExpKind::AdtDestructor(base, field) => {
                let base_exp = self.lower_pure::<Ext>(base)?;
                Ok(PureExpKind::AdtDestructor(base_exp, Ident(field.id())))
            }

            ExpKind::AdtDiscriminator(base, variant) => {
                let base_exp = self.lower_pure::<Ext>(base)?;
                Ok(PureExpKind::AdtDiscriminator(base_exp, Ident(variant.id())))
            }

            // Quantifiers emitted as bool constant (proper final_ast support later).
            ExpKind::Quantifier(..) => Ok(PureExpKind::Const(Literal::Bool(true))),

            _ => Err(TypeError::Other(format!(
                "unsupported pure expression: {:?}",
                exp.kind
            ))),
        }
    }

    fn lower_unop<Ext: PureExt>(
        &self,
        op: &silver::UnOp,
        inner: &silver::Exp,
    ) -> Result<PureExpKind<Ext>, TypeError> {
        match op {
            silver::UnOp::Not => Ok(PureExpKind::Unary(UnOp::Not, self.lower_pure::<Ext>(inner)?)),
            silver::UnOp::Neg => Ok(PureExpKind::Unary(UnOp::Neg, self.lower_pure::<Ext>(inner)?)),
            silver::UnOp::Perm => {
                let resource = self.lower_resource::<Ext>(inner)?;
                Ok(PureExpKind::Ext(Ext::lower_perm(resource)?))
            }
        }
    }

    fn lower_call<Ext: PureExt>(
        &self,
        call: &silver::Call<silver::ExpCallKind>,
    ) -> Result<PureExpKind<Ext>, TypeError> {
        use silver::ExpCallKind;
        let call_name = call.name.id();
        match call.kind.as_ref().expect("call kind must be resolved") {
            ExpCallKind::Predicate => Err(TypeError::PredicateInPureContext(
                self.env.interner.resolve(&call_name).to_string(),
            )),
            ExpCallKind::Function | ExpCallKind::AdtConstructor => {
                let mut args = Vec::with_capacity(call.args.len());
                for arg in call.args.iter() {
                    args.push(self.lower_pure::<Ext>(arg)?);
                }
                Ok(PureExpKind::FunctionCall(Call {
                    name: Ident(call_name),
                    args,
                }))
            }
            ExpCallKind::Macro => Err(TypeError::Other(
                "macro in expression (should have been inlined)".to_string(),
            )),
        }
    }

    fn lower_resource<Ext: PureExt>(
        &self,
        exp: &silver::Exp,
    ) -> Result<ResourceExp<Ext>, TypeError> {
        match &*exp.kind {
            silver::ExpKind::Field(base, field_name) => {
                let base_exp = self.lower_pure::<Ext>(base)?;
                Ok(ResourceExp(Box::new(ResourceExpKind::Field(
                    base_exp,
                    Ident(field_name.id()),
                ))))
            }
            silver::ExpKind::Call(call) => match call.kind.as_ref().expect("call kind resolved") {
                silver::ExpCallKind::Predicate => self.lower_predicate_resource::<Ext>(call),
                _ => Err(TypeError::Other(
                    "resource position requires field or predicate call".to_string(),
                )),
            },
            _ => Err(TypeError::Other(
                "resource position requires field or predicate call".to_string(),
            )),
        }
    }

    fn lower_predicate_resource<Ext: PureExt>(
        &self,
        call: &silver::Call<silver::ExpCallKind>,
    ) -> Result<ResourceExp<Ext>, TypeError> {
        let mut args = Vec::with_capacity(call.args.len());
        for arg in call.args.iter() {
            args.push(self.lower_pure::<Ext>(arg)?);
        }
        Ok(ResourceExp(Box::new(ResourceExpKind::PredicateCall(Call {
            name: Ident(call.name.id()),
            args,
        }))))
    }

    fn lower_spatial<Ext: PureExt>(
        &self,
        exp: &silver::Exp,
    ) -> Result<SpatialExp<Ext>, TypeError> {
        use silver::ExpKind;

        if let ExpKind::Call(call) = &*exp.kind {
            if matches!(call.kind, Some(silver::ExpCallKind::Predicate)) {
                let resource = self.lower_predicate_resource::<Ext>(call)?;
                return Ok(SpatialExp(Box::new(SpatialExpKind::Acc(
                    resource,
                    write_perm(),
                ))));
            }
        }

        match &*exp.kind {
            ExpKind::Acc(acc_exp) => {
                let resource = self.lower_resource::<Ext>(&acc_exp.loc)?;
                let perm_exp = self.lower_pure::<Ext>(&acc_exp.perm)?;
                Ok(SpatialExp(Box::new(SpatialExpKind::Acc(resource, perm_exp))))
            }

            ExpKind::BinOp(silver::BinOp::And | silver::BinOp::InhaleExhale, l, r) => {
                let ls = self.lower_spatial::<Ext>(l)?;
                let rs = self.lower_spatial::<Ext>(r)?;
                Ok(SpatialExp(Box::new(SpatialExpKind::Conj(ls, rs))))
            }

            ExpKind::BinOp(silver::BinOp::Implies, l, r) => {
                let cond_exp = self.lower_pure::<Ext>(l)?;
                let rs = self.lower_spatial::<Ext>(r)?;
                Ok(SpatialExp(Box::new(SpatialExpKind::Implies(cond_exp, rs))))
            }

            ExpKind::Ternary(cond, then, else_) => {
                let cond_exp = self.lower_pure::<Ext>(cond)?;
                let then_s = self.lower_spatial::<Ext>(then)?;
                let else_s = self.lower_spatial::<Ext>(else_)?;
                Ok(SpatialExp(Box::new(SpatialExpKind::Ternary {
                    if_: cond_exp,
                    then: then_s,
                    else_: else_s,
                })))
            }

            _ => {
                let pure_exp = self.lower_pure::<Ext>(exp)?;
                Ok(SpatialExp(Box::new(SpatialExpKind::Pure(pure_exp))))
            }
        }
    }
}

// ==========================================
// 9. Constant lowering helpers
// ==========================================

/// Type of a literal, used during constraint generation (no `final_ast` produced).
fn const_type(c: &silver::ConstKind) -> Type {
    match c {
        silver::ConstKind::Bool(_) => Type::Bool,
        silver::ConstKind::Int(_) => Type::Int,
        silver::ConstKind::Real(_) | silver::ConstKind::Wildcard | silver::ConstKind::Epsilon => {
            Type::Real
        }
        silver::ConstKind::Null => Type::Ref,
    }
}

fn lower_const_literal(c: &silver::ConstKind) -> Literal {
    match c {
        silver::ConstKind::Bool(b) => Literal::Bool(*b),
        silver::ConstKind::Int(i) => Literal::Int(i.clone()),
        silver::ConstKind::Real(r) => Literal::Real(r.clone()),
        silver::ConstKind::Null => Literal::Null,
        silver::ConstKind::Wildcard => Literal::Wildcard,
        silver::ConstKind::Epsilon => Literal::Real(num::BigRational::new(
            num::BigInt::from(0),
            num::BigInt::from(1),
        )),
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

// ==========================================
// 10. Statement lowering
// ==========================================

fn collect_labels(stmts: &[silver::Statement], labels: &mut HashSet<Spur>) {
    for stmt in stmts {
        match stmt {
            silver::Statement::Label(decl, _) => {
                labels.insert(decl.0.id());
            }
            silver::Statement::Block(block) => {
                collect_labels(&block.0, labels);
            }
            _ => {}
        }
    }
}

fn lower_statement(
    stmt: &mut silver::Statement,
    ctx: &mut LocalEnv,
) -> Result<final_ast::Statement, TypeError> {
    use silver::Statement as S;
    match stmt {
        S::Assume(e) => Ok(final_ast::Statement::Assume(ctx.typecheck_spatial(e)?)),
        S::Assert(e) => Ok(final_ast::Statement::Assert(ctx.typecheck_spatial(e)?)),
        S::Inhale(e) => Ok(final_ast::Statement::Inhale(ctx.typecheck_spatial(e)?)),
        S::Exhale(e) => Ok(final_ast::Statement::Exhale(ctx.typecheck_spatial(e)?)),

        S::Fold(acc) => Ok(final_ast::Statement::Fold(ctx.typecheck_pred_with_perm(acc)?)),
        S::Unfold(acc) => Ok(final_ast::Statement::Unfold(
            ctx.typecheck_pred_with_perm(acc)?,
        )),

        S::Var(decls, init) => {
            let mut typed_decls = Vec::with_capacity(decls.len());
            for d in decls.iter() {
                let ty = Type::from(&d.ty);
                ctx.add_local(d.idn.0.id(), ty.clone())?;
                typed_decls.push(TypedIdent {
                    name: Ident(d.idn.0.id()),
                    ty,
                });
            }
            let lhs_types: Vec<Type> = typed_decls.iter().map(|d| d.ty.clone()).collect();
            let lowered_rhs = init
                .as_mut()
                .map(|rhs| lower_rhs_against_lhs(rhs, ctx, &lhs_types))
                .transpose()?;
            Ok(final_ast::Statement::Var(typed_decls, lowered_rhs))
        }

        S::Assign(lhs_list, rhs) => {
            // Lower LHS first — concrete types, never generic
            let lowered_lhs_typed: Vec<(final_ast::AssignLhs, Type)> = lhs_list
                .iter_mut()
                .map(|lhs| lower_assign_lhs_typed(lhs, ctx))
                .collect::<Result<_, _>>()?;
            let lhs_types: Vec<Type> = lowered_lhs_typed.iter().map(|(_, ty)| ty.clone()).collect();
            let lowered_rhs = lower_rhs_against_lhs(rhs, ctx, &lhs_types)?;
            let lowered_lhs = lowered_lhs_typed.into_iter().map(|(lhs, _)| lhs).collect();
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

fn lower_assign_lhs_typed(
    lhs: &mut silver::AssignLhs,
    ctx: &mut LocalEnv,
) -> Result<(final_ast::AssignLhs, Type), TypeError> {
    match lhs {
        silver::AssignLhs::Ident(ident) => {
            let spur = ident.id();
            let ty = ctx
                .locals
                .get(&spur)
                .cloned()
                .ok_or_else(|| TypeError::UndefinedVariable(ctx.interner.resolve(&spur).to_string()))?;
            Ok((final_ast::AssignLhs::Var(Ident(spur)), ty))
        }
        silver::AssignLhs::Field(base, field) => {
            let field_id = field.id();
            let field_ty = ctx
                .globals
                .resolve(field_id)
                .and_then(|s| s.as_field())
                .cloned()
                .ok_or_else(|| TypeError::Other("undefined field".to_string()))?;
            let base_exp = ctx.typecheck_pure::<MethodBodyExt>(base, SilverTcType::Ref, None)?;
            Ok((final_ast::AssignLhs::Field(base_exp, Ident(field_id)), field_ty))
        }
    }
}

/// Lower an assignment/var-init RHS, validating and constraining against `lhs_types`.
/// Expression RHS: constrained to `lhs_types[0]` (must be single).
/// New RHS: requires single `Ref` LHS.
/// Method call RHS: arg and return types checked against signature.
fn lower_rhs_against_lhs(
    rhs: &mut silver::AssignRhs,
    ctx: &mut LocalEnv,
    lhs_types: &[Type],
) -> Result<final_ast::AssignRhs, TypeError> {
    match rhs {
        silver::AssignRhs::Exp(e) => {
            if lhs_types.len() != 1 {
                return Err(TypeError::WrongReturnCount {
                    expected: 1,
                    found: lhs_types.len(),
                });
            }
            let exp = ctx.typecheck_pure::<MethodBodyExt>(e, type_to_tc(&lhs_types[0]), None)?;
            Ok(final_ast::AssignRhs::Exp(exp))
        }

        silver::AssignRhs::New(fields) => {
            if lhs_types.len() != 1 {
                return Err(TypeError::WrongReturnCount {
                    expected: 1,
                    found: lhs_types.len(),
                });
            }
            if lhs_types[0] != Type::Ref {
                return Err(TypeError::Other(format!(
                    "new(*) requires a Ref target, found {:?}",
                    lhs_types[0]
                )));
            }
            let star_or_fields = match fields {
                silver::StarOrNames::Star => final_ast::StarOrFields::Star,
                silver::StarOrNames::Names(names) => {
                    final_ast::StarOrFields::Fields(names.iter().map(|n| Ident(n.id())).collect())
                }
            };
            Ok(final_ast::AssignRhs::New(star_or_fields))
        }

        silver::AssignRhs::Call(call) => {
            let call_name = call.name.id();
            // Clone sig to release borrow on ctx.globals before calling typecheck_pure.
            let sig = ctx
                .globals
                .resolve(call_name)
                .and_then(|s| s.as_method())
                .cloned()
                .ok_or_else(|| {
                    TypeError::Other(format!(
                        "method `{}` not found",
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
            if sig.rets.len() != lhs_types.len() {
                return Err(TypeError::WrongReturnCount {
                    expected: sig.rets.len(),
                    found: lhs_types.len(),
                });
            }
            // Each LHS type must match the corresponding return type from the signature.
            for (i, lhs_ty) in lhs_types.iter().enumerate() {
                let ret_ty = sig.rets[i].clone();
                if *lhs_ty != ret_ty {
                    return Err(TypeError::Other(format!(
                        "return {} of `{}`: expected {:?}, found {:?}",
                        i,
                        ctx.interner.resolve(&call_name),
                        ret_ty,
                        lhs_ty
                    )));
                }
            }
            // Each arg is constrained by the corresponding parameter type from the signature.
            let mut lowered_args = Vec::with_capacity(call.args.len());
            for (arg, param_ty) in call.args.iter_mut().zip(sig.params.iter()) {
                let tc = type_to_tc(param_ty);
                lowered_args.push(ctx.typecheck_pure::<MethodBodyExt>(arg, tc, None)?);
            }
            Ok(final_ast::AssignRhs::MethodCall(Call {
                name: Ident(call_name),
                args: lowered_args,
            }))
        }
    }
}

fn lower_stmt_block(
    stmts: &mut [silver::Statement],
    ctx: &mut LocalEnv,
) -> Result<Vec<final_ast::Statement>, TypeError> {
    stmts.iter_mut().map(|s| lower_statement(s, ctx)).collect()
}

// ==========================================
// 11. Declaration-level functions
// ==========================================

fn typecheck_field(field: &silver::Field) -> final_ast::Declaration {
    final_ast::Declaration::Field(final_ast::Field(TypedIdent {
        name: Ident(field.0.idn.0.id()),
        ty: Type::from(&field.0.ty),
    }))
}

fn collect_params(args: &[silver::ArgOrType]) -> Vec<TypedIdent> {
    args.iter()
        .filter_map(|p| {
            p.idn().map(|idn| TypedIdent {
                name: Ident(idn.0.id()),
                ty: Type::from(p.ty()),
            })
        })
        .collect()
}

fn add_arg_locals(ctx: &mut LocalEnv, args: &[silver::ArgOrType]) -> Result<(), TypeError> {
    for arg in args {
        if let silver::ArgOrType::Arg(decl) = arg {
            ctx.add_local(decl.idn.0.id(), Type::from(&decl.ty))?;
        }
    }
    Ok(())
}

fn typecheck_predicate(
    pred: &mut silver::Predicate,
    globals: &Globals,
    interner: &Interner,
) -> Result<final_ast::Declaration, TypeError> {
    let name = Ident(pred.signature.name.0.id());
    let params = collect_params(&pred.signature.args);

    let mut ctx = LocalEnv::new(globals, interner);
    add_arg_locals(&mut ctx, &pred.signature.args)?;

    let body = pred
        .body
        .as_mut()
        .map(|b| ctx.typecheck_spatial::<!>(&mut b.0))
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
    let func_spur = func.signature.name.0.id();
    let name = Ident(func_spur);
    let params = collect_params(&func.signature.args);
    let ret_ty = globals
        .resolve(func_spur)
        .and_then(|s| s.as_function())
        .map(|sig| sig.ret.clone())
        .ok_or_else(|| {
            TypeError::Other(format!(
                "internal: function `{}` not in globals",
                interner.resolve(&func_spur)
            ))
        })?;

    let mut ctx = LocalEnv::new(globals, interner);
    add_arg_locals(&mut ctx, &func.signature.args)?;

    let requires = combine_spatial::<!>(&mut func.contract.precondition, &ctx)?;

    // Body cannot mention `result` (only postconditions can): pass None.
    let body = func
        .body
        .as_mut()
        .map(|b| ctx.typecheck_pure::<!>(&mut b.0, type_to_tc(&ret_ty), None))
        .transpose()?;

    // Postconditions enable `result`, typed as the return type.
    let ensures = {
        let mut iter = func.contract.postcondition.iter_mut();
        match iter.next() {
            None => None,
            Some(e) => {
                let first =
                    ctx.typecheck_pure::<FuncEnsuresExt>(e, SilverTcType::Bool, Some(ret_ty.clone()))?;
                let combined = iter.try_fold(first, |acc, e| {
                    let next = ctx.typecheck_pure::<FuncEnsuresExt>(
                        e,
                        SilverTcType::Bool,
                        Some(ret_ty.clone()),
                    )?;
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

    let mut ctx = LocalEnv::new(globals, interner);

    // Collect all label names from the body before processing anything.
    if let Some(body) = &method.body {
        collect_labels(&body.0, &mut ctx.labels);
    }

    add_arg_locals(&mut ctx, &method.signature.args)?;

    let requires = combine_spatial::<!>(&mut method.contract.precondition, &ctx)?;

    add_arg_locals(&mut ctx, &method.signature.ret)?;

    let ensures = combine_spatial::<MethodEnsuresExt>(&mut method.contract.postcondition, &ctx)?;

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
        self, disambiguator::disambiguate, globals::GlobalsCollector,
        interner::IdentCollector, r#macro::inline_macros, silver_parser, walk::AstWalkable,
    };

    fn run_pipeline(input: &str) -> Result<final_ast::Program, Vec<TypeError>> {
        let mut program = silver_parser::sil_program(input).expect("parse failed");
        let mut ident_collector = IdentCollector::default();
        program.walk_mut(&mut ident_collector);
        let interner = ident_collector.finalize();
        let mut globals_collector = GlobalsCollector::new(&interner);
        program.walk(&mut globals_collector);
        let globals = globals_collector.finalize().expect("globals error");
        disambiguate(&mut program, &interner, &globals).expect("disambiguation failed");
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
        // Rusttyc catches this as a constraint error (Bool cannot meet Numeric).
        assert!(
            result
                .as_ref()
                .is_err_and(|errs| errs.iter().any(|e| matches!(e, TypeError::Tc(_)))),
            "expected type constraint error, got: {result:?}"
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

    #[test]
    fn let_in_sibling_scopes_same_name_ok() {
        let result = run_pipeline(
            r#"
function f(x: Int): Int
{ (let a == (3) in a) + (let a == (3) in a) }
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
    }

    #[test]
    fn let_in_nested_same_name_is_error() {
        let result = run_pipeline(
            r#"
function f(x: Int): Int
{ let a == (3) in (let a == (3) in a) }
"#,
        );
        assert!(
            result
                .as_ref()
                .is_err_and(|errs| errs.iter().any(|e| matches!(e, TypeError::ShadowedName(_)))),
            "expected ShadowedName, got: {result:?}"
        );
    }

    #[test]
    fn let_in_shadows_param_is_error() {
        let result = run_pipeline(
            r#"
function f(x: Int): Int
{ let x == (3) in x }
"#,
        );
        assert!(
            result
                .as_ref()
                .is_err_and(|errs| errs.iter().any(|e| matches!(e, TypeError::ShadowedName(_)))),
            "expected ShadowedName, got: {result:?}"
        );
    }

    #[test]
    fn expr_rhs_multi_lhs_is_error() {
        let result = run_pipeline(
            r#"
method test()
{
  var x: Int
  var y: Int
  x, y := 1
}
"#,
        );
        assert!(
            result
                .as_ref()
                .is_err_and(|errs| errs
                    .iter()
                    .any(|e| matches!(e, TypeError::WrongReturnCount { expected: 1, found: 2 }))),
            "expected WrongReturnCount, got: {result:?}"
        );
    }

    #[test]
    fn new_rhs_multi_lhs_is_error() {
        let result = run_pipeline(
            r#"
method test()
{
  var x: Ref
  var y: Ref
  x, y := new(*)
}
"#,
        );
        assert!(
            result
                .as_ref()
                .is_err_and(|errs| errs
                    .iter()
                    .any(|e| matches!(e, TypeError::WrongReturnCount { expected: 1, found: 2 }))),
            "expected WrongReturnCount, got: {result:?}"
        );
    }

    #[test]
    fn method_call_too_few_returns_is_error() {
        let result = run_pipeline(
            r#"
method m(x: Int) returns (r: Int)

method test(a: Int)
{
  var x: Int
  var y: Int
  x, y := m(a)
}
"#,
        );
        assert!(
            result
                .as_ref()
                .is_err_and(|errs| errs
                    .iter()
                    .any(|e| matches!(e, TypeError::WrongReturnCount { expected: 1, found: 2 }))),
            "expected WrongReturnCount, got: {result:?}"
        );
    }

    #[test]
    fn method_call_multi_return_correct_count_is_ok() {
        let result = run_pipeline(
            r#"
method m(x: Int) returns (r: Int, s: Int)

method test(a: Int)
{
  var x: Int
  var y: Int
  x, y := m(a)
}
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
    }
}
