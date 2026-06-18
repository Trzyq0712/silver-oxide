use lasso::Spur;
use rusttyc::{TcKey, TypeChecker, VarlessTypeChecker};
use std::collections::{HashMap, HashSet};

use crate::viper::{
    self,
    globals::{GlobalSignature, Globals},
    interner::Interner,
    typed::{
        self, BinOp, Call, FuncEnsuresExt, Ident, Literal, MethodBodyExt, MethodEnsuresExt,
        PredicateWithPerm, PureExpKind, ResourceExp, ResourceExpKind, SpatialExp, SpatialExpKind,
        Type, TypedIdent, TypedPureExp, UnOp,
    },
};

mod error;
mod lattice;

pub use error::TypeError;
use lattice::{ViperTcType, type_to_tc};

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

    /// Typecheck a pure expression and lower it to `typed`.
    /// `result_ty` enables the `result` keyword (function postconditions); pass `None`
    /// for methods, predicates, and function bodies.
    fn typecheck_pure<Ext: PureExt>(
        &self,
        exp: &mut viper::Exp,
        expected: &Type,
        result_ty: Option<Type>,
    ) -> Result<TypedPureExp<Ext>, TypeError> {
        let mut c = ConstraintCtx::new(self, result_ty);
        let root = c.constrain_pure(exp)?;
        // Impose the expected type with full structure (including any `Domain`
        // type arguments) so a nested mismatch (e.g. `Option[Int]` vs
        // `Option[Bool]`) is caught at the root.
        c.impose_type(root, expected, &HashMap::new())?;
        let table = c.tc.type_check().map_err(TypeError::from)?;
        LoweringCtx::new(self, &table).lower_pure::<Ext>(exp)
    }

    /// Typecheck a spatial (assertion) expression and lower it to `typed`.
    fn typecheck_spatial<Ext: PureExt>(
        &self,
        exp: &mut viper::Exp,
    ) -> Result<SpatialExp<Ext>, TypeError> {
        let mut c = ConstraintCtx::new(self, None);
        c.constrain_spatial(exp)?;
        let table = c.tc.type_check().map_err(TypeError::from)?;
        LoweringCtx::new(self, &table).lower_spatial::<Ext>(exp)
    }

    /// Typecheck a `acc(pred(..), perm)` location used by fold/unfold.
    fn typecheck_pred_with_perm<Ext: PureExt>(
        &self,
        acc: &mut viper::AccExp,
    ) -> Result<PredicateWithPerm<Ext>, TypeError> {
        let mut c = ConstraintCtx::new(self, None);
        c.constrain_resource(&mut acc.loc)?;
        let pk = c.constrain_pure(&mut acc.perm)?;
        c.tc.impose(pk.concretizes_explicit(ViperTcType::Numeric))?;
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

/// Phase 1: constraint generation. Walks `viper::Exp`, stamps a fresh `TcKey` onto every
/// pure node (`exp.ty = Infer(key)`), and feeds rules into the `rusttyc` solver. Produces
/// no `typed`; that is the lowering phase's job.
struct ConstraintCtx<'a, 'g> {
    env: &'a LocalEnv<'g>,
    tc: VarlessTypeChecker<ViperTcType>,
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

/// Phase 3: lowering. Reads the solved `TypeTable` and maps each `viper::Exp` into a
/// `typed` node in one immutable pass. Stateless w.r.t. binders: every node's type is
/// fetched from its stamped `TcKey`, so let/quantifier bindings need no bookkeeping here.
struct LoweringCtx<'a, 'g> {
    env: &'a LocalEnv<'g>,
    table: &'a TypeTable,
}

impl<'a, 'g> LoweringCtx<'a, 'g> {
    fn new(env: &'a LocalEnv<'g>, table: &'a TypeTable) -> Self {
        Self { env, table }
    }

    fn resolved_ty(&self, exp: &viper::Exp) -> Result<Type, TypeError> {
        match exp.ty {
            viper::InferenceType::Infer(k) => self
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

fn lower_ident(ident: &viper::Ident) -> Ident {
    Ident(ident.id())
}

/// Collect the distinct `Generic` type-parameter names occurring in `ty`
/// (recursing into `Domain` type arguments), preserving first-seen order.
fn collect_generics(ty: &Type, acc: &mut Vec<Spur>) {
    match ty {
        Type::Generic(id) => {
            if !acc.contains(&id.0) {
                acc.push(id.0);
            }
        }
        Type::Domain(_, args) => {
            for a in args {
                collect_generics(a, acc);
            }
        }
        _ => {}
    }
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
    exps: &mut [viper::Exp],
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
    fn constrain_pure(&mut self, exp: &mut viper::Exp) -> Result<TcKey, TypeError> {
        use viper::ExpKind;

        let key = self.tc.new_term_key();
        exp.ty = viper::InferenceType::Infer(key);

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
                    self.impose_type(key, &ty, &HashMap::new())?;
                }
            }

            ExpKind::Result => {
                let ty = self
                    .result_ty
                    .clone()
                    .ok_or(TypeError::IllegalResultUsage)?;
                self.impose_type(key, &ty, &HashMap::new())?;
            }

            ExpKind::Old(_label, inner) => {
                let inner_key = self.constrain_pure(inner)?;
                self.tc.impose(key.equate_with(inner_key))?;
            }

            ExpKind::Ascribe(inner, ascribed_ty) => {
                let target = Type::from(&*ascribed_ty);
                let inner_key = self.constrain_pure(inner)?;
                self.impose_type(inner_key, &target, &HashMap::new())?;
                self.impose_type(key, &target, &HashMap::new())?;
            }

            ExpKind::UnOp(op, inner) => self.constrain_unop(op, inner, key)?,

            ExpKind::BinOp(op, left, right) => self.constrain_binop(op, left, right, key)?,

            ExpKind::Ternary(cond, then, else_) => {
                let cond_key = self.constrain_pure(cond)?;
                self.tc
                    .impose(cond_key.concretizes_explicit(ViperTcType::Bool))?;
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

            ExpKind::HeapUpdate(viper::HeapUpdateOp::Unfold, acc_exp, body) => {
                self.constrain_resource(&mut acc_exp.loc)?;
                self.constrain_pure(&mut acc_exp.perm)?;
                let body_key = self.constrain_pure(body)?;
                self.tc.impose(key.equate_with(body_key))?;
            }

            ExpKind::AdtDestructor(base, field) => {
                // `e.f`: `e` must be the ADT owning destructor `f`; the result is
                // the field's type.
                let fid = field.id();
                let (adt, field_ty) = {
                    let info = self.env.globals.dtor_by_name.get(&fid).ok_or_else(|| {
                        TypeError::Other(format!(
                            "unknown ADT destructor: {}",
                            self.env.interner.resolve(&fid)
                        ))
                    })?;
                    (info.adt, info.ty.clone())
                };
                let (arity, adt_params) = {
                    let sig = self.env.globals.resolve(adt).and_then(|s| s.as_adt());
                    match sig {
                        Some(s) => (s.type_arity, s.params.clone()),
                        None => (0, Vec::new()),
                    }
                };
                let base_key = self.constrain_pure(base)?;
                self.tc.impose(
                    base_key.concretizes_explicit(ViperTcType::Domain(Ident(adt), arity)),
                )?;
                // Map each of the ADT's type parameters to the scrutinee's
                // corresponding type argument (its `i`-th child), so a generic
                // field type `T` resolves to the concrete instantiation.
                let mut subst = HashMap::new();
                for (i, pname) in adt_params.iter().enumerate() {
                    let child = self.tc.get_child_key(base_key, i)?;
                    subst.insert(*pname, child);
                }
                self.impose_type(key, &field_ty, &subst)?;
            }

            ExpKind::AdtDiscriminator(base, variant) => {
                // `e.is<Ctor>`: `e` must be the ADT owning `Ctor`; result is Bool.
                let vid = variant.id();
                let adt = {
                    let sym = self.env.globals.resolve(vid).ok_or_else(|| {
                        TypeError::Other(format!(
                            "unknown ADT constructor in discriminator: {}",
                            self.env.interner.resolve(&vid)
                        ))
                    })?;
                    sym.as_adt_constructor()
                        .ok_or_else(|| {
                            TypeError::Other(format!(
                                "{} is not an ADT constructor",
                                self.env.interner.resolve(&vid)
                            ))
                        })?
                        .adt
                };
                let arity = self
                    .env
                    .globals
                    .resolve(adt)
                    .and_then(|s| s.as_adt())
                    .map_or(0, |s| s.type_arity);
                let base_key = self.constrain_pure(base)?;
                self.tc.impose(
                    base_key.concretizes_explicit(ViperTcType::Domain(Ident(adt), arity)),
                )?;
                self.tc
                    .impose(key.concretizes_explicit(ViperTcType::Bool))?;
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
                self.tc
                    .impose(body_key.concretizes_explicit(ViperTcType::Bool))?;
                self.tc
                    .impose(key.concretizes_explicit(ViperTcType::Bool))?;
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
        op: &viper::UnOp,
        inner: &mut viper::Exp,
        key: TcKey,
    ) -> Result<(), TypeError> {
        match op {
            viper::UnOp::Not => {
                let inner_key = self.constrain_pure(inner)?;
                self.tc
                    .impose(inner_key.concretizes_explicit(ViperTcType::Bool))?;
                self.tc
                    .impose(key.concretizes_explicit(ViperTcType::Bool))?;
            }
            viper::UnOp::Neg => {
                let inner_key = self.constrain_pure(inner)?;
                self.tc
                    .impose(inner_key.concretizes_explicit(ViperTcType::Numeric))?;
                self.tc.impose(key.equate_with(inner_key))?;
            }
            viper::UnOp::Perm => {
                self.constrain_resource(inner)?;
                self.tc
                    .impose(key.concretizes_explicit(ViperTcType::Real))?;
            }
        }
        Ok(())
    }

    fn constrain_binop(
        &mut self,
        op: &viper::BinOp,
        left: &mut viper::Exp,
        right: &mut viper::Exp,
        key: TcKey,
    ) -> Result<(), TypeError> {
        use viper::BinOp as SBinOp;

        let lk = self.constrain_pure(left)?;
        let rk = self.constrain_pure(right)?;

        match op {
            SBinOp::And | SBinOp::Or | SBinOp::Implies | SBinOp::Iff => {
                self.tc.impose(lk.concretizes_explicit(ViperTcType::Bool))?;
                self.tc.impose(rk.concretizes_explicit(ViperTcType::Bool))?;
                self.tc
                    .impose(key.concretizes_explicit(ViperTcType::Bool))?;
            }
            SBinOp::Eq | SBinOp::Neq => {
                self.tc.impose(lk.equate_with(rk))?;
                self.tc
                    .impose(key.concretizes_explicit(ViperTcType::Bool))?;
            }
            SBinOp::Lt | SBinOp::Le | SBinOp::Gt | SBinOp::Ge => {
                self.tc
                    .impose(lk.concretizes_explicit(ViperTcType::Numeric))?;
                self.tc
                    .impose(rk.concretizes_explicit(ViperTcType::Numeric))?;
                self.tc.impose(lk.equate_with(rk))?;
                self.tc
                    .impose(key.concretizes_explicit(ViperTcType::Bool))?;
            }
            SBinOp::Plus | SBinOp::Minus | SBinOp::Mult | SBinOp::Mod => {
                self.tc
                    .impose(lk.concretizes_explicit(ViperTcType::Numeric))?;
                self.tc
                    .impose(rk.concretizes_explicit(ViperTcType::Numeric))?;
                self.tc.impose(key.is_sym_meet_of(lk, rk))?;
            }
            SBinOp::Div => {
                self.tc
                    .impose(lk.concretizes_explicit(ViperTcType::Numeric))?;
                self.tc
                    .impose(rk.concretizes_explicit(ViperTcType::Numeric))?;
                self.tc
                    .impose(key.concretizes_explicit(ViperTcType::Numeric))?;
            }
            _ => {
                return Err(TypeError::Other(format!(
                    "unsupported binary operator: {op:?}"
                )));
            }
        }
        Ok(())
    }

    /// Impose that `key` has type `ty`, recursing into a `Domain`'s type
    /// arguments as `rusttyc` children. `subst` instantiates the free type
    /// parameters (`Generic`) of a generic signature: each is bound to a fresh
    /// type-variable key, so e.g. `Some(value: T): Option[T]` unifies `T` with
    /// the argument and propagates it to the result. A non-generic context
    /// passes an empty `subst`.
    fn impose_type(
        &mut self,
        key: TcKey,
        ty: &Type,
        subst: &HashMap<Spur, TcKey>,
    ) -> Result<(), TypeError> {
        match ty {
            Type::Bool => self
                .tc
                .impose(key.concretizes_explicit(ViperTcType::Bool))?,
            Type::Int => self.tc.impose(key.concretizes_explicit(ViperTcType::Int))?,
            Type::Real => self
                .tc
                .impose(key.concretizes_explicit(ViperTcType::Real))?,
            Type::Ref => self.tc.impose(key.concretizes_explicit(ViperTcType::Ref))?,
            Type::Generic(id) => {
                let var = subst.get(&id.0).copied().ok_or_else(|| {
                    TypeError::UnboundTypeParam(self.env.interner.resolve(&id.0).to_string())
                })?;
                if var != key {
                    self.tc.impose(key.equate_with(var))?;
                }
            }
            Type::Domain(id, args) => {
                self.tc
                    .impose(key.concretizes_explicit(ViperTcType::Domain(*id, args.len())))?;
                for (i, arg) in args.iter().enumerate() {
                    let child = self.tc.get_child_key(key, i)?;
                    self.impose_type(child, arg, subst)?;
                }
            }
            // Built-in collections are not yet modelled in the lattice; leave
            // the key unconstrained (Top) as before.
            Type::Collection(_) => {}
        }
        Ok(())
    }

    /// Instantiate the free type parameters of a callee signature: a fresh
    /// type-variable key per distinct `Generic` name occurring in `tys`.
    fn instantiate_generics(&mut self, tys: &[Type]) -> HashMap<Spur, TcKey> {
        let mut names = Vec::new();
        for ty in tys {
            collect_generics(ty, &mut names);
        }
        names
            .into_iter()
            .map(|n| (n, self.tc.new_term_key()))
            .collect()
    }

    fn constrain_call(
        &mut self,
        call: &mut viper::Call<viper::ExpCallKind>,
        key: TcKey,
    ) -> Result<(), TypeError> {
        use viper::ExpCallKind;
        let call_name = call.name.id();
        let sym = self.env.globals.resolve(call_name).ok_or_else(|| {
            TypeError::UndefinedVariable(self.env.interner.resolve(&call_name).to_string())
        })?;

        match call.kind.as_ref().expect("call kind must be resolved") {
            ExpCallKind::Predicate => Err(TypeError::PredicateInPureContext(
                self.env.interner.resolve(&call_name).to_string(),
            )),
            ExpCallKind::Function | ExpCallKind::AdtConstructor => {
                let (params, ret_ty) = match sym.signature() {
                    GlobalSignature::Function(s) => (s.params.clone(), s.ret.clone()),
                    GlobalSignature::AdtConstructor(s) => (s.params.clone(), s.ret.clone()),
                    _ => {
                        return Err(TypeError::Other(format!(
                            "{} is not callable",
                            self.env.interner.resolve(&call_name)
                        )));
                    }
                };
                if params.len() != call.args.len() {
                    return Err(TypeError::WrongArgCount {
                        name: self.env.interner.resolve(&call_name).to_string(),
                        expected: params.len(),
                        found: call.args.len(),
                    });
                }
                // Instantiate the callee's free type parameters with fresh
                // type variables (empty for a monomorphic signature), then
                // unify args and result against the substituted signature.
                let mut sig_tys = params.clone();
                sig_tys.push(ret_ty.clone());
                let subst = self.instantiate_generics(&sig_tys);
                for (arg, expected) in call.args.iter_mut().zip(params.iter()) {
                    let arg_key = self.constrain_pure(arg)?;
                    self.impose_type(arg_key, expected, &subst)?;
                }
                self.impose_type(key, &ret_ty, &subst)?;
                Ok(())
            }
            ExpCallKind::Macro => Err(TypeError::Other(
                "macro in expression (should have been inlined)".to_string(),
            )),
        }
    }

    fn constrain_field(
        &mut self,
        base: &mut viper::Exp,
        field_name: &viper::Ident,
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
        self.tc
            .impose(base_key.concretizes_explicit(ViperTcType::Ref))?;
        self.impose_type(key, &ret_ty, &HashMap::new())?;
        Ok(())
    }

    fn constrain_resource(&mut self, exp: &mut viper::Exp) -> Result<(), TypeError> {
        match exp.kind.as_mut() {
            viper::ExpKind::Field(base, _field_name) => {
                let base_key = self.constrain_pure(base)?;
                self.tc
                    .impose(base_key.concretizes_explicit(ViperTcType::Ref))?;
                Ok(())
            }
            viper::ExpKind::Call(call) => match call.kind.as_ref().expect("call kind resolved") {
                viper::ExpCallKind::Predicate => self.constrain_predicate_resource(call),
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
        call: &mut viper::Call<viper::ExpCallKind>,
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
            self.impose_type(arg_key, expected, &HashMap::new())?;
        }
        Ok(())
    }

    fn constrain_spatial(&mut self, exp: &mut viper::Exp) -> Result<(), TypeError> {
        use viper::ExpKind;

        // A bare predicate call in assertion position is shorthand for full permission.
        if let ExpKind::Call(call) = exp.kind.as_mut() {
            if matches!(call.kind, Some(viper::ExpCallKind::Predicate)) {
                return self.constrain_predicate_resource(call);
            }
        }

        match exp.kind.as_mut() {
            ExpKind::Acc(acc_exp) => {
                self.constrain_resource(&mut acc_exp.loc)?;
                let perm_key = self.constrain_pure(&mut acc_exp.perm)?;
                self.tc
                    .impose(perm_key.concretizes_explicit(ViperTcType::Numeric))?;
                Ok(())
            }
            ExpKind::BinOp(viper::BinOp::And | viper::BinOp::InhaleExhale, l, r) => {
                self.constrain_spatial(l)?;
                self.constrain_spatial(r)
            }
            ExpKind::BinOp(viper::BinOp::Implies, l, r) => {
                let cond_key = self.constrain_pure(l)?;
                self.tc
                    .impose(cond_key.concretizes_explicit(ViperTcType::Bool))?;
                self.constrain_spatial(r)
            }
            ExpKind::Ternary(cond, then, else_) => {
                let cond_key = self.constrain_pure(cond)?;
                self.tc
                    .impose(cond_key.concretizes_explicit(ViperTcType::Bool))?;
                self.constrain_spatial(then)?;
                self.constrain_spatial(else_)
            }
            _ => {
                let pure_key = self.constrain_pure(exp)?;
                self.tc
                    .impose(pure_key.concretizes_explicit(ViperTcType::Bool))?;
                Ok(())
            }
        }
    }
}

// ==========================================
// 8. Phase 3 — lowering to typed
// ==========================================

impl<'a, 'g> LoweringCtx<'a, 'g> {
    fn lower_pure<Ext: PureExt>(&self, exp: &viper::Exp) -> Result<TypedPureExp<Ext>, TypeError> {
        let ty = self.resolved_ty(exp)?;
        let kind = self.lower_pure_kind::<Ext>(exp)?;
        Ok(TypedPureExp {
            ty,
            exp: Box::new(kind),
        })
    }

    fn lower_pure_kind<Ext: PureExt>(
        &self,
        exp: &viper::Exp,
    ) -> Result<PureExpKind<Ext>, TypeError> {
        use viper::ExpKind;

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

            ExpKind::HeapUpdate(viper::HeapUpdateOp::Unfold, acc_exp, body) => {
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

            // Quantifiers emitted as bool constant (proper typed support later).
            ExpKind::Quantifier(..) => Ok(PureExpKind::Const(Literal::Bool(true))),

            _ => Err(TypeError::Other(format!(
                "unsupported pure expression: {:?}",
                exp.kind
            ))),
        }
    }

    fn lower_unop<Ext: PureExt>(
        &self,
        op: &viper::UnOp,
        inner: &viper::Exp,
    ) -> Result<PureExpKind<Ext>, TypeError> {
        match op {
            viper::UnOp::Not => Ok(PureExpKind::Unary(
                UnOp::Not,
                self.lower_pure::<Ext>(inner)?,
            )),
            viper::UnOp::Neg => Ok(PureExpKind::Unary(
                UnOp::Neg,
                self.lower_pure::<Ext>(inner)?,
            )),
            viper::UnOp::Perm => {
                let resource = self.lower_resource::<Ext>(inner)?;
                Ok(PureExpKind::Ext(Ext::lower_perm(resource)?))
            }
        }
    }

    fn lower_call<Ext: PureExt>(
        &self,
        call: &viper::Call<viper::ExpCallKind>,
    ) -> Result<PureExpKind<Ext>, TypeError> {
        use viper::ExpCallKind;
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
        exp: &viper::Exp,
    ) -> Result<ResourceExp<Ext>, TypeError> {
        match &*exp.kind {
            viper::ExpKind::Field(base, field_name) => {
                let base_exp = self.lower_pure::<Ext>(base)?;
                Ok(ResourceExp(Box::new(ResourceExpKind::Field(
                    base_exp,
                    Ident(field_name.id()),
                ))))
            }
            viper::ExpKind::Call(call) => match call.kind.as_ref().expect("call kind resolved") {
                viper::ExpCallKind::Predicate => self.lower_predicate_resource::<Ext>(call),
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
        call: &viper::Call<viper::ExpCallKind>,
    ) -> Result<ResourceExp<Ext>, TypeError> {
        let mut args = Vec::with_capacity(call.args.len());
        for arg in call.args.iter() {
            args.push(self.lower_pure::<Ext>(arg)?);
        }
        Ok(ResourceExp(Box::new(ResourceExpKind::PredicateCall(
            Call {
                name: Ident(call.name.id()),
                args,
            },
        ))))
    }

    fn lower_spatial<Ext: PureExt>(&self, exp: &viper::Exp) -> Result<SpatialExp<Ext>, TypeError> {
        use viper::ExpKind;

        if let ExpKind::Call(call) = &*exp.kind {
            if matches!(call.kind, Some(viper::ExpCallKind::Predicate)) {
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
                Ok(SpatialExp(Box::new(SpatialExpKind::Acc(
                    resource, perm_exp,
                ))))
            }

            ExpKind::BinOp(viper::BinOp::And | viper::BinOp::InhaleExhale, l, r) => {
                let ls = self.lower_spatial::<Ext>(l)?;
                let rs = self.lower_spatial::<Ext>(r)?;
                Ok(SpatialExp(Box::new(SpatialExpKind::Conj(ls, rs))))
            }

            ExpKind::BinOp(viper::BinOp::Implies, l, r) => {
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

/// Type of a literal, used during constraint generation (no `typed` produced).
fn const_type(c: &viper::ConstKind) -> Type {
    match c {
        viper::ConstKind::Bool(_) => Type::Bool,
        viper::ConstKind::Int(_) => Type::Int,
        viper::ConstKind::Real(_) | viper::ConstKind::Wildcard | viper::ConstKind::Epsilon => {
            Type::Real
        }
        viper::ConstKind::Null => Type::Ref,
    }
}

fn lower_const_literal(c: &viper::ConstKind) -> Literal {
    match c {
        viper::ConstKind::Bool(b) => Literal::Bool(*b),
        viper::ConstKind::Int(i) => Literal::Int(i.clone()),
        viper::ConstKind::Real(r) => Literal::Real(r.clone()),
        viper::ConstKind::Null => Literal::Null,
        viper::ConstKind::Wildcard => Literal::Wildcard,
        viper::ConstKind::Epsilon => Literal::Real(num::BigRational::new(
            num::BigInt::from(0),
            num::BigInt::from(1),
        )),
    }
}

fn lower_bin_op(op: &viper::BinOp) -> BinOp {
    use viper::BinOp as S;
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

fn collect_labels(stmts: &[viper::Statement], labels: &mut HashSet<Spur>) {
    for stmt in stmts {
        match stmt {
            viper::Statement::Label(decl, _) => {
                labels.insert(decl.0.id());
            }
            viper::Statement::Block(block) => {
                collect_labels(&block.0, labels);
            }
            _ => {}
        }
    }
}

fn lower_statement(
    stmt: &mut viper::Statement,
    ctx: &mut LocalEnv,
) -> Result<typed::Statement, TypeError> {
    use viper::Statement as S;
    match stmt {
        S::Assume(e) => Ok(typed::Statement::Assume(ctx.typecheck_spatial(e)?)),
        S::Assert(e) => Ok(typed::Statement::Assert(ctx.typecheck_spatial(e)?)),
        S::Refute(e) => Ok(typed::Statement::Refute(ctx.typecheck_spatial(e)?)),
        S::Inhale(e) => Ok(typed::Statement::Inhale(ctx.typecheck_spatial(e)?)),
        S::Exhale(e) => Ok(typed::Statement::Exhale(ctx.typecheck_spatial(e)?)),

        S::Fold(acc) => Ok(typed::Statement::Fold(ctx.typecheck_pred_with_perm(acc)?)),
        S::Unfold(acc) => Ok(typed::Statement::Unfold(ctx.typecheck_pred_with_perm(acc)?)),

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
            Ok(typed::Statement::Var(typed_decls, lowered_rhs))
        }

        S::Assign(lhs_list, rhs) => {
            // Lower LHS first — concrete types, never generic
            let lowered_lhs_typed: Vec<(typed::AssignLhs, Type)> = lhs_list
                .iter_mut()
                .map(|lhs| lower_assign_lhs_typed(lhs, ctx))
                .collect::<Result<_, _>>()?;
            let lhs_types: Vec<Type> = lowered_lhs_typed.iter().map(|(_, ty)| ty.clone()).collect();
            let lowered_rhs = lower_rhs_against_lhs(rhs, ctx, &lhs_types)?;
            let lowered_lhs = lowered_lhs_typed.into_iter().map(|(lhs, _)| lhs).collect();
            Ok(typed::Statement::Assign(lowered_lhs, lowered_rhs))
        }

        S::Block(block) => {
            let stmts = lower_stmt_block(&mut block.0, ctx)?;
            Ok(typed::Statement::Block(typed::StmtBlock(stmts)))
        }

        // A `label L` marks the current heap state; its name was already
        // collected by `collect_labels` for `old[L]` validation. Invariants on
        // the label are loop-related and out of scope (ignored).
        S::Label(decl, _invs) => Ok(typed::Statement::Label(decl.0.id())),

        S::If(..) | S::While(..) | S::Goto(..) => Err(TypeError::Other(
            "statement not yet supported in initial scope".to_string(),
        )),
    }
}

fn lower_assign_lhs_typed(
    lhs: &mut viper::AssignLhs,
    ctx: &mut LocalEnv,
) -> Result<(typed::AssignLhs, Type), TypeError> {
    match lhs {
        viper::AssignLhs::Ident(ident) => {
            let spur = ident.id();
            let ty = ctx.locals.get(&spur).cloned().ok_or_else(|| {
                TypeError::UndefinedVariable(ctx.interner.resolve(&spur).to_string())
            })?;
            Ok((typed::AssignLhs::Var(Ident(spur)), ty))
        }
        viper::AssignLhs::Field(base, field) => {
            let field_id = field.id();
            let field_ty = ctx
                .globals
                .resolve(field_id)
                .and_then(|s| s.as_field())
                .cloned()
                .ok_or_else(|| TypeError::Other("undefined field".to_string()))?;
            let base_exp = ctx.typecheck_pure::<MethodBodyExt>(base, &Type::Ref, None)?;
            Ok((typed::AssignLhs::Field(base_exp, Ident(field_id)), field_ty))
        }
    }
}

/// Lower an assignment/var-init RHS, validating and constraining against `lhs_types`.
/// Expression RHS: constrained to `lhs_types[0]` (must be single).
/// New RHS: requires single `Ref` LHS.
/// Method call RHS: arg and return types checked against signature.
fn lower_rhs_against_lhs(
    rhs: &mut viper::AssignRhs,
    ctx: &mut LocalEnv,
    lhs_types: &[Type],
) -> Result<typed::AssignRhs, TypeError> {
    match rhs {
        viper::AssignRhs::Exp(e) => {
            if lhs_types.len() != 1 {
                return Err(TypeError::WrongReturnCount {
                    expected: 1,
                    found: lhs_types.len(),
                });
            }
            let exp = ctx.typecheck_pure::<MethodBodyExt>(e, &lhs_types[0], None)?;
            Ok(typed::AssignRhs::Exp(exp))
        }

        viper::AssignRhs::New(fields) => {
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
                viper::StarOrNames::Star => typed::StarOrFields::Star,
                viper::StarOrNames::Names(names) => {
                    typed::StarOrFields::Fields(names.iter().map(|n| Ident(n.id())).collect())
                }
            };
            Ok(typed::AssignRhs::New(star_or_fields))
        }

        viper::AssignRhs::Call(call) => {
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
                lowered_args.push(ctx.typecheck_pure::<MethodBodyExt>(arg, param_ty, None)?);
            }
            Ok(typed::AssignRhs::MethodCall(Call {
                name: Ident(call_name),
                args: lowered_args,
            }))
        }
    }
}

fn lower_stmt_block(
    stmts: &mut [viper::Statement],
    ctx: &mut LocalEnv,
) -> Result<Vec<typed::Statement>, TypeError> {
    stmts.iter_mut().map(|s| lower_statement(s, ctx)).collect()
}

// ==========================================
// 11. Declaration-level functions
// ==========================================

fn typecheck_field(field: &viper::Field) -> typed::Declaration {
    typed::Declaration::Field(typed::Field(TypedIdent {
        name: Ident(field.0.idn.0.id()),
        ty: Type::from(&field.0.ty),
    }))
}

fn collect_params(args: &[viper::ArgOrType]) -> Vec<TypedIdent> {
    args.iter()
        .filter_map(|p| {
            p.idn().map(|idn| TypedIdent {
                name: Ident(idn.0.id()),
                ty: Type::from(p.ty()),
            })
        })
        .collect()
}

fn add_arg_locals(ctx: &mut LocalEnv, args: &[viper::ArgOrType]) -> Result<(), TypeError> {
    for arg in args {
        if let viper::ArgOrType::Arg(decl) = arg {
            ctx.add_local(decl.idn.0.id(), Type::from(&decl.ty))?;
        }
    }
    Ok(())
}

fn typecheck_predicate(
    pred: &mut viper::Predicate,
    globals: &Globals,
    interner: &Interner,
) -> Result<typed::Declaration, TypeError> {
    let name = Ident(pred.signature.name.0.id());
    let params = collect_params(&pred.signature.args);

    let mut ctx = LocalEnv::new(globals, interner);
    add_arg_locals(&mut ctx, &pred.signature.args)?;

    let body = pred
        .body
        .as_mut()
        .map(|b| ctx.typecheck_spatial::<!>(&mut b.0))
        .transpose()?;

    Ok(typed::Declaration::Predicate(typed::Predicate {
        name,
        params,
        body,
    }))
}

fn typecheck_function(
    func: &mut viper::Function,
    globals: &Globals,
    interner: &Interner,
) -> Result<typed::Declaration, TypeError> {
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
        .map(|b| ctx.typecheck_pure::<!>(&mut b.0, &ret_ty, None))
        .transpose()?;

    // Postconditions enable `result`, typed as the return type.
    let ensures = {
        let mut iter = func.contract.postcondition.iter_mut();
        match iter.next() {
            None => None,
            Some(e) => {
                let first =
                    ctx.typecheck_pure::<FuncEnsuresExt>(e, &Type::Bool, Some(ret_ty.clone()))?;
                let combined = iter.try_fold(first, |acc, e| {
                    let next =
                        ctx.typecheck_pure::<FuncEnsuresExt>(e, &Type::Bool, Some(ret_ty.clone()))?;
                    Ok::<_, TypeError>(TypedPureExp {
                        ty: Type::Bool,
                        exp: Box::new(PureExpKind::Binary(BinOp::And, acc, next)),
                    })
                })?;
                Some(combined)
            }
        }
    };

    Ok(typed::Declaration::Function(typed::Function {
        name,
        params,
        ret: ret_ty,
        requires,
        ensures,
        body,
    }))
}

fn typecheck_method(
    method: &mut viper::Method,
    globals: &Globals,
    interner: &Interner,
) -> Result<typed::Declaration, TypeError> {
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
        .map(typed::StmtBlock);

    Ok(typed::Declaration::Method(typed::Method {
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
    program: &mut viper::Program,
    interner: &Interner,
    globals: &Globals,
) -> Result<typed::Program, Vec<TypeError>> {
    let mut decls = Vec::new();
    let mut errors = Vec::new();

    for decl in &mut program.0 {
        let result = match decl {
            viper::Declaration::Field(field) => Ok(Some(typecheck_field(field))),
            viper::Declaration::Predicate(pred) => {
                typecheck_predicate(pred, globals, interner).map(Some)
            }
            viper::Declaration::Function(func) => {
                typecheck_function(func, globals, interner).map(Some)
            }
            viper::Declaration::Method(method) => {
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
        Ok(typed::Program(decls))
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
    use crate::viper::{
        GlobalsCollector, IdentCollector, disambiguate, inline_macros, viper_parser,
        walk::AstWalkable,
    };

    fn run_pipeline(input: &str) -> Result<typed::Program, Vec<TypeError>> {
        let mut program = viper_parser::vpr_program(input).expect("parse failed");
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
    fn adt_destructor_classified_and_typed() {
        // `l.head` is classified as a destructor (disambiguation succeeds) and
        // typed to the field's type (`Int`), so the function body type-checks.
        let result = run_pipeline(
            r#"
adt List { Cons(head: Int, tail: List) Nil() }
function f(l: List): Int { l.head }
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
    }

    #[test]
    fn generic_adt_constructor_infers_type_arg() {
        // `Some(3)` infers `Option[Int]`, matching the declared return type.
        let result = run_pipeline(
            r#"
adt Option[T] { Some(value: T) None() }
function f(): Option[Int] { Some(3) }
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
    }

    #[test]
    fn generic_adt_constructor_type_arg_mismatch_fails() {
        // `Some(3) : Option[Int]` cannot satisfy a declared `Option[Bool]`.
        let result = run_pipeline(
            r#"
adt Option[T] { Some(value: T) None() }
function f(): Option[Bool] { Some(3) }
"#,
        );
        assert!(result.is_err(), "expected type mismatch, got Ok");
    }

    #[test]
    fn generic_adt_none_infers_from_context() {
        // `None()` has no argument to pin `T`; the return type provides it.
        let result = run_pipeline(
            r#"
adt Option[T] { Some(value: T) None() }
function f(): Option[Int] { None() }
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
    }

    #[test]
    fn generic_adt_destructor_resolves_type_arg() {
        // `o.value` on `Option[Int]` resolves the generic field type `T` to Int.
        let result = run_pipeline(
            r#"
adt Option[T] { Some(value: T) None() }
function f(o: Option[Int]): Int { o.value }
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
    }

    #[test]
    fn generic_adt_destructor_type_arg_mismatch_fails() {
        // `o.value` on `Option[Bool]` is Bool, not the declared Int return.
        let result = run_pipeline(
            r#"
adt Option[T] { Some(value: T) None() }
function f(o: Option[Bool]): Int { o.value }
"#,
        );
        assert!(result.is_err(), "expected type mismatch, got Ok");
    }

    #[test]
    fn generic_adt_two_params_pinned_independently() {
        let result = run_pipeline(
            r#"
adt Pair[A, B] { mk(fst: A, snd: B) }
function f(): Pair[Int, Bool] { mk(1, true) }
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
    }

    #[test]
    fn generic_adt_two_params_swapped_fails() {
        let result = run_pipeline(
            r#"
adt Pair[A, B] { mk(fst: A, snd: B) }
function f(): Pair[Int, Bool] { mk(true, 1) }
"#,
        );
        assert!(result.is_err(), "expected type mismatch, got Ok");
    }

    #[test]
    fn adt_discriminator_on_adt_ok() {
        let result = run_pipeline(
            r#"
adt MyAdt { one() two() }
function h(x: MyAdt): Bool { x.istwo }
"#,
        );
        assert!(result.is_ok(), "expected Ok, got: {result:?}");
    }

    #[test]
    fn adt_discriminator_on_non_adt_base_fails() {
        // Soundness: the base must be the variant's ADT, not an arbitrary type.
        let result = run_pipeline(
            r#"
adt MyAdt { one() two() }
function g(n: Int): Bool { n.istwo }
"#,
        );
        assert!(result.is_err(), "expected type error for Int base, got Ok");
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
                if let typed::Declaration::Method(m) = d {
                    Some(m)
                } else {
                    None
                }
            })
            .expect("method not found");
        let req = method.requires.as_ref().expect("requires missing");
        assert!(
            matches!(req.0.as_ref(), typed::SpatialExpKind::Acc(_, _)),
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
                .is_err_and(|errs| errs.iter().any(|e| matches!(
                    e,
                    TypeError::WrongReturnCount {
                        expected: 1,
                        found: 2
                    }
                ))),
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
                .is_err_and(|errs| errs.iter().any(|e| matches!(
                    e,
                    TypeError::WrongReturnCount {
                        expected: 1,
                        found: 2
                    }
                ))),
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
                .is_err_and(|errs| errs.iter().any(|e| matches!(
                    e,
                    TypeError::WrongReturnCount {
                        expected: 1,
                        found: 2
                    }
                ))),
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
