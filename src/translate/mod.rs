//! Lowers Silver `typed::Program` to `vmir::Program`.

use lasso::{Rodeo, Spur};
use std::collections::HashMap;
use typed_index_collections::TiVec;

use crate::viper::{Interner, typed};
use crate::vmir;

pub mod errors;
mod method;
mod pure_exp;
mod reach;
mod resource;
mod sink;
mod spatial;
mod types;

pub use errors::TranslationError;

/// Build a `vmir::Program` from a typed `typed::Program`.
///
/// Two phases: `declare` reserves a slot and records metadata for every member
/// (so any member can reference any other), then `define` fills each slot with
/// its body.
pub fn translate(program: &typed::Program) -> Result<vmir::Program, Vec<TranslationError>> {
    let mut builder = Builder::new(&program.interner);
    builder.declare(&program.decls);
    let errors = builder.define(&program.decls);
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(builder.finalize())
}

/// ADT shape metadata recorded in `declare`, consumed when lowering `AdtCons` /
/// `AdtProj` / `AdtTag` use sites.
#[derive(Default)]
pub(crate) struct AdtInfo {
    /// A constructor's `Spur` to `(owning ADT `Spur`, tag index)`.
    pub ctor_tag: HashMap<Spur, (Spur, usize)>,
    /// A destructor's `Spur` to the `(adt id, variant, field)` it projects.
    pub dtor_sem: HashMap<Spur, (vmir::MemberId, usize, usize)>,
}

/// A method's contract resource ids (`#requires` / `#ensures`), absent when the
/// method omits that clause.
#[derive(Default)]
pub(crate) struct MethodContracts {
    pub requires: Option<vmir::MemberId>,
    pub ensures: Option<vmir::MemberId>,
}

/// Mid-translation state.
pub(crate) struct Builder<'a> {
    pub interner: &'a Interner,
    /// Cheap string repr for member/constructor names. Keys are independent of
    /// `MemberId` — names are mapped to ids via `decl_names`.
    vmir_interner: Rodeo,
    /// Each declaration's name, parallel to `decls` (→ `Program.names`).
    decl_names: Vec<Spur>,
    /// Location **group** tags (`Type::Addr.group`) — field/predicate names,
    /// resolvable at verify time via `Program.groups`.
    groups: Rodeo<Spur>,
    /// Declarations indexed by `MemberId`. `None` slots are filled in `define`.
    decls: Vec<Option<vmir::Declaration>>,
    /// Silver `Spur` names to VMIR `MemberId`s.
    pub name_map: HashMap<Spur, vmir::MemberId>,
    /// A field's `Spur` to its lowered value type (for `field@addr`'s `Addr<T>`).
    pub field_types: HashMap<Spur, vmir::Type>,
    /// A method's `Spur` to its contract resource ids.
    pub contracts: HashMap<Spur, MethodContracts>,
    /// ADT constructor/destructor metadata.
    pub adt: AdtInfo,
    /// A generic function's `Spur` to its declared generic signature, used to
    /// recover a call's **full** type-argument instantiation (in the function's
    /// own type-parameter order) by matching the declared params/ret against the
    /// concrete call types. Absent ⟹ monomorphic ⟹ no type args.
    pub fn_generic_sigs: HashMap<Spur, GenericSig>,
}

/// A generic function's declared signature — the data needed to recover a call
/// site's type-argument instantiation. `ty_params` is the ordered list of
/// type-parameter names; `params`/`ret` are the declared types (possibly
/// mentioning those names as `Type::Generic`).
pub(crate) struct GenericSig {
    pub ty_params: Vec<Spur>,
    pub params: Vec<typed::Type>,
    pub ret: typed::Type,
}

impl<'a> Builder<'a> {
    fn new(interner: &'a Interner) -> Self {
        Self {
            interner,
            vmir_interner: Rodeo::new(),
            decl_names: Vec::new(),
            groups: Rodeo::new(),
            decls: Vec::new(),
            name_map: HashMap::new(),
            field_types: HashMap::new(),
            contracts: HashMap::new(),
            adt: AdtInfo::default(),
            fn_generic_sigs: HashMap::new(),
        }
    }

    /// A call's full type-argument instantiation, in the callee's own
    /// type-parameter order, recovered by matching the callee's declared
    /// generic signature against the concrete argument and result types. Empty
    /// for a monomorphic callee (no registered generic signature). This is the
    /// inference the backend would otherwise have to redo: doing it once here
    /// lets the verifier read the instantiation verbatim.
    pub(crate) fn call_type_args(
        &self,
        name: Spur,
        arg_tys: &[&typed::Type],
        ret_ty: &typed::Type,
    ) -> Vec<vmir::Type> {
        let Some(sig) = self.fn_generic_sigs.get(&name) else {
            return Vec::new();
        };
        let mut subst: HashMap<Spur, typed::Type> = HashMap::new();
        for (decl, actual) in sig.params.iter().zip(arg_tys) {
            match_generic(decl, actual, &mut subst);
        }
        match_generic(&sig.ret, ret_ty, &mut subst);
        // Every type parameter is guaranteed to occur in the params/ret (a
        // parameter used only in the body is not a real type parameter), so the
        // match populates all of them.
        sig.ty_params
            .iter()
            .map(|n| {
                let t = subst
                    .get(n)
                    .expect("type parameter must occur in params/ret");
                self.lower_type(t)
            })
            .collect()
    }

    /// The `#requires` contract resource of method `m`, if it has one.
    pub(crate) fn method_requires(&self, m: Spur) -> Option<vmir::MemberId> {
        self.contracts.get(&m).and_then(|c| c.requires)
    }

    /// The `#ensures` contract resource of method `m`, if it has one.
    pub(crate) fn method_ensures(&self, m: Spur) -> Option<vmir::MemberId> {
        self.contracts.get(&m).and_then(|c| c.ensures)
    }

    /// Reserve a `Declaration` slot (filled via `set_decl`), recording its name.
    /// `MemberId` is just the slot index; the interner key is unrelated.
    fn fresh_decl(&mut self, name: &str) -> (vmir::MemberId, Spur) {
        let id = vmir::MemberId(self.decls.len());
        let name_spur = self.vmir_interner.get_or_intern(name);
        self.decl_names.push(name_spur);
        self.decls.push(None);
        (id, name_spur)
    }

    /// Reserve a slot and record metadata for every member — predicates, fields,
    /// ADTs (+ constructors/destructors), user functions, and methods (+ their
    /// `#requires`/`#ensures` contracts). No bodies; ids are assigned so any
    /// member can reference any other in `define`.
    fn declare(&mut self, decls: &[typed::Declaration]) {
        for decl in decls {
            match decl {
                typed::Declaration::Predicate(p) => self.declare_predicate_accessors(p),
                typed::Declaration::Field(f) => self.declare_field_accessor(f),
                // ADTs/Domains/functions are handled by `declare_adts_and_functions`;
                // methods by `declare_method`.
                typed::Declaration::Adt(_)
                | typed::Declaration::Domain(_)
                | typed::Declaration::Function(_)
                | typed::Declaration::Method(_) => {}
            }
        }
        self.declare_adts_and_functions(decls);
        for decl in decls {
            if let typed::Declaration::Method(m) = decl {
                self.declare_method(m);
            }
        }
    }

    /// Fill every reserved slot with its body, collecting per-member errors.
    /// Contract resources are defined before method bodies: a method body inhales
    /// /exhales its callees' contracts and inspects their `precond`
    /// ([`Self::is_ctx_resource`]), which must already be set.
    fn define(&mut self, decls: &[typed::Declaration]) -> Vec<TranslationError> {
        let mut errors = Vec::new();
        for decl in decls {
            let r = match decl {
                typed::Declaration::Predicate(p) => self.define_predicate(p),
                typed::Declaration::Method(m) => self.define_method_contracts(m),
                typed::Declaration::Function(f) => self.define_function(f),
                _ => Ok(()),
            };
            if let Err(e) = r {
                errors.push(e);
            }
        }
        for decl in decls {
            if let typed::Declaration::Method(m) = decl
                && let Err(e) = self.define_method_body(m)
            {
                errors.push(e);
            }
        }
        errors
    }

    /// Whether `id` is a two-state resource (has a precondition resource, e.g.
    /// `#ensures`). Such calls carry a context heap; self-framed resources don't.
    pub(crate) fn is_ctx_resource(&self, id: vmir::MemberId) -> bool {
        matches!(
            self.decls.get(usize::from(id)),
            Some(Some(vmir::Declaration::Resource(r))) if !matches!(r.precond, vmir::Precond::SelfFramed)
        )
    }

    /// Lower a type in a concrete (non-generic) context. For ADT-declaration
    /// field types (which may mention type parameters) call the free
    /// [`lower_type`] with the owning ADT's parameter list instead.
    pub(crate) fn lower_type(&self, ty: &typed::Type) -> vmir::Type {
        lower_type(&self.name_map, &[], ty)
    }

    fn set_decl(&mut self, id: vmir::MemberId, decl: vmir::Declaration) {
        let slot = &mut self.decls[usize::from(id)];
        debug_assert!(slot.is_none(), "decl slot filled twice");
        *slot = Some(decl);
    }

    /// Declare a stub `Adt` per ADT, a decl per user/domain function, and record
    /// constructor/destructor metadata — all from the typed declarations. ADT
    /// stubs are reserved first so a variant field type or constructor can
    /// reference any ADT by id.
    fn declare_adts_and_functions(&mut self, decls: &[typed::Declaration]) {
        // Pass 1: reserve a stub `Adt` per ADT (the verifier mints its own ids
        // and reductions from the variant shapes filled in pass 3).
        for decl in decls {
            if let typed::Declaration::Adt(adt) = decl {
                let name_str = self.interner.resolve(&adt.name.0).to_string();
                let (adt_id, name) = self.fresh_decl(&name_str);
                self.set_decl(
                    adt_id,
                    vmir::Declaration::Adt(vmir::Adt {
                        name,
                        ty_params: adt.type_params.len().into(),
                        variants: Vec::new(),
                    }),
                );
                self.name_map.insert(adt.name.0, adt_id);
            } else if let typed::Declaration::Domain(d) = decl {
                let name_str = self.interner.resolve(&d.name.0).to_string();
                let (dom_id, name) = self.fresh_decl(&name_str);
                self.set_decl(
                    dom_id,
                    vmir::Declaration::Domain(vmir::Domain {
                        name,
                        ty_params: d.type_params.len().into(),
                    })
                );
                self.name_map.insert(d.name.0, dom_id);
            }
        }

        // Pass 2: user functions (top-level + domain functions).
        //
        // A top-level Silver `function` reserves slots (its own decl, plus a
        // `#requires` resource and `#ensures` contract function when present) and
        // is *filled* in `define_function` — where a `Sink` and the precondition
        // framing heap are available for its body. A domain function has no
        // contract/body and is emitted here directly as a bodyless
        // `vmir::Function`. `generics` is the owning domain's type parameters, in
        // scope for the signature (`Generic(T)`); top-level functions are
        // monomorphic.
        for decl in decls {
            match decl {
                typed::Declaration::Function(f) => {
                    let name = self.interner.resolve(&f.name.0).to_string();
                    let (id, _) = self.fresh_decl(&name);
                    self.name_map.insert(f.name.0, id);
                    let mut contracts = MethodContracts::default();
                    if f.requires.is_some() {
                        let (rid, _) = self.fresh_decl(&format!("{name}#requires"));
                        contracts.requires = Some(rid);
                    }
                    if f.ensures.is_some() {
                        let (eid, _) = self.fresh_decl(&format!("{name}#ensures"));
                        contracts.ensures = Some(eid);
                    }
                    self.contracts.insert(f.name.0, contracts);
                }
                typed::Declaration::Domain(d) => {
                    let generics: Vec<Spur> = d.type_params.iter().map(|i| i.0).collect();
                    for df in &d.functions {
                        let typed_params: Vec<typed::Type> =
                            df.params.iter().map(|p| p.ty.clone()).collect();
                        let name_str = self.interner.resolve(&df.name.0).to_string();
                        let (id, name_spur) = self.fresh_decl(&name_str);
                        let params = typed_params
                            .iter()
                            .map(|t| lower_type(&self.name_map, &generics, t))
                            .collect();
                        let ret = lower_type(&self.name_map, &generics, &df.ret);
                        self.set_decl(
                            id,
                            vmir::Declaration::Function(vmir::Function {
                                name: name_spur,
                                ty_params: generics.len().into(),
                                params,
                                ret,
                                body: None,
                            }),
                        );
                        self.name_map.insert(df.name.0, id);
                        // Record the declared generic signature so a call site can
                        // recover its full type-argument instantiation (in this
                        // domain's type-parameter order). Only generic functions
                        // need it; a monomorphic one carries no type args.
                        if !generics.is_empty() {
                            self.fn_generic_sigs.insert(
                                df.name.0,
                                GenericSig {
                                    ty_params: generics.clone(),
                                    params: typed_params,
                                    ret: df.ret.clone(),
                                },
                            );
                        }
                    }
                    // TODO: axioms are not yet translated
                }
                _ => {}
            }
        }

        // Pass 3: fill each ADT's variant shape and record constructor/destructor
        // metadata. Needs every ADT id from pass 1 (field types reference them).
        for decl in decls {
            if let typed::Declaration::Adt(adt) = decl {
                self.declare_adt_variants(adt);
            }
        }
    }

    /// Fill `adt`'s variant shapes and record its constructor (`ctor_tag`) and
    /// destructor (`dtor_sem`) metadata. A constructor/destructor is not a
    /// declaration: the constructor name is interned for display only, and a
    /// destructor maps a field name to its `(adt, variant, field)` projection.
    fn declare_adt_variants(&mut self, adt: &typed::Adt) {
        let adt_id = self.name_map[&adt.name.0];
        // Variant field types may mention the ADT's type parameters (→ `Generic`).
        let type_params: Vec<Spur> = adt.type_params.iter().map(|i| i.0).collect();
        for (tag, v) in adt.variants.iter().enumerate() {
            self.adt.ctor_tag.insert(v.name.0, (adt.name.0, tag));
            let ctor_str = self.interner.resolve(&v.name.0).to_string();
            let ctor_name = self.vmir_interner.get_or_intern(&ctor_str);
            let field_types: Vec<vmir::Type> = v
                .params
                .iter()
                .map(|p| lower_type(&self.name_map, &type_params, &p.ty))
                .collect();
            for (field, p) in v.params.iter().enumerate() {
                self.adt.dtor_sem.insert(p.name.0, (adt_id, tag, field));
            }
            if let Some(vmir::Declaration::Adt(a)) = self.decls[usize::from(adt_id)].as_mut() {
                if a.variants.len() <= tag {
                    a.variants.resize(
                        tag + 1,
                        vmir::AdtVariant {
                            name: None,
                            field_types: Vec::new(),
                        },
                    );
                }
                a.variants[tag] = vmir::AdtVariant {
                    name: Some(ctor_name),
                    field_types,
                };
            }
        }
    }

    fn declare_predicate_accessors(&mut self, p: &typed::Predicate) {
        let pred_name = self.interner.resolve(&p.name.0).to_owned();
        // Reserve the predicate's Resource slot (filled by `emit_predicate`) so its
        // id can serve as snapshot head, address `LocId`, and footprint reference.
        let (pred_id, _) = self.fresh_decl(&pred_name);
        self.name_map.insert(p.name.0, pred_id);
        // Its address is grouped by the predicate name, not by `pred_id`.
        self.groups.get_or_intern(&pred_name);
    }

    fn declare_field_accessor(&mut self, f: &typed::Field) {
        // A field's address is an ordinary function `Ref -> Addr<T>` (group = field
        // name, value = field type, bound = full permission `1/1`).
        let field_name = self.interner.resolve(&f.0.name.0).to_owned();
        self.groups.get_or_intern(&field_name);
        let (field_id, name_spur) = self.fresh_decl(&field_name);
        let group = self.group_tag(f.0.name.0);
        let value = self.lower_type(&f.0.ty);
        self.field_types.insert(f.0.name.0, value.clone());
        let bound = vmir::Bound::Bounded(num::BigRational::from(num::BigInt::from(1)));
        let ret = vmir::Type::addr(group, value, bound);
        self.set_decl(
            field_id,
            vmir::Declaration::Function(vmir::Function {
                name: name_spur,
                ty_params: 0.into(),
                params: vec![vmir::Type::Ref].into(),
                ret,
                body: None,
            }),
        );
        self.name_map.insert(f.0.name.0, field_id);
    }

    /// The interned group tag for a field/predicate name (registered in the
    /// declare phase).
    pub fn group_tag(&self, name: Spur) -> Spur {
        let s = self.interner.resolve(&name);
        self.groups
            .get(s)
            .unwrap_or_else(|| panic!("group tag `{s}` not registered"))
    }

    fn define_predicate(&mut self, p: &typed::Predicate) -> Result<(), TranslationError> {
        let pred_id = self.name_map[&p.name.0];
        let params: Vec<vmir::Type> = p.params.iter().map(|p| self.lower_type(&p.ty)).collect();
        // Self-framed: params occupy `Val::Temp(0..n)`, heaps accumulate from
        // `Empty` starting at `HeapVal::Temp(0)`.
        let body = match &p.body {
            None => None,
            Some(body_exp) => {
                let mut env: HashMap<Spur, vmir::Val> = HashMap::new();
                for (i, param) in p.params.iter().enumerate() {
                    env.insert(param.name.0, vmir::Val::Temp(i));
                }
                Some(spatial::lower_spatial_never(
                    self,
                    &env,
                    body_exp,
                    params.len(),
                    vmir::HeapVal::Empty,
                    0,
                )?)
            }
        };
        let name = self.vmir_interner.get_or_intern(self.interner.resolve(&p.name.0));
        self.set_decl(
            pred_id,
            vmir::Declaration::Resource(vmir::Resource {
                name,
                params,
                precond: vmir::Precond::SelfFramed,
                body,
            }),
        );
        Ok(())
    }

    /// Fill a Silver `function`'s reserved slots (see the declare pass in
    /// [`Self::declare_adts_and_functions`]): the main function decl, plus
    /// boolean `#requires` / `#ensures` contract functions when present.
    ///
    /// Functions are **pure and heap-free**. Their contracts are ordinary boolean
    /// functions, stitched as pure `assume`/`assert`:
    /// - `#requires` → a boolean [`vmir::Function`] `params -> Bool`.
    /// - `#ensures` → a boolean [`vmir::Function`] `(params ++ result) -> Bool`.
    /// - the main function → its lowered body (when present) which **assumes**
    ///   `#requires(params)` at entry and **asserts** `#ensures(params, result)`
    ///   at exit.
    ///
    /// A `requires` that mentions `acc` makes the function heap-dependent, which
    /// is not yet supported (a future separate declaration) — rejected here.
    fn define_function(&mut self, f: &typed::Function) -> Result<(), TranslationError> {
        let fname = self.interner.resolve(&f.name.0).to_string();
        let n_params = f.params.len();
        let params: Vec<vmir::Type> = f.params.iter().map(|p| self.lower_type(&p.ty)).collect();
        let ret = self.lower_type(&f.ret);

        // Heap-dependent functions (a `requires` granting permission) are a future
        // separate declaration.
        if let Some(requires) = &f.requires
            && spatial::spatial_contains_acc(requires)
        {
            return Err(TranslationError::Unsupported(
                "heap-dependent function (acc in precondition)",
            ));
        }

        // Params occupy `Val::Temp(0..n_params)` in every body lowered below.
        let mut env: HashMap<Spur, vmir::Val> = HashMap::new();
        for (i, p) in f.params.iter().enumerate() {
            env.insert(p.name.0, vmir::Val::Temp(i));
        }

        // #requires: a boolean function `params -> Bool` (the pure precondition).
        if let Some(requires) = &f.requires {
            let req_id = self
                .method_requires(f.name.0)
                .expect("declared in declare pass");
            let body = spatial::lower_pure_precond_body(self, &env, requires, n_params)?;
            let name = self
                .vmir_interner
                .get_or_intern(format!("{fname}#requires"));
            self.set_decl(
                req_id,
                vmir::Declaration::Function(vmir::Function {
                    name,
                    ty_params: 0.into(),
                    params: params.clone().into(),
                    ret: vmir::Type::Bool,
                    body: Some(body),
                }),
            );
        }

        // #ensures: a boolean function `(params ++ result) -> Bool`. `result`
        // occupies `Val::Temp(n_params)`, so body temps start after it.
        if let Some(ensures) = &f.ensures {
            let ens_id = self
                .method_ensures(f.name.0)
                .expect("declared in declare pass");
            let mut ens_params = params.clone();
            ens_params.push(ret.clone());
            let result = vmir::Val::Temp(n_params);
            let body = pure_exp::lower_function_body(
                self,
                &env,
                ensures,
                n_params + 1,
                vmir::HeapVal::Empty,
                Some(result),
                None,
            )?;
            let name = self.vmir_interner.get_or_intern(format!("{fname}#ensures"));
            self.set_decl(
                ens_id,
                vmir::Declaration::Function(vmir::Function {
                    name,
                    ty_params: 0.into(),
                    params: ens_params.into(),
                    ret: vmir::Type::Bool,
                    body: Some(body),
                }),
            );
        }

        // The main function: pure, heap-free. Its body (when present) assumes
        // `#requires(params)` at entry and asserts `#ensures(params, result)` at
        // exit — the contract functions applied to the actual body result.
        let contract = pure_exp::FnContract {
            requires: self.method_requires(f.name.0),
            ensures: self.method_ensures(f.name.0),
            params: (0..n_params).map(vmir::Val::Temp).collect(),
        };
        let f_id = self.name_map[&f.name.0];
        let body = match &f.body {
            None => None,
            Some(body_exp) => Some(pure_exp::lower_function_body(
                self,
                &env,
                body_exp,
                n_params,
                vmir::HeapVal::Empty,
                None,
                Some(contract),
            )?),
        };
        let name = self.vmir_interner.get_or_intern(&fname);
        self.set_decl(
            f_id,
            vmir::Declaration::Function(vmir::Function {
                name,
                ty_params: 0.into(),
                params: params.into(),
                ret,
                body,
            }),
        );
        Ok(())
    }

    /// Reserve slots for a method and its contract resources (filled by
    /// [`Self::define_method_contracts`] / [`Self::define_method_body`]). A method
    /// gets a slot only if it has a body.
    fn declare_method(&mut self, m: &typed::Method) {
        let name = self.interner.resolve(&m.name.0).to_owned();
        if m.body.is_some() {
            let (method_id, _) = self.fresh_decl(&name);
            self.name_map.insert(m.name.0, method_id);
        }
        let mut contracts = MethodContracts::default();
        if m.requires.is_some() {
            let (id, _) = self.fresh_decl(&format!("{name}#requires"));
            contracts.requires = Some(id);
        }
        if m.ensures.is_some() {
            let (id, _) = self.fresh_decl(&format!("{name}#ensures"));
            contracts.ensures = Some(id);
        }
        self.contracts.insert(m.name.0, contracts);
    }

    fn define_method_contracts(&mut self, m: &typed::Method) -> Result<(), TranslationError> {
        if let Some(requires) = &m.requires {
            let req_id = self
                .method_requires(m.name.0)
                .expect("declared in declare_method");
            let params: Vec<vmir::Type> = m.params.iter().map(|p| self.lower_type(&p.ty)).collect();
            let mut env: HashMap<Spur, vmir::Val> = HashMap::new();
            for (i, p) in m.params.iter().enumerate() {
                env.insert(p.name.0, vmir::Val::Temp(i));
            }
            // Self-framed: accumulate from `Empty`, heaps start at `HeapVal::Temp(0)`.
            let body = spatial::lower_spatial_never(
                self,
                &env,
                requires,
                params.len(),
                vmir::HeapVal::Empty,
                0,
            )?;
            let name = self.vmir_interner.get_or_intern(&format!("{}#requires", self.interner.resolve(&m.name.0)));
            self.set_decl(
                req_id,
                vmir::Declaration::Resource(vmir::Resource {
                    name,
                    params,
                    precond: vmir::Precond::SelfFramed,
                    body: Some(body),
                }),
            );
        }

        if let Some(ensures) = &m.ensures {
            let ens_id = self
                .method_ensures(m.name.0)
                .expect("declared in declare_method");
            let mut params: Vec<vmir::Type> =
                m.params.iter().map(|p| self.lower_type(&p.ty)).collect();
            params.extend(m.rets.iter().map(|r| self.lower_type(&r.ty)));
            let mut env: HashMap<Spur, vmir::Val> = HashMap::new();
            for (i, p) in m.params.iter().enumerate() {
                env.insert(p.name.0, vmir::Val::Temp(i));
            }
            for (i, r) in m.rets.iter().enumerate() {
                env.insert(r.name.0, vmir::Val::Temp(m.params.len() + i));
            }
            // The ensures precondition is `m#requires` (when present). Its delta
            // accumulates from `Empty` so a resource in both contracts isn't
            // double-counted.
            let precond = self
                .method_requires(m.name.0)
                .map(|req_id| {
                    let req_args: Vec<vmir::Val> =
                        (0..m.params.len()).map(vmir::Val::Temp).collect();
                    vmir::Precond::Ctx(req_id, req_args)
                })
                .unwrap_or(vmir::Precond::SelfFramed);
            // Two-state (`Ctx`) ensures reserves `HeapVal::Temp(0)` as the pre-state
            // slot that `old(...)` reads (so emitted heaps start at 1); self-framed
            // ensures has no pre-state.
            let (heap_base, pre_state) = match &precond {
                vmir::Precond::Ctx(..) => (1, Some(vmir::HeapVal::Temp(0))),
                vmir::Precond::SelfFramed => (0, None),
            };
            let body = spatial::lower_spatial_ensures(
                self,
                &env,
                ensures,
                params.len(),
                vmir::HeapVal::Empty,
                heap_base,
                pre_state,
            )?;
            let name = self.vmir_interner.get_or_intern(&format!("{}#ensures", self.interner.resolve(&m.name.0)));
            self.set_decl(
                ens_id,
                vmir::Declaration::Resource(vmir::Resource {
                    name,
                    params,
                    precond,
                    body: Some(body),
                }),
            );
        }

        Ok(())
    }

    fn define_method_body(&mut self, m: &typed::Method) -> Result<(), TranslationError> {
        let Some(body) = &m.body else { return Ok(()) };
        let method_id = *self
            .name_map
            .get(&m.name.0)
            .expect("method id should be interned");
        let name = self.vmir_interner.get_or_intern(self.interner.resolve(&m.name.0));
        let method = method::lower_method(self, m, name, body)?;
        self.set_decl(method_id, vmir::Declaration::Method(method));
        Ok(())
    }

    fn finalize(self) -> vmir::Program {
        let decls: TiVec<vmir::MemberId, vmir::Declaration> = self
            .decls
            .into_iter()
            .map(|o| o.expect("declaration slot left empty"))
            .collect();
        vmir::Program {
            decls,
            interner: self.vmir_interner,
            groups: self.groups,
        }
    }
}

pub(crate) use types::{lower_type, match_generic};

#[cfg(test)]
mod tests;
