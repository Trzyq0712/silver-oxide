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
        }
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
    fn fresh_decl(&mut self, name: &str) -> vmir::MemberId {
        let id = vmir::MemberId(self.decls.len());
        self.decl_names.push(self.vmir_interner.get_or_intern(name));
        self.decls.push(None);
        id
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
                let name = self.interner.resolve(&adt.name.0).to_string();
                let adt_id = self.fresh_decl(&name);
                self.set_decl(
                    adt_id,
                    vmir::Declaration::Adt(vmir::Adt {
                        variants: Vec::new(),
                    }),
                );
                self.name_map.insert(adt.name.0, adt_id);
            }
        }

        // Pass 2a: top-level user functions (ground signatures).
        for decl in decls {
            if let typed::Declaration::Function(func) = decl {
                self.declare_function(func, &[]);
            }
        }
        // Pass 2b: domain functions — schemas over their domain's type parameters.
        for decl in decls {
            if let typed::Declaration::Domain(domain) = decl {
                let generics: Vec<Spur> = domain.type_params.iter().map(|i| i.0).collect();
                for func in &domain.functions {
                    self.declare_function(func, &generics);
                }
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

    /// Declare a VMIR `Function` from a typed function signature, lowering its
    /// param/return types against `generics` (empty for a ground top-level
    /// function; the domain's type parameters for a domain function).
    fn declare_function<G: typed::TypeParam>(
        &mut self,
        func: &typed::Function<G>,
        generics: &[Spur],
    ) {
        let name = self.interner.resolve(&func.name.0).to_string();
        let id = self.fresh_decl(&name);
        let params = func
            .params
            .iter()
            .map(|p| lower_type(&self.name_map, generics, &p.ty))
            .collect();
        let ret = lower_type(&self.name_map, generics, &func.ret);
        self.set_decl(
            id,
            vmir::Declaration::Function(vmir::Function {
                params,
                ret,
                body: None,
            }),
        );
        self.name_map.insert(func.name.0, id);
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
        let pred_id = self.fresh_decl(&pred_name);
        self.name_map.insert(p.name.0, pred_id);
        // Its address is grouped by the predicate name, not by `pred_id`.
        self.groups.get_or_intern(&pred_name);
    }

    fn declare_field_accessor(&mut self, f: &typed::Field) {
        // A field's address is an ordinary function `Ref -> Addr<T>` (group = field
        // name, value = field type, bound = full permission `1/1`).
        let field_name = self.interner.resolve(&f.0.name.0).to_owned();
        self.groups.get_or_intern(&field_name);
        let field_id = self.fresh_decl(&field_name);
        let group = self.group_tag(f.0.name.0);
        let value = self.lower_type(&f.0.ty);
        self.field_types.insert(f.0.name.0, value.clone());
        let bound = vmir::Bound::Bounded(num::BigRational::from(num::BigInt::from(1)));
        let ret = vmir::Type::addr(group, value, bound);
        self.set_decl(
            field_id,
            vmir::Declaration::Function(vmir::Function {
                params: vec![vmir::Type::Ref],
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
        self.set_decl(
            pred_id,
            vmir::Declaration::Resource(vmir::Resource {
                params,
                precond: vmir::Precond::SelfFramed,
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
            let method_id = self.fresh_decl(&name);
            self.name_map.insert(m.name.0, method_id);
        }
        let mut contracts = MethodContracts::default();
        if m.requires.is_some() {
            contracts.requires = Some(self.fresh_decl(&format!("{name}#requires")));
        }
        if m.ensures.is_some() {
            contracts.ensures = Some(self.fresh_decl(&format!("{name}#ensures")));
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
            self.set_decl(
                req_id,
                vmir::Declaration::Resource(vmir::Resource {
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
            self.set_decl(
                ens_id,
                vmir::Declaration::Resource(vmir::Resource {
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
        let method = method::lower_method(self, m, body)?;
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
            names: self.decl_names.into(),
            interner: self.vmir_interner,
            groups: self.groups,
        }
    }
}

pub(crate) use types::lower_type;

#[cfg(test)]
mod tests;
