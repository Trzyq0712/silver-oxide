//! Lowers Silver `typed::Program` to `vmir::Program`.

use lasso::{Rodeo, Spur};
use std::collections::HashMap;
use typed_index_collections::TiVec;

use crate::viper::{GlobalSignature, Globals, Interner, typed};
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
pub fn translate(
    program: &typed::Program,
    globals: &Globals,
) -> Result<vmir::Program, Vec<TranslationError>> {
    let mut builder = Builder::new(&program.interner, globals);
    builder.declare(&program.decls);
    let errors = builder.define(&program.decls);
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(builder.finalize())
}

/// Mid-translation state.
pub(crate) struct Builder<'a> {
    pub interner: &'a Interner,
    pub globals: &'a Globals,
    /// Cheap string repr for member/constructor names. Keys are independent of
    /// `MemberId` — names are mapped to ids via `decl_names`.
    vmir_interner: Rodeo,
    /// Each declaration's name, parallel to `decls` (→ `Program.names`).
    decl_names: Vec<Spur>,
    /// Location **group** tags (`Type::Addr.group`) — field/predicate names,
    /// resolvable at verify time via `Program.groups`.
    groups: Rodeo<lasso::Spur>,
    /// Declarations indexed by MemberId. `None` slots are filled in later phases.
    decls: Vec<Option<vmir::Declaration>>,
    /// Silver `Spur` names to VMIR `MemberId`s.
    pub name_map: HashMap<Spur, vmir::MemberId>,
    /// A method's `Spur` to its `#requires` Resource MemberId (if any).
    pub method_requires: HashMap<Spur, vmir::MemberId>,
    /// A method's `Spur` to its `#ensures` Resource MemberId (if any).
    pub method_ensures: HashMap<Spur, vmir::MemberId>,
    /// A constructor's `Spur` to `(owning ADT `Spur`, tag index)`.
    pub ctor_tag: HashMap<Spur, (Spur, usize)>,
    /// A destructor's `Spur` to the `(adt id, variant, field)` it projects.
    pub dtor_sem: HashMap<Spur, (vmir::MemberId, usize, usize)>,
}

impl<'a> Builder<'a> {
    fn new(interner: &'a Interner, globals: &'a Globals) -> Self {
        Self {
            interner,
            globals,
            vmir_interner: Rodeo::new(),
            decl_names: Vec::new(),
            groups: Rodeo::new(),
            decls: Vec::new(),
            name_map: HashMap::new(),
            method_requires: HashMap::new(),
            method_ensures: HashMap::new(),
            ctor_tag: HashMap::new(),
            dtor_sem: HashMap::new(),
        }
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
                typed::Declaration::Function(_) | typed::Declaration::Method(_) => {}
            }
        }
        // ADTs/functions live in `globals`, not the typed decls.
        self.declare_adts_and_functions();
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

    /// Declare a stub `Adt` per ADT, a decl per user function, and record
    /// constructor/destructor metadata. ADTs first so a constructor can register
    /// against its ADT; functions before constructors so every `fresh_decl`
    /// precedes the constructor-name interning (see `pending_ctor_names`).
    fn declare_adts_and_functions(&mut self) {
        let globals = self.globals;
        let interner = self.interner;
        // Deterministic order: by Silver declaration order (global MemberId).
        let mut entries: Vec<_> = globals.symbol_table.iter().map(|(s, m)| (*s, *m)).collect();
        entries.sort_by_key(|(_, m)| usize::from(*m));

        // Pass 1: ADTs (the verifier mints its own ids and reductions).
        for (spur, gmid) in &entries {
            if let GlobalSignature::Adt(_) = &globals.signatures[*gmid] {
                let name = interner.resolve(spur).to_string();
                let adt_id = self.fresh_decl(&name);
                self.set_decl(
                    adt_id,
                    vmir::Declaration::Adt(vmir::Adt {
                        variants: Vec::new(),
                    }),
                );
                self.name_map.insert(*spur, adt_id);
            }
        }

        // Pass 2a: user functions.
        for (spur, gmid) in &entries {
            if let GlobalSignature::Function(sig) = &globals.signatures[*gmid] {
                let name = interner.resolve(spur).to_string();
                let id = self.fresh_decl(&name);
                let params = sig.params.iter().map(|t| self.lower_type(t)).collect();
                let ret = self.lower_type(&sig.ret);
                self.set_decl(
                    id,
                    vmir::Declaration::Function(vmir::Function {
                        params,
                        ret,
                        body: None,
                    }),
                );
                self.name_map.insert(*spur, id);
            }
        }

        // Pass 2b: ADT constructors — no decl (they lower to a semantic `AdtCons`
        // node). Record the `(adt, tag)` mapping and fill the ADT's variant shape.
        // A constructor name is not a declaration, so it is interned for display
        // only (its `Spur` is unrelated to any `MemberId`).
        for (spur, gmid) in &entries {
            if let GlobalSignature::AdtConstructor(sig) = &globals.signatures[*gmid] {
                self.ctor_tag.insert(*spur, (sig.adt, sig.tag));
                let adt_id = self.name_map[&sig.adt];
                let ctor_name = self.vmir_interner.get_or_intern(interner.resolve(spur));
                // Field types may mention the ADT's type parameters, so lower
                // them against the owning ADT's parameter list (→ `Generic(i)`).
                let adt_params = globals
                    .resolve(sig.adt)
                    .and_then(|s| s.as_adt())
                    .map(|a| a.params.clone())
                    .unwrap_or_default();
                let field_types: Vec<vmir::Type> = sig
                    .params
                    .iter()
                    .map(|t| lower_type(&self.name_map, &adt_params, t))
                    .collect();
                if let Some(vmir::Declaration::Adt(adt)) = self.decls[usize::from(adt_id)].as_mut()
                {
                    if adt.variants.len() <= sig.tag {
                        adt.variants.resize(
                            sig.tag + 1,
                            vmir::AdtVariant {
                                name: None,
                                field_types: Vec::new(),
                            },
                        );
                    }
                    adt.variants[sig.tag] = vmir::AdtVariant {
                        name: Some(ctor_name),
                        field_types,
                    };
                }
            }
        }

        // Pass 3: destructor semantics `(adt, variant, field)` for `AdtProj` use
        // sites (no accessor decls — the verifier mints projection ids).
        let mut dtors: Vec<_> = globals.dtor_by_name.iter().collect();
        dtors.sort_by_key(|(s, _)| interner.resolve(s).to_string());
        for (dtor_spur, info) in dtors {
            let adt_id = self.name_map[&info.adt];
            let variant = self.ctor_tag[&info.ctor].1;
            self.dtor_sem
                .insert(*dtor_spur, (adt_id, variant, info.index));
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
    pub fn group_tag(&self, name: Spur) -> lasso::Spur {
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
        if m.requires.is_some() {
            let req_id = self.fresh_decl(&format!("{name}#requires"));
            self.method_requires.insert(m.name.0, req_id);
        }
        if m.ensures.is_some() {
            let ens_id = self.fresh_decl(&format!("{name}#ensures"));
            self.method_ensures.insert(m.name.0, ens_id);
        }
    }

    fn define_method_contracts(&mut self, m: &typed::Method) -> Result<(), TranslationError> {
        if let Some(requires) = &m.requires {
            let req_id = self.method_requires[&m.name.0];
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
            let ens_id = self.method_ensures[&m.name.0];
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
                .method_requires
                .get(&m.name.0)
                .copied()
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
