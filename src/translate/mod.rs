//! Lowers Silver `typed::Program` to `vmir::Program`.
//!
//! The coordinator (`translate`) walks `program.decls` in several passes
//! (mirroring the original single-`Builder` pipeline's `declare`/`define`
//! split), calling each entity kind's `Translator::declare`/`::define`
//! (`field.rs`/`predicate.rs`/`adt.rs`/`domain.rs`/`function.rs`/`method.rs`).
//! `declare` reserves a `Hole<T>` write-capability token for a member (see
//! `hole.rs`) and returns a `Meta` describing it; the coordinator folds every
//! `Meta` into `TranslationContext` (`name_map`, `contracts`, ...) so any
//! member can reference any other by the time bodies are lowered. `define`
//! later consumes the `Hole`, producing the actual `vmir::Declaration`
//! payload — a `Hole` left unfilled panics on drop, replacing the old
//! `debug_assert!`-guarded "slot filled twice" discipline with a
//! compile-time-enforced one.

use std::collections::HashMap;

use lasso::{Rodeo, Spur};
use typed_index_collections::TiVec;

use crate::viper::typed;
use crate::vmir;

pub mod errors;
mod adt;
mod context;
mod domain;
mod field;
mod function;
mod hole;
mod method;
mod predicate;
mod pure_exp;
mod reach;
mod resource;
mod sink;
mod spatial;
mod types;

pub use errors::TranslationError;

pub(crate) use context::{GenericSig, MethodContracts, TranslationContext};
pub(crate) use hole::{Declarator, Definer, Hole};

/// Build a `vmir::Program` from a typed `typed::Program`.
pub fn translate(program: &typed::Program) -> Result<vmir::Program, Vec<TranslationError>> {
    let interner = &program.interner;
    let decls = &program.decls;
    let mut builder = Builder::new();
    let mut ctx = TranslationContext::new(interner);

    // ---- declare ----
    //
    // Phase 1: predicates + fields, in source order (mirrors the original
    // `declare`'s first loop). A field's value type is looked up against
    // `ctx.name_map` *as built so far* — i.e. before any ADT/domain stub
    // exists — preserved unchanged from before this refactor.
    let mut predicates: HashMap<Spur, predicate::PredicateTranslator> = HashMap::new();
    for decl in decls {
        match decl {
            typed::Declaration::Predicate(p) => {
                let pt = predicate::PredicateTranslator::declare(p, interner, &mut builder);
                let m = pt.meta();
                ctx.name_map.insert(m.silver_name, m.id);
                predicates.insert(m.silver_name, pt);
            }
            typed::Declaration::Field(f) => {
                let ft = field::FieldTranslator::declare(f, interner, &ctx, &mut builder);
                let m = ft.meta();
                ctx.name_map.insert(m.silver_name, m.id);
                ctx.field_types.insert(m.silver_name, m.value.clone());
                // A field has no distinct body to lower later — fill its
                // `Hole` right away.
                ft.define(&mut builder);
            }
            typed::Declaration::Adt(_)
            | typed::Declaration::Domain(_)
            | typed::Declaration::Function(_)
            | typed::Declaration::Method(_) => {}
        }
    }

    // Phase 2 (pass 1): reserve a stub `Adt`/`Domain` per declaration (the
    // verifier mints its own ids/reductions from the variant shapes filled in
    // phase 4). Stubs are reserved first so a variant field type or
    // constructor, and a domain function's param/ret types, can reference any
    // ADT/domain by id regardless of source order.
    let mut adt_translators: Vec<adt::AdtTranslator> = Vec::new();
    for decl in decls {
        match decl {
            typed::Declaration::Adt(a) => {
                let at = adt::AdtTranslator::declare(a, interner, &mut builder);
                let m = at.meta();
                ctx.name_map.insert(m.silver_name, m.id);
                adt_translators.push(at);
            }
            typed::Declaration::Domain(d) => {
                let dt = domain::DomainTranslator::declare(d, interner, &mut builder);
                let m = dt.meta();
                ctx.name_map.insert(m.silver_name, m.id);
                // Bodyless — fill its `Hole` right away.
                dt.define(&mut builder);
            }
            _ => {}
        }
    }

    // Phase 3 (pass 2): user functions (top-level + domain functions). A
    // top-level function's own `Hole`s are filled later (`define_function`
    // needs a `Sink` and the precondition framing heap, available once every
    // member's id is known); a domain function is bodyless and filled
    // immediately, same as phase 2's stubs.
    let mut function_translators: HashMap<Spur, function::FunctionTranslator> = HashMap::new();
    for decl in decls {
        match decl {
            typed::Declaration::Function(f) => {
                let ft = function::FunctionTranslator::declare(f, interner, &mut builder);
                let m = ft.meta();
                ctx.contracts.insert(
                    m.silver_name,
                    MethodContracts {
                        requires: m.requires,
                        ensures: m.ensures,
                        heap_dep: m.heap_dep,
                    },
                );
                ctx.name_map.insert(m.silver_name, m.function);
                function_translators.insert(m.silver_name, ft);
            }
            typed::Declaration::Domain(d) => {
                let generics: Vec<Spur> = d.type_params.iter().map(|i| i.0).collect();
                for df in &d.functions {
                    let dft = domain::DomainFunctionTranslator::declare(
                        df,
                        interner,
                        &generics,
                        &ctx.name_map,
                        &mut builder,
                    );
                    let m = dft.meta();
                    ctx.name_map.insert(m.silver_name, m.id);
                    // Record the declared generic signature so a call site can
                    // recover its full type-argument instantiation (in this
                    // domain's type-parameter order). Only generic functions
                    // need it; a monomorphic one carries no type args.
                    if let Some(sig) = &m.generic_sig {
                        ctx.fn_generic_sigs.insert(m.silver_name, sig.clone());
                    }
                    dft.define(&mut builder);
                }
                // TODO: axioms are not yet translated
            }
            _ => {}
        }
    }

    // Phase 4 (pass 3): fill each ADT's variant shape and record
    // constructor/destructor metadata. Needs every ADT id from phase 2 (field
    // types reference them).
    let typed_adts: Vec<&typed::Adt> = decls
        .iter()
        .filter_map(|d| match d {
            typed::Declaration::Adt(a) => Some(a),
            _ => None,
        })
        .collect();
    let mut variants_by_adt =
        adt::compute_adt_info(&typed_adts, interner, &ctx.name_map, &mut ctx.adt, &mut builder);
    for at in adt_translators {
        let variants = variants_by_adt
            .remove(&at.meta().silver_name)
            .unwrap_or_default();
        at.define(variants, &mut builder);
    }

    // Phase 5: methods — contract resources and (for a method with a body) a
    // body slot.
    let mut method_contracts: HashMap<Spur, method::MethodContractsTranslator> = HashMap::new();
    let mut method_bodies: HashMap<Spur, method::MethodBodyTranslator> = HashMap::new();
    for decl in decls {
        if let typed::Declaration::Method(m) = decl {
            let mct = method::MethodContractsTranslator::declare(m, interner, &mut builder);
            let cm = mct.meta();
            ctx.contracts.insert(
                cm.silver_name,
                MethodContracts {
                    requires: cm.requires,
                    ensures: cm.ensures,
                    heap_dep: false,
                },
            );
            method_contracts.insert(cm.silver_name, mct);

            let mbt = method::MethodBodyTranslator::declare(m, interner, &mut builder);
            if let Some(id) = mbt.meta().id {
                ctx.name_map.insert(mbt.meta().silver_name, id);
            }
            method_bodies.insert(mbt.meta().silver_name, mbt);
        }
    }

    // `declare` is done: every group tag any body-lowering helper will ever
    // look up is registered. Snapshot it into `ctx` (owned, independent of
    // `builder` from here on).
    ctx.groups = builder.groups.clone();

    // ---- define ----
    //
    // Contract resources are defined before method bodies: a method body
    // inhales/exhales its callees' contracts and checks whether a callee has
    // its own `#requires` (`method_requires(callee).is_some()`), which must
    // already be recorded in `ctx.contracts`.
    let mut errors = Vec::new();
    for decl in decls {
        let r = match decl {
            typed::Declaration::Predicate(p) => predicates
                .remove(&p.name.0)
                .expect("declared in phase 1")
                .define(&ctx, p, &mut builder),
            typed::Declaration::Method(m) => method_contracts
                .remove(&m.name.0)
                .expect("declared in phase 5")
                .define(&ctx, m, &mut builder),
            typed::Declaration::Function(f) => function_translators
                .remove(&f.name.0)
                .expect("declared in phase 3")
                .define(&ctx, f, &mut builder),
            _ => Ok(()),
        };
        if let Err(e) = r {
            errors.push(e);
        }
    }
    for decl in decls {
        if let typed::Declaration::Method(m) = decl {
            let mbt = method_bodies.remove(&m.name.0).expect("declared in phase 5");
            if let Err(e) = mbt.define(&ctx, m, &mut builder) {
                errors.push(e);
            }
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(builder.finalize())
}

/// The write side of translation: allocates and fills `Declaration` slots.
/// Holds no shared read state (`name_map`, `contracts`, ...) — that lives in
/// the coordinator's [`TranslationContext`], a value entirely independent of
/// `Builder` (see `context.rs`'s module doc for why that separation matters).
pub(crate) struct Builder {
    /// Cheap string repr for member/constructor names. Keys are independent of
    /// `MemberId` — names are mapped to ids via `decl_names`.
    vmir_interner: Rodeo,
    /// Each declaration's name, parallel to `decls` (→ `Program.names`).
    decl_names: Vec<Spur>,
    /// Location **group** tags (`Type::Addr.group`) — field/predicate names,
    /// resolvable at verify time via `Program.groups`.
    groups: Rodeo<Spur>,
    /// Declarations indexed by `MemberId`. `None` slots are filled by `Hole`
    /// consumption (`Definer::define_*`).
    decls: Vec<Option<vmir::Declaration>>,
}

impl Builder {
    fn new() -> Self {
        Self {
            vmir_interner: Rodeo::new(),
            decl_names: Vec::new(),
            groups: Rodeo::new(),
            decls: Vec::new(),
        }
    }

    /// Reserve a `Declaration` slot (filled via `set_decl`), recording its name.
    /// `MemberId` is just the slot index; the interner key is unrelated.
    fn fresh_decl(&mut self, name: &str) -> vmir::MemberId {
        let id = vmir::MemberId(self.decls.len());
        let name_spur = self.vmir_interner.get_or_intern(name);
        self.decl_names.push(name_spur);
        self.decls.push(None);
        id
    }

    fn set_decl(&mut self, id: vmir::MemberId, decl: vmir::Declaration) {
        let slot = &mut self.decls[usize::from(id)];
        debug_assert!(slot.is_none(), "decl slot filled twice");
        *slot = Some(decl);
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

impl Declarator for Builder {
    fn allocate_hole<T>(&mut self, name: &str) -> (vmir::MemberId, Hole<T>) {
        let id = self.fresh_decl(name);
        (id, Hole::new(id))
    }

    fn intern_group(&mut self, s: &str) -> Spur {
        self.groups.get_or_intern(s)
    }
}

impl Definer for Builder {
    fn define_function(&mut self, hole: Hole<vmir::Function>, decl: vmir::Function) {
        let id = hole.fill();
        self.set_decl(id, vmir::Declaration::Function(decl));
    }

    fn define_resource(&mut self, hole: Hole<vmir::Resource>, decl: vmir::Resource) {
        let id = hole.fill();
        self.set_decl(id, vmir::Declaration::Resource(decl));
    }

    fn define_method(&mut self, hole: Hole<vmir::Method>, decl: vmir::Method) {
        let id = hole.fill();
        self.set_decl(id, vmir::Declaration::Method(decl));
    }

    fn define_adt(&mut self, hole: Hole<vmir::Adt>, decl: vmir::Adt) {
        let id = hole.fill();
        self.set_decl(id, vmir::Declaration::Adt(decl));
    }

    fn define_domain(&mut self, hole: Hole<vmir::Domain>, decl: vmir::Domain) {
        let id = hole.fill();
        self.set_decl(id, vmir::Declaration::Domain(decl));
    }

    fn intern_name(&mut self, s: &str) -> Spur {
        self.vmir_interner.get_or_intern(s)
    }
}

pub(crate) use types::{lower_type, match_generic};

#[cfg(test)]
mod tests;
