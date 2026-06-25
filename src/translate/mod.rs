//! Lowers Silver `typed::Program` to `vmir::Program`.
//!
//! Minimal scope (Phase 2 first cut): abstract predicates, method contracts
//! over `acc(P(args), perm)` / `Conj` / `Implies` / `Ternary` / `Pure` lifts
//! and the pure ops `Binary` / `Unary` / `Ternary` / `Ident` / `Const`.
//! Method bodies: straight-line var/assign + method calls. No control flow,
//! no unfolding, no user function calls, no field acc (stubbed but not
//! exercised by the target case).

use lasso::{Rodeo, Spur};
use std::collections::HashMap;
use typed_index_collections::TiVec;

use crate::viper::{GlobalSignature, Globals, Interner, typed};
use crate::vmir;

pub mod errors;
mod method;
mod pure_exp;
mod resource;

pub use errors::TranslationError;

/// Build a `vmir::Program` from a typed `typed::Program`.
pub fn translate(
    program: &typed::Program,
    interner: &Interner,
    globals: &Globals,
) -> Result<vmir::Program, Vec<TranslationError>> {
    let mut builder = Builder::new(interner, globals);
    let mut errors = Vec::new();

    // Phase A: synthesise the predicate `@snap`/`@addr` accessors and the
    // field address functions (emitted under the field's own name).
    for decl in &program.0 {
        match decl {
            typed::Declaration::Predicate(p) => builder.declare_predicate_accessors(p),
            typed::Declaration::Field(f) => builder.declare_field_accessor(f),
            typed::Declaration::Function(_) | typed::Declaration::Method(_) => {}
        }
    }

    // Phase A2: declare ADTs, their `@tag` functions, constructors, and user
    // functions, so calls/discriminators resolve in later phases.
    builder.declare_adts_and_functions();

    // Phase B1: emit Resource declarations (predicates + method contracts).
    for decl in &program.0 {
        match decl {
            typed::Declaration::Predicate(p) => {
                if let Err(e) = builder.emit_predicate(p) {
                    errors.push(e);
                }
            }
            typed::Declaration::Method(m) => {
                if let Err(e) = builder.emit_method_contracts(m) {
                    errors.push(e);
                }
            }
            _ => {}
        }
    }

    // Phase B2: emit Method bodies.
    for decl in &program.0 {
        if let typed::Declaration::Method(m) = decl
            && let Err(e) = builder.emit_method_body(m)
        {
            errors.push(e);
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(builder.finalize())
}

/// Mid-translation state.
pub(crate) struct Builder<'a> {
    pub interner: &'a Interner,
    pub globals: &'a Globals,
    /// VMIR name interner. MemberIds are positions in `decls`.
    vmir_interner: Rodeo<vmir::MemberId>,
    /// Location **group** tags (`Type::Addr.group`) — field/predicate names
    /// interned here, NOT as declarations. Resolvable at verify time via
    /// `Program.groups`.
    groups: Rodeo<lasso::Spur>,
    /// Declarations indexed by MemberId. Empty `None` slots are filled in
    /// later phases.
    decls: Vec<Option<vmir::Declaration>>,
    /// Maps Silver `Spur` names to VMIR `MemberId`s.
    pub name_map: HashMap<Spur, vmir::MemberId>,
    /// Maps a method's `Spur` to its `#requires` Resource MemberId (if any).
    pub method_requires: HashMap<Spur, vmir::MemberId>,
    /// Maps a method's `Spur` to its `#ensures` Resource MemberId (if any).
    pub method_ensures: HashMap<Spur, vmir::MemberId>,
    /// Maps a constructor's `Spur` to `(owning ADT `Spur`, tag index)`.
    pub ctor_tag: HashMap<Spur, (Spur, usize)>,
    /// Maps a destructor's `Spur` to the semantic `(adt id, variant, field)` it
    /// projects — the operands of a `PureInst::AdtProj`.
    pub dtor_sem: HashMap<Spur, (vmir::MemberId, usize, usize)>,
    /// Constructor names to intern (`(adt id, variant tag, name)`), applied in
    /// `finalize` after every `fresh_decl` so interning a non-decl name never
    /// breaks the decl/interner index invariant.
    pending_ctor_names: Vec<(vmir::MemberId, usize, String)>,
}

impl<'a> Builder<'a> {
    fn new(interner: &'a Interner, globals: &'a Globals) -> Self {
        Self {
            interner,
            globals,
            vmir_interner: Rodeo::new(),
            groups: Rodeo::new(),
            decls: Vec::new(),
            name_map: HashMap::new(),
            method_requires: HashMap::new(),
            method_ensures: HashMap::new(),
            ctor_tag: HashMap::new(),
            dtor_sem: HashMap::new(),
            pending_ctor_names: Vec::new(),
        }
    }

    /// Intern a fresh name and reserve a `Declaration` slot for it. The
    /// caller fills the slot via `set_decl`.
    fn fresh_decl(&mut self, name: &str) -> vmir::MemberId {
        let id = self.vmir_interner.get_or_intern(name);
        // get_or_intern assigns ids in increasing order; we never re-intern.
        debug_assert_eq!(usize::from(id), self.decls.len());
        self.decls.push(None);
        id
    }

    /// Whether `id` is a resource with a precondition resource (two-state, e.g.
    /// `#ensures`). Such calls carry a context heap; self-framed resources don't.
    pub(crate) fn is_ctx_resource(&self, id: vmir::MemberId) -> bool {
        matches!(
            self.decls.get(usize::from(id)),
            Some(Some(vmir::Declaration::Resource(r))) if !matches!(r.precond, vmir::Precond::SelfFramed)
        )
    }

    /// Lower a typed type in a concrete (non-generic) context, resolving
    /// domain/ADT names through the VMIR name map. For ADT-declaration field
    /// types (which may mention type parameters) call the free [`lower_type`]
    /// with the owning ADT's parameter list instead.
    pub(crate) fn lower_type(&self, ty: &typed::Type) -> vmir::Type {
        lower_type(&self.name_map, &[], ty)
    }

    fn set_decl(&mut self, id: vmir::MemberId, decl: vmir::Declaration) {
        let slot = &mut self.decls[usize::from(id)];
        debug_assert!(slot.is_none(), "decl slot filled twice");
        *slot = Some(decl);
    }

    /// Declare VMIR decls for every ADT (a stub `Adt` + a synthesized `@tag`
    /// function), every ADT constructor, and every user function, populating
    /// the name map and ADT metadata. ADTs are declared first so a
    /// constructor can register against its ADT's `@tag` function.
    fn declare_adts_and_functions(&mut self) {
        let globals = self.globals;
        let interner = self.interner;
        // Deterministic order: by Silver declaration order (global MemberId).
        let mut entries: Vec<_> = globals.symbol_table.iter().map(|(s, m)| (*s, *m)).collect();
        entries.sort_by_key(|(_, m)| usize::from(*m));

        // Pass 1: ADTs (semantic — no synthetic `@tag` function; the verifier
        // mints its own ids and reductions, see `verify::mono`).
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

        // Pass 2a: user functions (each gets a decl). Done before constructors so
        // every `fresh_decl` precedes the constructor-name interning below (which
        // advances the interner past `decls.len()` without a decl slot).
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

        // Pass 2b: ADT constructors. No declaration is emitted (they lower to a
        // semantic `AdtCons` node; the verifier mints the id). Record the
        // `(adt, tag)` mapping and fill the ADT's variant shape. The constructor
        // *name* is interned in `finalize` (after every `fresh_decl`, so it never
        // perturbs the decl/interner index invariant) — see `pending_ctor_names`.
        for (spur, gmid) in &entries {
            if let GlobalSignature::AdtConstructor(sig) = &globals.signatures[*gmid] {
                self.ctor_tag.insert(*spur, (sig.adt, sig.tag));
                let adt_id = self.name_map[&sig.adt];
                let ctor_name = interner.resolve(spur).to_string();
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
                        name: None,
                        field_types,
                    };
                }
                self.pending_ctor_names.push((adt_id, sig.tag, ctor_name));
            }
        }

        // Pass 3: record destructor semantics `(adt, variant, field)` for use
        // sites (`PureInst::AdtProj`). No accessor declarations are emitted —
        // the verifier mints projection ids (see `verify::mono`).
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
        // Reserve the predicate's Resource slot now (filled by `emit_predicate`)
        // so its id can serve as the snapshot ADT head (`Type::Snap(pred_id)`),
        // its address `LocId`, and be referenced by sibling predicates' footprints
        // (self & mutual recursion). The address location and snapshot are derived
        // on demand (`Resource::derive_location`/`derive_snapshot`) — not emitted.
        let pred_id = self.fresh_decl(&pred_name);
        self.name_map.insert(p.name.0, pred_id);
        // Register the predicate's location group tag (its address is grouped by
        // the predicate name, not by `pred_id`).
        self.groups.get_or_intern(&pred_name);
    }

    fn declare_field_accessor(&mut self, f: &typed::Field) {
        // A field's address is the result of an ordinary function `Ref -> Addr<T>`
        // (no bespoke location instruction or declaration). Register the location
        // **group** tag (addresses are grouped by field name), then emit the
        // address function as a normal `Declaration::Function`; `field_addr` calls
        // it like any function.
        let field_name = self.interner.resolve(&f.0.name.0).to_owned();
        self.groups.get_or_intern(&field_name);
        let field_id = self.fresh_decl(&field_name);
        // The field's address type: group = the field's tag, value = the field
        // type, bound = full permission `1/1`.
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

    /// The interned group tag for a field/predicate source name (registered during
    /// the declare phase).
    pub fn group_tag(&self, name: Spur) -> lasso::Spur {
        let s = self.interner.resolve(&name);
        self.groups
            .get(s)
            .unwrap_or_else(|| panic!("group tag `{s}` not registered"))
    }

    fn emit_predicate(&mut self, p: &typed::Predicate) -> Result<(), TranslationError> {
        // The Resource slot was reserved in `declare_predicate_accessors`.
        let pred_id = self.name_map[&p.name.0];
        let params: Vec<vmir::Type> = p.params.iter().map(|p| self.lower_type(&p.ty)).collect();
        // A concrete predicate body is self-framed (no precondition): params
        // occupy `Val::Temp(0..n)` and the spatial assertion accumulates onto an
        // empty initial heap, so emitted heaps start at `HeapVal::Temp(0)`.
        let body = match &p.body {
            None => None,
            Some(body_exp) => {
                let mut env: HashMap<Spur, vmir::Val> = HashMap::new();
                for (i, param) in p.params.iter().enumerate() {
                    env.insert(param.name.0, vmir::Val::Temp(i));
                }
                Some(resource::lower_spatial_never(
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

    fn emit_method_contracts(&mut self, m: &typed::Method) -> Result<(), TranslationError> {
        let name = self.interner.resolve(&m.name.0).to_owned();
        // Method itself gets a name slot only if it has a body (Phase B2 fills it).
        // We still intern it now to give it a stable id; Phase B2 sets the decl.
        if m.body.is_some() {
            let method_id = self.fresh_decl(&name);
            self.name_map.insert(m.name.0, method_id);
        }

        if let Some(requires) = &m.requires {
            let req_id = self.fresh_decl(&format!("{name}#requires"));
            self.method_requires.insert(m.name.0, req_id);
            let params: Vec<vmir::Type> = m.params.iter().map(|p| self.lower_type(&p.ty)).collect();
            let mut env: HashMap<Spur, vmir::Val> = HashMap::new();
            for (i, p) in m.params.iter().enumerate() {
                env.insert(p.name.0, vmir::Val::Temp(i));
            }
            // `#requires` is self-framed: accumulate from an empty initial heap,
            // emitted heaps start at `HeapVal::Temp(0)`.
            let body = resource::lower_spatial_never(
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
            let ens_id = self.fresh_decl(&format!("{name}#ensures"));
            self.method_ensures.insert(m.name.0, ens_id);
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
            // m#ensures's precondition resource is m#requires (when present).
            // The ensures delta is produced-only: accumulate from `HeapVal::Empty`
            // so a resource named in both requires and ensures isn't counted
            // twice. When there *is* a precondition, `HeapVal::Temp(0)` is the
            // reserved ctx slot (the precondition's heap delta, for future
            // pre-state / `old` reads), so emitted heaps start at `1`. With no
            // precondition the resource is self-framed and emitted heaps start at
            // `0`.
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
            // Two-state (`Ctx`) ensures reserves `HeapVal::Temp(0)` as the ctx /
            // pre-state slot (so emitted heaps start at 1); it is the heap that
            // `old(...)` reads. Self-framed ensures has no pre-state.
            let (heap_base, pre_state) = match &precond {
                vmir::Precond::Ctx(..) => (1, Some(vmir::HeapVal::Temp(0))),
                vmir::Precond::SelfFramed => (0, None),
            };
            let body = resource::lower_spatial_ensures(
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

    fn emit_method_body(&mut self, m: &typed::Method) -> Result<(), TranslationError> {
        let Some(body) = &m.body else { return Ok(()) };
        let method_id = *self
            .name_map
            .get(&m.name.0)
            .expect("method id should be interned");
        let method = method::lower_method(self, m, body)?;
        self.set_decl(method_id, vmir::Declaration::Method(method));
        Ok(())
    }

    fn finalize(mut self) -> vmir::Program {
        // Intern constructor names now — past every `fresh_decl`, so these
        // non-decl interner entries don't perturb the decl index invariant — and
        // attach them to their variants.
        for (adt_id, tag, name) in std::mem::take(&mut self.pending_ctor_names) {
            let ctor_id = self.vmir_interner.get_or_intern(&name);
            if let Some(vmir::Declaration::Adt(adt)) = self.decls[usize::from(adt_id)].as_mut() {
                adt.variants[tag].name = Some(ctor_id);
            }
        }
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

/// Lower a typed Silver type to a VMIR type.
///
/// `names` resolves a domain/ADT name `Spur` to its VMIR declaration id;
/// `generics` is the enclosing generic declaration's type-parameter list (used
/// to map a `Type::Generic` to its 0-based index). Both are empty in fully
/// concrete contexts (most call sites go through [`Builder::lower_type`]).
pub(crate) fn lower_type(
    names: &HashMap<Spur, vmir::MemberId>,
    generics: &[Spur],
    ty: &typed::Type,
) -> vmir::Type {
    match ty {
        typed::Type::Bool => vmir::Type::Bool,
        typed::Type::Int => vmir::Type::Int,
        typed::Type::Real => vmir::Type::Real,
        typed::Type::Ref => vmir::Type::Ref,
        typed::Type::Generic(id) => {
            let idx = generics
                .iter()
                .position(|p| *p == id.0)
                .expect("generic type parameter not in the enclosing declaration's scope");
            vmir::Type::Generic(idx)
        }
        typed::Type::Domain(id, args) => match names.get(&id.0) {
            // An ADT (or a modeled domain): keep the head + recurse on args so
            // the monomorphization key `(head, args)` is faithful.
            Some(&head) => {
                let args = args
                    .iter()
                    .map(|a| lower_type(names, generics, a))
                    .collect();
                vmir::Type::Domain(head, args)
            }
            // A domain with no VMIR declaration (not yet modeled). Fall back to
            // Ref, as before; ADTs are always present (declared in pass 1).
            None => vmir::Type::Ref,
        },
        // TODO: Seq/Set — modeled as builtin parametric types like Option.
        typed::Type::Collection(_) => vmir::Type::Ref,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::viper::{
        GlobalsCollector, IdentCollector, disambiguate, inline_macros, typecheck_program,
        viper_parser, walk::AstWalkable,
    };

    fn run(input: &str) -> vmir::Program {
        let mut program = viper_parser::vpr_program(input).expect("parse failed");
        let mut ident_collector = IdentCollector::default();
        program.walk_mut(&mut ident_collector);
        let interner = ident_collector.finalize();
        let mut globals_collector = GlobalsCollector::new(&interner);
        program.walk(&mut globals_collector);
        let globals = globals_collector.finalize().expect("globals error");
        disambiguate(&mut program, &interner, &globals).expect("disambiguation failed");
        inline_macros(&mut program, &interner).expect("macro inlining failed");
        let typed = typecheck_program(&mut program, &interner, &globals).expect("typecheck failed");
        translate(&typed, &interner, &globals).expect("translation failed")
    }

    #[test]
    fn translates_number_pred_simpler() {
        let input = r#"
predicate number(this: Ref)

method assign(this: Ref, value: Int)
    ensures number(this)

method read(this: Ref) returns (val: Int)
    requires number(this)
    ensures number(this)

method add(this: Ref, other: Ref) returns (res: Ref)
    requires number(this) && number(other)
    ensures number(this) && number(other) && number(res)
{
    var a: Int := read(this)
    var b: Int := read(other)
    var sum: Int := a + b
    assign(res, sum)
}
"#;
        let p = run(input);

        // No `@snap`/`@addr` decls are emitted; the snapshot type and address
        // location are derived from the predicate's own id.
        assert!(p.interner.get("number@snap").is_none());
        assert!(p.interner.get("number@addr").is_none());

        let pred_id = p.interner.get("number").expect("missing number");

        // Predicate itself is abstract; its address location is derived.
        let vmir::Declaration::Resource(pred) = &p.decls[pred_id] else {
            panic!("number must be a Resource");
        };
        assert!(
            pred.body.is_none(),
            "abstract predicate must have body=None"
        );
        let group = p.groups.get("number").expect("predicate group tag");
        let addr_fn = pred.derive_location(pred_id, group);
        assert_eq!(addr_fn.params, vec![vmir::Type::Ref]);
        assert_eq!(
            addr_fn.ret,
            vmir::Type::addr(group, vmir::Type::Snap(pred_id), vmir::Bound::Unbounded)
        );
        // Abstract predicate (no body) derives an opaque empty Domain snapshot.
        assert!(matches!(
            pred.derive_snapshot(),
            Some(vmir::Snapshot::Abstract(_))
        ));

        // Method contracts.
        for name in [
            "assign#ensures",
            "read#requires",
            "read#ensures",
            "add#requires",
            "add#ensures",
        ] {
            let id = p
                .interner
                .get(name)
                .unwrap_or_else(|| panic!("missing resource {name}"));
            assert!(
                matches!(&p.decls[id], vmir::Declaration::Resource(r) if r.body.is_some()),
                "{name} must be a concrete Resource"
            );
        }
        assert!(
            p.interner.get("assign#requires").is_none(),
            "assign has no precondition; #requires must not exist"
        );

        // The read#requires body must reference the predicate's address
        // location (`Location(number_id, ..)` — the predicate's own id) and an
        // Acc on its result, NOT a ResourceCall on number.
        let read_req_id = p.interner.get("read#requires").unwrap();
        let vmir::Declaration::Resource(read_req) = &p.decls[read_req_id] else {
            unreachable!();
        };
        let body = read_req.body.as_ref().unwrap();
        let mut saw_addr_call = false;
        let mut saw_acc = false;
        let number_group = p.groups.get("number").expect("number group tag");
        for inst in &body.insts {
            match &inst.kind {
                // An address is an ordinary call to the predicate's address
                // function (its own id), result type grouped under `number`.
                vmir::InstKind::Pure(
                    vmir::Type::Addr { group, .. },
                    vmir::PureInst::FunctionCall(None, fc),
                ) if *group == number_group && fc.function == pred_id => {
                    saw_addr_call = true;
                }
                vmir::InstKind::Heap(vmir::HeapInst::Combine { .. }) => saw_acc = true,
                _ => {}
            }
        }
        assert!(saw_addr_call, "read#requires must address number");
        assert!(saw_acc, "read#requires must contain an acc");

        // The `add` body's method contracts lower to resource inhale/exhale
        // instructions: an `exhale` of `add#requires` (implicit assert) and an
        // `inhale` of `add#ensures` (implicit assume). No standalone
        // Assert/Assume/ResourceCall remain.
        let add_id = p.interner.get("add").expect("missing add method");
        let vmir::Declaration::Method(add) = &p.decls[add_id] else {
            panic!("add must be a Method");
        };
        let kinds: Vec<_> = add.insts.iter().map(|i| &i.kind).collect();
        assert!(
            kinds
                .iter()
                .any(|k| matches!(k, vmir::InstKind::Heap(vmir::HeapInst::Exhale { .. }))),
            "add body must contain an exhale (requires)"
        );
        assert!(
            kinds
                .iter()
                .any(|k| matches!(k, vmir::InstKind::Heap(vmir::HeapInst::Inhale { .. }))),
            "add body must contain an inhale (ensures)"
        );
        assert!(
            !kinds
                .iter()
                .any(|k| matches!(k, vmir::InstKind::Assert(_) | vmir::InstKind::Assume(_))),
            "resource bools are now implicit in the combine; no standalone Assert/Assume"
        );

        // Display smoke: must not panic.
        let _ = format!("{p}");
    }

    #[test]
    fn div_inside_ternary_branch_carries_guard() {
        // The division only executes on the path where the guard holds, so the
        // emitted `Div` instruction must carry a non-empty path condition.
        let input = r#"
method m(x: Int, y: Int)
    requires y != 0 ? x / y == x : true
"#;
        let p = run(input);

        let req_id = p.interner.get("m#requires").expect("missing m#requires");
        let vmir::Declaration::Resource(req) = &p.decls[req_id] else {
            panic!("m#requires must be a Resource");
        };
        let body = req.body.as_ref().unwrap();

        let div = body
            .insts
            .iter()
            .find(|i| {
                matches!(
                    &i.kind,
                    vmir::InstKind::Pure(_, vmir::PureInst::Binary(vmir::BinOp::Div, _, _))
                )
            })
            .expect("requires body must contain a Div");
        assert!(
            !div.pc.conds.is_empty(),
            "Div inside the ternary then-branch must be guarded by a path condition"
        );
    }

    #[test]
    fn if_else_arms_carry_complementary_path_conditions() {
        // Each arm's guarded instructions (the `assert`s) must run under the
        // branch condition: `<c>` in the then-arm, `<!c>` in the else-arm.
        let input = r#"
method m(c: Bool, x: Int)
{
    if (c) { assert x == x } else { assert x == x }
}
"#;
        let p = run(input);
        let m_id = p.interner.get("m").expect("missing m");
        let vmir::Declaration::Method(m) = &p.decls[m_id] else {
            panic!("m must be a Method");
        };
        // params: c = Temp(0), x = Temp(1); the branch cond is the bare param c.
        let c = vmir::Val::Temp(0);
        let asserts: Vec<&vmir::PathConds> = m
            .insts
            .iter()
            .filter_map(|i| matches!(i.kind, vmir::InstKind::Assert(_)).then_some(&i.pc))
            .collect();
        assert_eq!(asserts.len(), 2, "one assert per arm");
        assert!(
            asserts
                .iter()
                .any(|pc| pc.conds == vec![(c.clone(), vmir::Polarity::Positive)]),
            "then-arm assert must be guarded by <c>"
        );
        assert!(
            asserts
                .iter()
                .any(|pc| pc.conds == vec![(c.clone(), vmir::Polarity::Negative)]),
            "else-arm assert must be guarded by <!c>"
        );
    }

    #[test]
    fn structured_nesting_keeps_pcs_minimal() {
        // Structured (reducible) nesting must never produce a pc fatter than the
        // enclosing split: inside `if a { if b { .. } }` the guard is exactly the
        // two real branch literals `<a, b>` (no materialized OR), and each merge
        // returns to the dominator's pc — the final `ensures` exhale carries `<>`.
        let input = r#"
field f: Int

method m(a: Bool, b: Bool, x: Ref)
    requires acc(x.f, 1/1)
    ensures acc(x.f, 1/1)
{
    if (a) {
        if (b) {
            assert true
        }
    }
}
"#;
        let p = run(input);
        let m_id = p.interner.get("m").expect("missing m");
        let vmir::Declaration::Method(m) = &p.decls[m_id] else {
            panic!("m must be a Method");
        };
        // params: a = Temp(0), b = Temp(1).
        let assert = m
            .insts
            .iter()
            .find(|i| matches!(i.kind, vmir::InstKind::Assert(_)))
            .expect("inner assert");
        assert_eq!(
            assert.pc.conds,
            vec![
                (vmir::Val::Temp(0), vmir::Polarity::Positive),
                (vmir::Val::Temp(1), vmir::Polarity::Positive),
            ],
            "nested guard must be the two real branch literals <a, b>, not a materialized OR"
        );
        let exhale = m
            .insts
            .iter()
            .find(|i| matches!(&i.kind, vmir::InstKind::Heap(vmir::HeapInst::Exhale { .. })))
            .expect("ensures exhale");
        assert!(
            exhale.pc.conds.is_empty(),
            "both merges return to the dominator pc; final exhale is <>, got {:?}",
            exhale.pc
        );
    }

    #[test]
    fn exhaustive_three_way_join_minimizes_to_empty_pc() {
        // A 3-way `goto` join whose reach is `a ∨ (!a∧b) ∨ (!a∧!b)` — a tautology.
        // Cube minimization (`merge_cubes`) collapses it, so the post-merge
        // `ensures` exhale must carry the trivial `<>`, not a materialized-OR
        // literal: the permission stays ungated.
        let input = r#"
field f: Int

method m(a: Bool, b: Bool, x: Ref)
    requires acc(x.f, 1/1)
    ensures acc(x.f, 1/1)
{
    if (a) { goto done }
    if (b) { goto done }
    label done
}
"#;
        let p = run(input);
        let m_id = p.interner.get("m").expect("missing m");
        let vmir::Declaration::Method(m) = &p.decls[m_id] else {
            panic!("m must be a Method");
        };
        let exhale = m
            .insts
            .iter()
            .find(|i| matches!(&i.kind, vmir::InstKind::Heap(vmir::HeapInst::Exhale { .. })))
            .expect("ensures lowers to an exhale");
        assert!(
            exhale.pc.conds.is_empty(),
            "exhaustive 3-way join must minimize to <>, got {:?}",
            exhale.pc
        );
    }

    #[test]
    fn join_inserts_phi_for_divergent_variable() {
        // `r` takes different values on the two arms, so the merge block must
        // reconcile it with a phi `c ? a : b`; the merged value flows into the
        // postcondition with the trivial `<>` path condition.
        let input = r#"
method m(c: Bool, a: Int, b: Int) returns (r: Int)
{
    if (c) { r := a } else { r := b }
}
"#;
        let p = run(input);
        let m_id = p.interner.get("m").expect("missing m");
        let vmir::Declaration::Method(m) = &p.decls[m_id] else {
            panic!("m must be a Method");
        };
        // params: c=Temp(0), a=Temp(1), b=Temp(2); ret r=Temp(3).
        let phi = m
            .insts
            .iter()
            .find(|i| {
                matches!(
                    &i.kind,
                    vmir::InstKind::Pure(_, vmir::PureInst::Ternary(c, t, e))
                        if *c == vmir::Val::Temp(0)
                            && *t == vmir::Val::Temp(1)
                            && *e == vmir::Val::Temp(2)
                )
            })
            .expect("merge must emit phi `c ? a : b`");
        assert!(phi.pc.conds.is_empty(), "phi itself is unguarded");
    }

    #[test]
    fn lowers_generic_adt_type_parameters() {
        // A generic ADT's declared field types keep their type parameters
        // (`Generic(i)`) and nested ADT structure; a use at a concrete
        // instantiation lowers to `Domain(head, [concrete args])` — never the
        // erased `Ref` placeholder, so the monomorphization key is faithful.
        let input = r#"
adt List[T] {
    Nil()
    Cons(head: T, tail: List[T])
}

function len(l: List[Int]): Int
"#;
        let p = run(input);
        let list_id = p.interner.get("List").expect("missing List");

        let vmir::Declaration::Adt(adt) = &p.decls[list_id] else {
            panic!("List must be an Adt");
        };
        // Variant 0 = `Nil()` (no fields); variant 1 = `Cons(?0, List[?0])`.
        assert!(adt.variants[0].field_types.is_empty(), "Nil has no fields");
        assert_eq!(
            adt.variants[1].field_types,
            vec![
                vmir::Type::Generic(0),
                vmir::Type::Domain(list_id, Box::new([vmir::Type::Generic(0)])),
            ],
            "Cons field types must be [?0, List[?0]], not erased to Ref"
        );

        // `len`'s parameter is `List[Int]` — a concrete monomorphization.
        let len_id = p.interner.get("len").expect("missing len");
        let vmir::Declaration::Function(func) = &p.decls[len_id] else {
            panic!("len must be a Function");
        };
        assert_eq!(
            func.params,
            vec![vmir::Type::Domain(list_id, Box::new([vmir::Type::Int]))],
            "len's param must lower to List[Int], not Ref"
        );
    }
}
