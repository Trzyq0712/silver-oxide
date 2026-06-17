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
    /// Declarations indexed by MemberId. Empty `None` slots are filled in
    /// later phases.
    decls: Vec<Option<vmir::Declaration>>,
    /// Maps Silver `Spur` names to VMIR `MemberId`s.
    pub name_map: HashMap<Spur, vmir::MemberId>,
    /// Maps a predicate's `Spur` to its `@snap` Domain MemberId.
    pub pred_snap: HashMap<Spur, vmir::MemberId>,
    /// Maps a predicate's `Spur` to its `@addr` Function MemberId.
    pub pred_addr: HashMap<Spur, vmir::MemberId>,
    /// Maps a field's `Spur` to its `@addr` Function MemberId.
    pub field_addr: HashMap<Spur, vmir::MemberId>,
    /// Maps a method's `Spur` to its `@requires` Resource MemberId (if any).
    pub method_requires: HashMap<Spur, vmir::MemberId>,
    /// Maps a method's `Spur` to its `@ensures` Resource MemberId (if any).
    pub method_ensures: HashMap<Spur, vmir::MemberId>,
    /// Maps an ADT's `Spur` to its synthesized `@tag` Function MemberId.
    pub adt_tag_fn: HashMap<Spur, vmir::MemberId>,
    /// Maps a constructor's `Spur` to `(owning ADT `Spur`, tag index)`.
    pub ctor_tag: HashMap<Spur, (Spur, usize)>,
    /// Maps a destructor's `Spur` to its synthesized accessor Function MemberId.
    pub dtor_accessor: HashMap<Spur, vmir::MemberId>,
    /// ADT metadata for the verifier (tag-fn → ctor → tag index).
    pub adt_meta: vmir::AdtMeta,
    /// Per-predicate fold/unfold metadata (addr fn + snapshot cons/projs).
    pub pred_meta: HashMap<vmir::MemberId, vmir::PredMeta>,
}

impl<'a> Builder<'a> {
    fn new(interner: &'a Interner, globals: &'a Globals) -> Self {
        Self {
            interner,
            globals,
            vmir_interner: Rodeo::new(),
            decls: Vec::new(),
            name_map: HashMap::new(),
            pred_snap: HashMap::new(),
            pred_addr: HashMap::new(),
            field_addr: HashMap::new(),
            method_requires: HashMap::new(),
            method_ensures: HashMap::new(),
            adt_tag_fn: HashMap::new(),
            ctor_tag: HashMap::new(),
            dtor_accessor: HashMap::new(),
            adt_meta: vmir::AdtMeta::default(),
            pred_meta: HashMap::new(),
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
    /// `@ensures`). Such calls carry a context heap; self-framed resources don't.
    pub(crate) fn is_ctx_resource(&self, id: vmir::MemberId) -> bool {
        matches!(
            self.decls.get(usize::from(id)),
            Some(Some(vmir::Declaration::Resource(r))) if !matches!(r.precond, vmir::Precond::SelfFramed)
        )
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

        // Pass 1: ADTs and their `@tag` functions.
        for (spur, gmid) in &entries {
            if let GlobalSignature::Adt(_) = &globals.signatures[*gmid] {
                let name = interner.resolve(spur).to_string();
                let adt_id = self.fresh_decl(&name);
                self.set_decl(adt_id, vmir::Declaration::Adt(vmir::Adt {}));
                let tag_id = self.fresh_decl(&format!("{name}@tag"));
                self.set_decl(
                    tag_id,
                    vmir::Declaration::Function(vmir::Function {
                        params: vec![vmir::Type::Ref],
                        ret: vmir::Type::Int,
                        body: None,
                    }),
                );
                self.adt_tag_fn.insert(*spur, tag_id);
                self.adt_meta.tag_fns.insert(tag_id, HashMap::new());
            }
        }

        // Pass 2: user functions and ADT constructors.
        for (spur, gmid) in &entries {
            match &globals.signatures[*gmid] {
                GlobalSignature::Function(sig) => {
                    let name = interner.resolve(spur).to_string();
                    let id = self.fresh_decl(&name);
                    let params = sig.params.iter().map(lower_type).collect();
                    let ret = lower_type(&sig.ret);
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
                GlobalSignature::AdtConstructor(sig) => {
                    let name = interner.resolve(spur).to_string();
                    let id = self.fresh_decl(&name);
                    let params = sig.params.iter().map(lower_type).collect();
                    let ret = lower_type(&sig.ret);
                    self.set_decl(
                        id,
                        vmir::Declaration::Function(vmir::Function {
                            params,
                            ret,
                            body: None,
                        }),
                    );
                    self.name_map.insert(*spur, id);
                    self.ctor_tag.insert(*spur, (sig.adt, sig.tag));
                    let tag_fn = self.adt_tag_fn[&sig.adt];
                    self.adt_meta
                        .tag_fns
                        .get_mut(&tag_fn)
                        .expect("adt tag fn declared in pass 1")
                        .insert(id, sig.tag);
                }
                _ => {}
            }
        }

        // Pass 3: destructor accessor functions (constructors are now in the
        // name map). One accessor per destructor name; `accessor(ctor(..))`
        // projects the corresponding field.
        let mut dtors: Vec<_> = globals.dtor_by_name.iter().collect();
        dtors.sort_by_key(|(s, _)| interner.resolve(s).to_string());
        for (dtor_spur, info) in dtors {
            let adt_name = interner.resolve(&info.adt);
            let dtor_name = interner.resolve(dtor_spur);
            let id = self.fresh_decl(&format!("{adt_name}@{dtor_name}"));
            self.set_decl(
                id,
                vmir::Declaration::Function(vmir::Function {
                    params: vec![vmir::Type::Ref],
                    ret: lower_type(&info.ty),
                    body: None,
                }),
            );
            self.dtor_accessor.insert(*dtor_spur, id);
            let ctor_id = self.name_map[&info.ctor];
            self.adt_meta.dtors.insert(id, (ctor_id, info.index));
        }
    }

    fn declare_predicate_accessors(&mut self, p: &typed::Predicate) {
        let pred_name = self.interner.resolve(&p.name.0);
        let snap_id = self.fresh_decl(&format!("{pred_name}@snap"));
        self.set_decl(snap_id, vmir::Declaration::Domain(vmir::Domain {}));
        let addr_id = self.fresh_decl(&format!("{pred_name}@addr"));
        let addr_fn = vmir::Function {
            params: p.params.iter().map(|p| lower_type(&p.ty)).collect(),
            ret: vmir::Type::Addr(Box::new(vmir::Type::domain(snap_id))),
            body: None,
        };
        self.set_decl(addr_id, vmir::Declaration::Function(addr_fn));
        self.pred_snap.insert(p.name.0, snap_id);
        self.pred_addr.insert(p.name.0, addr_id);
    }

    fn declare_field_accessor(&mut self, f: &typed::Field) {
        // A field's address function carries the field's *original* name (no
        // `@addr` suffix). The field name has exactly one VMIR meaning — its
        // `Ref -> Addr<T>` accessor — so the bare name is canonical. The `@`
        // suffixes (`@addr`, `@snap`, …) are reserved for *generated* implicit
        // members that sit alongside a user-named resource (e.g. a predicate's
        // `P@addr` / `P@snap`).
        let field_name = self.interner.resolve(&f.0.name.0).to_owned();
        let addr_id = self.fresh_decl(&field_name);
        let addr_fn = vmir::Function {
            params: vec![vmir::Type::Ref],
            ret: vmir::Type::Addr(Box::new(lower_type(&f.0.ty))),
            body: None,
        };
        self.set_decl(addr_id, vmir::Declaration::Function(addr_fn));
        self.field_addr.insert(f.0.name.0, addr_id);
    }

    fn emit_predicate(&mut self, p: &typed::Predicate) -> Result<(), TranslationError> {
        let name = self.interner.resolve(&p.name.0).to_owned();
        let pred_id = self.fresh_decl(&name);
        self.name_map.insert(p.name.0, pred_id);
        let params: Vec<vmir::Type> = p.params.iter().map(|p| lower_type(&p.ty)).collect();
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

        // Synthesize the snapshot ADT for a foldable (flat) concrete predicate:
        // a constructor `P@snap@cons` over the footprint field values and one
        // accessor `P@snap@proj_i` per slot, registered so the projection
        // reduction makes fold→unfold round-trips exact. See `PredMeta`.
        if let Some(body_exp) = &p.body
            && let Some(types) = self.flat_footprint_types(body_exp)
        {
            let snap_id = self.pred_snap[&p.name.0];
            let addr_id = self.pred_addr[&p.name.0];
            let cons_id = self.fresh_decl(&format!("{name}@snap@cons"));
            self.set_decl(
                cons_id,
                vmir::Declaration::Function(vmir::Function {
                    params: types.clone(),
                    ret: vmir::Type::domain(snap_id),
                    body: None,
                }),
            );
            let mut snap_projs = Vec::with_capacity(types.len());
            for (i, ty) in types.iter().enumerate() {
                let proj_id = self.fresh_decl(&format!("{name}@snap@{i}"));
                self.set_decl(
                    proj_id,
                    vmir::Declaration::Function(vmir::Function {
                        params: vec![vmir::Type::domain(snap_id)],
                        ret: ty.clone(),
                        body: None,
                    }),
                );
                self.adt_meta.dtors.insert(proj_id, (cons_id, i));
                snap_projs.push(proj_id);
            }
            self.pred_meta.insert(
                pred_id,
                vmir::PredMeta {
                    addr_fn: addr_id,
                    snap_cons: cons_id,
                    snap_projs,
                },
            );
        }
        Ok(())
    }

    /// The ordered field-types of a **foldable** predicate body: a conjunction
    /// of `acc(_.f, _)` over fields (with optional pure conjuncts), now also
    /// through conditionals (`b ==> acc(..)`, `c ? .. : ..`). The conditional's
    /// guard is *not* captured here — it lives in the resource body's gated
    /// permission (`perm = b ? p : 0`), which the verifier lifts to the
    /// snapshot member's `present` discriminant. Returns `None` for nested
    /// predicates (not foldable yet). The slot order must match the body
    /// instruction stream, so conditional branches contribute in source order.
    fn flat_footprint_types(&self, exp: &typed::SpatialExp<!>) -> Option<Vec<vmir::Type>> {
        use typed::ResourceExpKind as R;
        use typed::SpatialExpKind as S;
        match &*exp.0 {
            S::Conj(l, r) => {
                let mut v = self.flat_footprint_types(l)?;
                v.extend(self.flat_footprint_types(r)?);
                Some(v)
            }
            S::Acc(res, _perm) => match &*res.0 {
                R::Field(_base, fname) => {
                    let ty = self.globals.resolve(fname.0)?.as_field()?;
                    Some(vec![lower_type(ty)])
                }
                R::PredicateCall(_) => None,
            },
            S::Pure(_) => Some(vec![]),
            // `b ==> A`: A's slots, with permission gated by `b` in the body.
            S::Implies(_cond, inner) => self.flat_footprint_types(inner),
            // `c ? A : B`: A's slots then B's slots (each gated by the branch
            // condition in the body), in source order.
            S::Ternary { then, else_, .. } => {
                let mut v = self.flat_footprint_types(then)?;
                v.extend(self.flat_footprint_types(else_)?);
                Some(v)
            }
        }
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
            let req_id = self.fresh_decl(&format!("{name}@requires"));
            self.method_requires.insert(m.name.0, req_id);
            let params: Vec<vmir::Type> = m.params.iter().map(|p| lower_type(&p.ty)).collect();
            let mut env: HashMap<Spur, vmir::Val> = HashMap::new();
            for (i, p) in m.params.iter().enumerate() {
                env.insert(p.name.0, vmir::Val::Temp(i));
            }
            // `@requires` is self-framed: accumulate from an empty initial heap,
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
            let ens_id = self.fresh_decl(&format!("{name}@ensures"));
            self.method_ensures.insert(m.name.0, ens_id);
            let mut params: Vec<vmir::Type> = m.params.iter().map(|p| lower_type(&p.ty)).collect();
            params.extend(m.rets.iter().map(|r| lower_type(&r.ty)));
            let mut env: HashMap<Spur, vmir::Val> = HashMap::new();
            for (i, p) in m.params.iter().enumerate() {
                env.insert(p.name.0, vmir::Val::Temp(i));
            }
            for (i, r) in m.rets.iter().enumerate() {
                env.insert(r.name.0, vmir::Val::Temp(m.params.len() + i));
            }
            // m@ensures's precondition resource is m@requires (when present).
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
            let heap_base = match &precond {
                vmir::Precond::Ctx(..) => 1,
                vmir::Precond::SelfFramed => 0,
            };
            let body = resource::lower_spatial_ensures(
                self,
                &env,
                ensures,
                params.len(),
                vmir::HeapVal::Empty,
                heap_base,
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

    fn finalize(self) -> vmir::Program {
        let decls: TiVec<vmir::MemberId, vmir::Declaration> = self
            .decls
            .into_iter()
            .map(|o| o.expect("declaration slot left empty"))
            .collect();
        vmir::Program {
            decls,
            interner: self.vmir_interner,
            adt_meta: self.adt_meta,
            pred_meta: self.pred_meta,
        }
    }
}

pub(crate) fn lower_type(ty: &typed::Type) -> vmir::Type {
    match ty {
        typed::Type::Bool => vmir::Type::Bool,
        typed::Type::Int => vmir::Type::Int,
        typed::Type::Real => vmir::Type::Real,
        typed::Type::Ref => vmir::Type::Ref,
        typed::Type::Generic(_) | typed::Type::Collection(_) | typed::Type::Domain(_, _) => {
            // Not exercised by the target case. Use Ref as a placeholder; a
            // future round will introduce proper VMIR domain/collection types.
            vmir::Type::Ref
        }
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

        // Auto-emitted snap + addr for the predicate.
        let snap_id = p.interner.get("number@snap").expect("missing number@snap");
        assert!(matches!(p.decls[snap_id], vmir::Declaration::Domain(_)));

        let addr_id = p.interner.get("number@addr").expect("missing number@addr");
        let vmir::Declaration::Function(addr_fn) = &p.decls[addr_id] else {
            panic!("number@addr must be a Function");
        };
        assert_eq!(addr_fn.params, vec![vmir::Type::Ref]);
        assert!(matches!(
            &addr_fn.ret,
            vmir::Type::Addr(inner) if **inner == vmir::Type::domain(snap_id)
        ));

        // Predicate itself is abstract.
        let pred_id = p.interner.get("number").expect("missing number");
        let vmir::Declaration::Resource(pred) = &p.decls[pred_id] else {
            panic!("number must be a Resource");
        };
        assert!(
            pred.body.is_none(),
            "abstract predicate must have body=None"
        );

        // Method contracts.
        for name in [
            "assign@ensures",
            "read@requires",
            "read@ensures",
            "add@requires",
            "add@ensures",
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
            p.interner.get("assign@requires").is_none(),
            "assign has no precondition; @requires must not exist"
        );

        // The read@requires body must contain a FunctionCall to number@addr
        // and an Acc on its result, NOT a ResourceCall on number.
        let read_req_id = p.interner.get("read@requires").unwrap();
        let vmir::Declaration::Resource(read_req) = &p.decls[read_req_id] else {
            unreachable!();
        };
        let body = read_req.body.as_ref().unwrap();
        let mut saw_addr_call = false;
        let mut saw_acc = false;
        for inst in &body.insts {
            match &inst.kind {
                vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(_, fc))
                    if fc.function == addr_id =>
                {
                    saw_addr_call = true;
                }
                vmir::InstKind::Heap(vmir::HeapInst::Combine {
                    target: vmir::Target::Loc(_),
                    ..
                }) => saw_acc = true,
                _ => {}
            }
        }
        let _ = pred_id;
        assert!(saw_addr_call, "read@requires must call number@addr");
        assert!(saw_acc, "read@requires must contain an acc");

        // The `add` body's method contracts now lower to fused resource
        // combines: a `Sub` exhale of `add@requires` (implicit assert) and an
        // `Add` inhale of `add@ensures` (implicit assume), each a
        // `Combine { target: Resource(..) }`. No standalone Assert/Assume/
        // ResourceCall remain.
        let add_id = p.interner.get("add").expect("missing add method");
        let vmir::Declaration::Method(add) = &p.decls[add_id] else {
            panic!("add must be a Method");
        };
        let kinds: Vec<_> = add.insts.iter().map(|i| &i.kind).collect();
        let combine = |sign| {
            move |k: &&vmir::InstKind| {
                matches!(
                    k,
                    vmir::InstKind::Heap(vmir::HeapInst::Combine {
                        sign: s,
                        target: vmir::Target::Resource(_),
                        ..
                    }) if *s == sign
                )
            }
        };
        assert!(
            kinds.iter().any(combine(vmir::Sign::Sub)),
            "add body must contain a Sub resource combine (requires exhale)"
        );
        assert!(
            kinds.iter().any(combine(vmir::Sign::Add)),
            "add body must contain an Add resource combine (ensures inhale)"
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

        let req_id = p.interner.get("m@requires").expect("missing m@requires");
        let vmir::Declaration::Resource(req) = &p.decls[req_id] else {
            panic!("m@requires must be a Resource");
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
}
