//! Lowers Silver `final_ast::Program` to `vmir::Program`.
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

use crate::silver::{Globals, Interner, final_ast};
use crate::vmir;

pub mod errors;
mod method;
mod pure_exp;
mod resource;

pub use errors::TranslationError;

/// Build a `vmir::Program` from a typed `final_ast::Program`.
pub fn translate(
    program: &final_ast::Program,
    interner: &Interner,
    globals: &Globals,
) -> Result<vmir::Program, Vec<TranslationError>> {
    let mut builder = Builder::new(interner, globals);
    let mut errors = Vec::new();

    // Phase A: synthesise @snap (predicates) and @addr (predicates + fields).
    for decl in &program.0 {
        match decl {
            final_ast::Declaration::Predicate(p) => builder.declare_predicate_accessors(p),
            final_ast::Declaration::Field(f) => builder.declare_field_accessor(f),
            final_ast::Declaration::Function(_) | final_ast::Declaration::Method(_) => {}
        }
    }

    // Phase B1: emit Resource declarations (predicates + method contracts).
    for decl in &program.0 {
        match decl {
            final_ast::Declaration::Predicate(p) => {
                if let Err(e) = builder.emit_predicate(p) {
                    errors.push(e);
                }
            }
            final_ast::Declaration::Method(m) => {
                if let Err(e) = builder.emit_method_contracts(m) {
                    errors.push(e);
                }
            }
            _ => {}
        }
    }

    // Phase B2: emit Method bodies.
    for decl in &program.0 {
        if let final_ast::Declaration::Method(m) = decl
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

    fn set_decl(&mut self, id: vmir::MemberId, decl: vmir::Declaration) {
        let slot = &mut self.decls[usize::from(id)];
        debug_assert!(slot.is_none(), "decl slot filled twice");
        *slot = Some(decl);
    }

    fn declare_predicate_accessors(&mut self, p: &final_ast::Predicate) {
        let pred_name = self.interner.resolve(&p.name.0);
        let snap_id = self.fresh_decl(&format!("{pred_name}@snap"));
        self.set_decl(snap_id, vmir::Declaration::Domain(vmir::Domain {}));
        let addr_id = self.fresh_decl(&format!("{pred_name}@addr"));
        let addr_fn = vmir::Function {
            params: p.params.iter().map(|p| lower_type(&p.ty)).collect(),
            ret: vmir::Type::Addr(Box::new(vmir::Type::Domain(snap_id))),
            body: None,
        };
        self.set_decl(addr_id, vmir::Declaration::Function(addr_fn));
        self.pred_snap.insert(p.name.0, snap_id);
        self.pred_addr.insert(p.name.0, addr_id);
    }

    fn declare_field_accessor(&mut self, f: &final_ast::Field) {
        let field_name = self.interner.resolve(&f.0.name.0);
        let addr_id = self.fresh_decl(&format!("{field_name}@addr"));
        let addr_fn = vmir::Function {
            params: vec![vmir::Type::Ref],
            ret: vmir::Type::Addr(Box::new(lower_type(&f.0.ty))),
            body: None,
        };
        self.set_decl(addr_id, vmir::Declaration::Function(addr_fn));
        self.field_addr.insert(f.0.name.0, addr_id);
    }

    fn emit_predicate(&mut self, p: &final_ast::Predicate) -> Result<(), TranslationError> {
        let name = self.interner.resolve(&p.name.0).to_owned();
        let pred_id = self.fresh_decl(&name);
        self.name_map.insert(p.name.0, pred_id);
        let params: Vec<vmir::Type> = p.params.iter().map(|p| lower_type(&p.ty)).collect();
        let body = match &p.body {
            None => None,
            Some(_) => return Err(TranslationError::Unsupported("concrete predicate body")),
        };
        self.set_decl(
            pred_id,
            vmir::Declaration::Resource(vmir::Resource {
                params,
                requires: None,
                body,
            }),
        );
        Ok(())
    }

    fn emit_method_contracts(&mut self, m: &final_ast::Method) -> Result<(), TranslationError> {
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
            let body = resource::lower_spatial_never(self, &env, requires, params.len())?;
            self.set_decl(
                req_id,
                vmir::Declaration::Resource(vmir::Resource {
                    params,
                    requires: None,
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
            let body = resource::lower_spatial_ensures(self, &env, ensures, params.len())?;
            self.set_decl(
                ens_id,
                vmir::Declaration::Resource(vmir::Resource {
                    params,
                    requires: None,
                    body: Some(body),
                }),
            );
        }

        Ok(())
    }

    fn emit_method_body(&mut self, m: &final_ast::Method) -> Result<(), TranslationError> {
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
        }
    }
}

pub(crate) fn lower_type(ty: &final_ast::Type) -> vmir::Type {
    match ty {
        final_ast::Type::Bool => vmir::Type::Bool,
        final_ast::Type::Int => vmir::Type::Int,
        final_ast::Type::Real => vmir::Type::Real,
        final_ast::Type::Ref => vmir::Type::Ref,
        final_ast::Type::Collection(_) | final_ast::Type::Domain(_, _) => {
            // Not exercised by the target case. Use Ref as a placeholder; a
            // future round will introduce proper VMIR domain/collection types.
            vmir::Type::Ref
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::silver::{
        GlobalsCollector, IdentCollector, inline_macros, resolve_call_kinds, silver_parser,
        typecheck_program, walk::AstWalkable,
    };

    fn run(input: &str) -> vmir::Program {
        let mut program = silver_parser::sil_program(input).expect("parse failed");
        let mut ident_collector = IdentCollector::default();
        program.walk_mut(&mut ident_collector);
        let interner = ident_collector.finalize();
        let mut globals_collector = GlobalsCollector::new(&interner);
        program.walk(&mut globals_collector);
        let globals = globals_collector.finalize().expect("globals error");
        resolve_call_kinds(&mut program, &interner, &globals).expect("call resolution failed");
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
            vmir::Type::Addr(inner) if **inner == vmir::Type::Domain(snap_id)
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
                vmir::InstKind::Heap(vmir::HeapInst::Acc(_)) => saw_acc = true,
                // ResourceCall is now in MethodInstExt — by construction
                // unreachable here (ResourceInst's Ext slot is `!`).
                _ => {}
            }
        }
        let _ = pred_id;
        assert!(saw_addr_call, "read@requires must call number@addr");
        assert!(saw_acc, "read@requires must contain an acc");

        // Method add body must contain Sub, Add, Assert, Assume, ResourceCall.
        let add_id = p.interner.get("add").expect("missing add method");
        let vmir::Declaration::Method(add) = &p.decls[add_id] else {
            panic!("add must be a Method");
        };
        let kinds: Vec<_> = add.insts.iter().map(|i| &i.kind).collect();
        assert!(
            kinds
                .iter()
                .any(|k| matches!(k, vmir::InstKind::Heap(vmir::HeapInst::Sub(_, _)))),
            "add body must contain HeapInst::Sub"
        );
        assert!(
            kinds
                .iter()
                .any(|k| matches!(k, vmir::InstKind::Heap(vmir::HeapInst::Add(_, _)))),
            "add body must contain HeapInst::Add"
        );
        assert!(
            kinds
                .iter()
                .any(|k| matches!(k, vmir::InstKind::Ext(vmir::InstExt::Assert(_)))),
            "add body must contain MethodInstExt::Assert"
        );
        assert!(
            kinds
                .iter()
                .any(|k| matches!(k, vmir::InstKind::Ext(vmir::InstExt::Assume(_)))),
            "add body must contain MethodInstExt::Assume"
        );
        assert!(
            kinds
                .iter()
                .any(|k| matches!(k, vmir::InstKind::Ext(vmir::InstExt::ResourceCall(_)))),
            "add body must contain a ResourceCall"
        );

        // Display smoke: must not panic.
        let _ = format!("{p}");
    }
}
