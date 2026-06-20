//! Verifier-side ADT id registry, derived once from the program's `Adt`
//! declarations.
//!
//! Each ADT operation (`PureInst::{AdtCons,AdtProj,AdtTag}`) is interpreted as a
//! `Symbolic::FuncApp` over a **verifier-minted** member id — distinct from any
//! VMIR declaration id, so no synthetic `@tag`/`@dtor`/constructor declarations
//! need exist. The ids are a deterministic function of declaration order, hence
//! **stable across verification contexts** — required so a resource
//! certificate's grafted e-nodes congruence-match the caller's.
//!
//! User ADTs are keyed purely by `(adt, variant[, field])`: any generic
//! monomorphization is already a distinct `Adt` declaration upstream. `Option`
//! is the exception — it is never a VMIR declaration but a verifier-internal
//! snapshot-membership type, monomorphized here per element type (one set of
//! `Some`/`None`/`value`/`tag` ids per distinct predicate-snapshot field type).

use std::collections::HashMap;

use crate::verify::analysis::ConstFold;
use crate::verify::lang::Symbolic;
use crate::verify::rewrite::{proj_rule, tag_rule};
use crate::vmir::{Declaration, MemberId, Program, Type};

type Rule = egg::Rewrite<Symbolic, ConstFold>;

/// The verifier-minted ids for one monomorphic `Option[elem]` — the snapshot
/// membership ADT. `Some` is variant 0 (field 0 = `value`), `None` variant 1.
#[derive(Debug, Clone, Copy)]
pub struct OptionIds {
    pub some: MemberId,
    pub none: MemberId,
    pub value: MemberId,
    pub tag: MemberId,
}

/// Stable verifier ids for every ADT constructor / projection / tag, plus the
/// reduction rules that fire over them.
pub struct MonoRegistry {
    cons: HashMap<(MemberId, usize), MemberId>,
    proj: HashMap<(MemberId, usize, usize), MemberId>,
    tag: HashMap<MemberId, MemberId>,
    /// Verifier-internal `Option[elem]` monomorphizations, keyed by element
    /// type. `Option` is never a VMIR declaration — it lives entirely here.
    option: HashMap<Type, OptionIds>,
    /// The generic `Option` type head (for `Option[elem]` value types).
    option_head: MemberId,
    /// Display names for minted ids (which are outside the interner).
    names: HashMap<MemberId, String>,
    rules: Vec<Rule>,
}

impl MonoRegistry {
    /// An empty registry (no ADTs). For tests / programs without ADTs.
    #[cfg(test)]
    pub fn empty() -> Self {
        MonoRegistry {
            cons: HashMap::new(),
            proj: HashMap::new(),
            tag: HashMap::new(),
            option: HashMap::new(),
            option_head: MemberId(0),
            names: HashMap::new(),
            rules: Vec::new(),
        }
    }

    /// Derive the registry from a program's `Adt` declarations (and the
    /// `Option[T]` monomorphizations its predicate snapshots need). Minted ids
    /// start past every real declaration id, so they never collide with one.
    pub fn build(program: &Program) -> Self {
        let mut reg = MonoRegistry {
            cons: HashMap::new(),
            proj: HashMap::new(),
            tag: HashMap::new(),
            option: HashMap::new(),
            option_head: MemberId(0),
            names: HashMap::new(),
            rules: Vec::new(),
        };
        let mut next = program.interner.len();
        let mut mint = |reg: &mut MonoRegistry, name: String| {
            let id = MemberId(next);
            next += 1;
            reg.names.insert(id, name);
            id
        };

        reg.option_head = mint(&mut reg, "Option".to_string());

        for (adt_id, decl) in program.decls.iter_enumerated() {
            let Declaration::Adt(adt) = decl else {
                continue;
            };
            let adt_name = program.interner.resolve(&adt_id);

            let tag_id = mint(&mut reg, format!("{adt_name}@tag"));
            reg.tag.insert(adt_id, tag_id);

            let mut ctor_tags = HashMap::new();
            for (variant, ctor) in adt.variants.iter().enumerate() {
                let cons_id = mint(&mut reg, format!("{adt_name}#{variant}"));
                reg.cons.insert((adt_id, variant), cons_id);
                ctor_tags.insert(cons_id, variant);

                for field in 0..ctor.field_types.len() {
                    let proj_id = mint(&mut reg, format!("{adt_name}#{variant}.{field}"));
                    reg.proj.insert((adt_id, variant, field), proj_id);
                    reg.rules.push(proj_rule(proj_id, cons_id, field));
                }
            }
            reg.rules.push(tag_rule(tag_id, ctor_tags));
        }

        // `Option[elem]` monomorphizations, one per distinct predicate-snapshot
        // field type. Each snapshot member is `(perm>0) ? Some(v) : None`; the
        // snapshot projection's declared return type is the element type.
        for decl in &program.decls {
            let Declaration::Resource(r) = decl else {
                continue;
            };
            let Some(snap) = &r.snapshot else { continue };
            for &proj in &snap.projs {
                let elem = match &program.decls[proj] {
                    Declaration::Function(f) => f.ret.clone(),
                    _ => Type::Int,
                };
                if reg.option.contains_key(&elem) {
                    continue;
                }
                let some = mint(&mut reg, "Some".to_string());
                let none = mint(&mut reg, "None".to_string());
                let value = mint(&mut reg, "Option@value".to_string());
                let tag = mint(&mut reg, "Option@tag".to_string());
                reg.rules.push(proj_rule(value, some, 0));
                reg.rules
                    .push(tag_rule(tag, HashMap::from([(some, 0), (none, 1)])));
                reg.option.insert(
                    elem,
                    OptionIds {
                        some,
                        none,
                        value,
                        tag,
                    },
                );
            }
        }
        reg
    }

    /// Constructor id for variant `variant` of ADT `adt`.
    pub fn cons(&self, adt: MemberId, variant: usize) -> MemberId {
        self.cons[&(adt, variant)]
    }

    /// Field-`field` projection id of variant `variant` of ADT `adt`.
    pub fn proj(&self, adt: MemberId, variant: usize, field: usize) -> MemberId {
        self.proj[&(adt, variant, field)]
    }

    /// Discriminator-tag id of ADT `adt`.
    pub fn tag(&self, adt: MemberId) -> MemberId {
        self.tag[&adt]
    }

    /// The verifier-minted `Option[elem]` ids.
    pub fn option(&self, elem: &Type) -> OptionIds {
        self.option[elem]
    }

    /// The `Option[elem]` value type (the snapshot membership type).
    pub fn option_type(&self, elem: Type) -> Type {
        Type::Domain(self.option_head, Box::new([elem]))
    }

    /// The cons/proj/tag reduction rules to inject into a context's runner.
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    /// Display name for a minted id (`None` if `m` is not registry-minted).
    pub fn name(&self, m: MemberId) -> Option<&str> {
        self.names.get(&m).map(String::as_str)
    }
}
