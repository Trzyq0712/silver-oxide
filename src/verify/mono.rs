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
//! Generic ADTs are monomorphized upstream: each concrete instance (e.g.
//! `Option[Int]` vs `Option[Bool]`) is already a separate `Adt` declaration with
//! its own id, so keying purely by `(adt, variant[, field])` keeps
//! monomorphizations apart with no explicit type dimension.

use std::collections::HashMap;

use crate::verify::analysis::ConstFold;
use crate::verify::lang::Symbolic;
use crate::verify::rewrite::{proj_rule, tag_rule};
use crate::vmir::{Declaration, MemberId, Program};

type Rule = egg::Rewrite<Symbolic, ConstFold>;

/// Stable verifier ids for every ADT constructor / projection / tag, plus the
/// reduction rules that fire over them.
pub struct MonoRegistry {
    cons: HashMap<(MemberId, usize), MemberId>,
    proj: HashMap<(MemberId, usize, usize), MemberId>,
    tag: HashMap<MemberId, MemberId>,
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
            names: HashMap::new(),
            rules: Vec::new(),
        }
    }

    /// Derive the registry from a program's `Adt` declarations. Minted ids start
    /// past every real declaration id, so they never collide with one.
    pub fn build(program: &Program) -> Self {
        let mut reg = MonoRegistry {
            cons: HashMap::new(),
            proj: HashMap::new(),
            tag: HashMap::new(),
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

    /// The cons/proj/tag reduction rules to inject into a context's runner.
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    /// Display name for a minted id (`None` if `m` is not registry-minted).
    pub fn name(&self, m: MemberId) -> Option<&str> {
        self.names.get(&m).map(String::as_str)
    }
}
