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
//! Monomorphization is keyed by `(adt, type-args)`: a non-generic ADT has a
//! single `args = []` instance; a generic ADT (e.g. the builtin `Option`,
//! injected by [`crate::verify::prelude`]) gets one instance per concrete type
//! argument tuple it is used at. There is no `Option`-specific machinery — the
//! verifier only needs the `Option` ADT's member id (see
//! [`MonoRegistry::option_adt`]).

use std::collections::HashMap;

use crate::verify::analysis::ConstFold;
use crate::verify::lang::Symbolic;
use crate::verify::prelude::OPTION;
use crate::verify::rewrite::{proj_rule, tag_rule};
use crate::vmir::{Adt, Declaration, MemberId, Program, Type};

type Rule = egg::Rewrite<Symbolic, ConstFold>;

/// Stable verifier ids for every monomorphic ADT constructor / projection /
/// tag, plus the reduction rules that fire over them. Keyed by
/// `(adt, type-args[, variant[, field]])`.
pub struct MonoRegistry {
    cons: HashMap<(MemberId, Vec<Type>, usize), MemberId>,
    proj: HashMap<(MemberId, Vec<Type>, usize, usize), MemberId>,
    tag: HashMap<(MemberId, Vec<Type>), MemberId>,
    /// The builtin `Option` ADT's declaration id (`None` if the program has no
    /// `Option`, e.g. a unit test with no prelude).
    option_adt: Option<MemberId>,
    /// Display names for minted ids (which are outside the interner).
    names: HashMap<MemberId, String>,
    rules: Vec<Rule>,
}

/// Whether any of an ADT's field types mentions a type parameter.
fn is_generic(adt: &Adt) -> bool {
    adt.variants
        .iter()
        .flat_map(|v| &v.field_types)
        .any(|t| matches!(t, Type::Generic(_)))
}

impl MonoRegistry {
    /// An empty registry (no ADTs). For tests / programs without ADTs.
    #[cfg(test)]
    pub fn empty() -> Self {
        MonoRegistry {
            cons: HashMap::new(),
            proj: HashMap::new(),
            tag: HashMap::new(),
            option_adt: None,
            names: HashMap::new(),
            rules: Vec::new(),
        }
    }

    /// Derive the registry from a program's `Adt` declarations and the
    /// monomorphizations they are used at. Minted ids start past every real
    /// declaration id, so they never collide with one.
    pub fn build(program: &Program) -> Self {
        let mut reg = MonoRegistry {
            cons: HashMap::new(),
            proj: HashMap::new(),
            tag: HashMap::new(),
            option_adt: program.interner.get(OPTION),
            names: HashMap::new(),
            rules: Vec::new(),
        };
        let mut next = program.interner.len();

        // Which monomorphic instances to mint, in deterministic order. Each is
        // `(adt-head, type-args, per-variant field counts)`:
        // - every non-generic ADT declaration at `[]`;
        // - `Option[elem]` for each distinct predicate-snapshot field type;
        // - each foldable predicate's snapshot: a single-variant ADT (head = the
        //   `@snap` Domain) over the footprint field types.
        // (Generic *user* ADTs at non-empty args are minted lazily on use once
        // allocation is dynamic; the eager build covers what static decls imply.)
        let mut specs: Vec<(MemberId, Vec<Type>, Vec<usize>)> = Vec::new();
        for (adt_id, decl) in program.decls.iter_enumerated() {
            if let Declaration::Adt(adt) = decl
                && !is_generic(adt)
            {
                specs.push((adt_id, Vec::new(), variant_field_counts(adt)));
            }
        }
        if let Some(opt) = reg.option_adt
            && let Declaration::Adt(adt) = &program.decls[opt]
        {
            let counts = variant_field_counts(adt);
            for elem in option_element_types(program) {
                specs.push((opt, vec![elem], counts.clone()));
            }
        }
        for decl in &program.decls {
            if let Declaration::Resource(r) = decl
                && let Some(snap) = &r.snapshot
            {
                specs.push((snap.snap, Vec::new(), vec![snap.field_types.len()]));
            }
        }

        for (adt_id, args, field_counts) in specs {
            mint_mono(&mut reg, &mut next, program, adt_id, &args, &field_counts);
        }
        reg
    }

    /// Constructor id for variant `variant` of `adt[args]`.
    pub fn cons(&self, adt: MemberId, args: &[Type], variant: usize) -> MemberId {
        self.cons[&(adt, args.to_vec(), variant)]
    }

    /// Field-`field` projection id of variant `variant` of `adt[args]`.
    pub fn proj(&self, adt: MemberId, args: &[Type], variant: usize, field: usize) -> MemberId {
        self.proj[&(adt, args.to_vec(), variant, field)]
    }

    /// Discriminator-tag id of `adt[args]`.
    pub fn tag(&self, adt: MemberId, args: &[Type]) -> MemberId {
        self.tag[&(adt, args.to_vec())]
    }

    /// The builtin `Option` ADT's declaration id.
    pub fn option_adt(&self) -> MemberId {
        self.option_adt.expect("Option prelude not injected")
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

/// Mint the constructor / projection / tag ids and reduction rules for one
/// monomorphic instance `adt[args]` whose variants have the given field counts.
fn mint_mono(
    reg: &mut MonoRegistry,
    next: &mut usize,
    program: &Program,
    adt: MemberId,
    args: &[Type],
    field_counts: &[usize],
) {
    let label = mono_label(program, adt, args);
    let mut mint = |reg: &mut MonoRegistry, name: String| {
        let id = MemberId(*next);
        *next += 1;
        reg.names.insert(id, name);
        id
    };

    let tag_id = mint(reg, format!("{label}@tag"));
    reg.tag.insert((adt, args.to_vec()), tag_id);

    let mut ctor_tags = HashMap::new();
    for (variant, &fields) in field_counts.iter().enumerate() {
        let cons_id = mint(reg, format!("{label}#{variant}"));
        reg.cons.insert((adt, args.to_vec(), variant), cons_id);
        ctor_tags.insert(cons_id, variant);

        for field in 0..fields {
            let proj_id = mint(reg, format!("{label}#{variant}.{field}"));
            reg.proj
                .insert((adt, args.to_vec(), variant, field), proj_id);
            reg.rules.push(proj_rule(proj_id, cons_id, field));
        }
    }
    reg.rules.push(tag_rule(tag_id, ctor_tags));
}

/// Per-variant field counts of an ADT declaration, in variant order.
fn variant_field_counts(adt: &Adt) -> Vec<usize> {
    adt.variants.iter().map(|v| v.field_types.len()).collect()
}

/// The distinct element types `Option` is monomorphized at: each predicate
/// snapshot's field types (a snapshot member is `(perm>0) ? Some(field) :
/// None`). Order-stable, de-duplicated.
fn option_element_types(program: &Program) -> Vec<Type> {
    let mut elems: Vec<Type> = Vec::new();
    for decl in &program.decls {
        let Declaration::Resource(r) = decl else {
            continue;
        };
        let Some(snap) = &r.snapshot else { continue };
        for elem in &snap.field_types {
            if !elems.contains(elem) {
                elems.push(elem.clone());
            }
        }
    }
    elems
}

/// A readable label for a monomorphic instance, e.g. `Option` or `Option[Int]`.
fn mono_label(program: &Program, adt: MemberId, args: &[Type]) -> String {
    let head = program.interner.resolve(&adt);
    if args.is_empty() {
        head.to_string()
    } else {
        let inner: Vec<String> = args.iter().map(|a| format!("{a}")).collect();
        format!("{head}[{}]", inner.join(", "))
    }
}
