//! Verifier-side ADT id allocator.
//!
//! ADT operations (`PureInst::{AdtCons,AdtProj,AdtTag}` and predicate snapshots)
//! are interpreted as `Symbolic::FuncApp`s over **verifier-minted** member ids,
//! distinct from any VMIR declaration id — so no synthetic `@tag`/`@dtor`/
//! constructor declarations exist. Ids are allocated **lazily on first use** of a
//! monomorphic instance `(adt, type-args)`; minting one mints its whole instance
//! (tag + every constructor + every projection) and appends its reduction rules.
//!
//! The allocator is owned by `verify::verify` and threaded `&mut` through each
//! (sequential) verification unit, so an instance gets the **same** id wherever
//! it appears — required for a resource certificate's grafted nodes to
//! congruence-match the caller (`transplant` carries the id verbatim). Contexts
//! never run concurrently, so a plain `&mut` suffices (no interior mutability).
//!
//! Monomorphization is general: a non-generic ADT is the instance with empty
//! type-args; a generic ADT (user-written, or the builtin `Option`) gets one
//! instance per concrete type-argument tuple it is used at — discovered on use.

use std::collections::HashMap;

use crate::verify::analysis::ConstFold;
use crate::verify::lang::{FuncId, Symbolic};
use crate::verify::prelude::OPTION;
use crate::verify::rewrite::{proj_rule, tag_rule};
use crate::vmir::{Declaration, MemberId, Program, Type};

type Rule = egg::Rewrite<Symbolic, ConstFold>;

/// Lazily allocates and names the verifier ids for monomorphic ADT
/// constructors / projections / tags, and accumulates their reduction rules.
pub struct Allocator {
    /// Next func id to mint (starts past every real declaration id, so a minted
    /// id never collides with a plain function reusing its declaration index).
    next: usize,
    cons: HashMap<(MemberId, Vec<Type>, usize), FuncId>,
    proj: HashMap<(MemberId, Vec<Type>, usize, usize), FuncId>,
    tag: HashMap<(MemberId, Vec<Type>), FuncId>,
    /// Display names for minted ids (which are outside the interner).
    names: HashMap<FuncId, String>,
    rules: Vec<Rule>,
    /// Per ADT *head* (an `Adt` decl id, or a predicate's own Resource id for its
    /// snapshot ADT — see `Type::Snap`), its per-variant field counts — the shape
    /// needed to mint an instance.
    shapes: HashMap<MemberId, Vec<usize>>,
    /// Base display name per ADT head.
    head_names: HashMap<MemberId, String>,
    /// The builtin `Option` ADT id, if present.
    option_adt: Option<MemberId>,
}

impl Allocator {
    /// Build an allocator for `program`: records the shape of every ADT head
    /// (ADT declarations and predicate snapshots, keyed by the predicate's own
    /// Resource id) so instances can be minted on demand. Mints nothing yet.
    pub fn new(program: &Program) -> Self {
        let mut shapes = HashMap::new();
        let mut head_names = HashMap::new();
        for (id, decl) in program.decls.iter_enumerated() {
            if let Declaration::Adt(adt) = decl {
                shapes.insert(
                    id,
                    adt.variants.iter().map(|v| v.field_types.len()).collect(),
                );
                head_names.insert(id, program.interner.resolve(&id).to_string());
            }
        }
        for (id, decl) in program.decls.iter_enumerated() {
            if let Declaration::Resource(r) = decl
                && let Some(snap) = &r.snapshot
            {
                // A snapshot is a single-variant ADT over the footprint slots,
                // headed by the predicate's own id (`Type::Snap(id)`).
                shapes.insert(id, vec![snap.field_types.len()]);
                head_names.insert(id, format!("{}@snap", program.interner.resolve(&id)));
            }
        }
        Allocator {
            next: program.interner.len(),
            cons: HashMap::new(),
            proj: HashMap::new(),
            tag: HashMap::new(),
            names: HashMap::new(),
            rules: Vec::new(),
            shapes,
            head_names,
            option_adt: program.interner.get(OPTION),
        }
    }

    /// An empty allocator (no ADT heads). For tests / programs without ADTs.
    #[cfg(test)]
    pub fn empty() -> Self {
        Allocator {
            next: 0,
            cons: HashMap::new(),
            proj: HashMap::new(),
            tag: HashMap::new(),
            names: HashMap::new(),
            rules: Vec::new(),
            shapes: HashMap::new(),
            head_names: HashMap::new(),
            option_adt: None,
        }
    }

    /// Constructor id for variant `variant` of `adt[args]` (minting the instance
    /// on first use).
    pub fn cons(&mut self, adt: MemberId, args: &[Type], variant: usize) -> FuncId {
        self.ensure(adt, args);
        self.cons[&(adt, args.to_vec(), variant)]
    }

    /// Field-`field` projection id of variant `variant` of `adt[args]`.
    pub fn proj(&mut self, adt: MemberId, args: &[Type], variant: usize, field: usize) -> FuncId {
        self.ensure(adt, args);
        self.proj[&(adt, args.to_vec(), variant, field)]
    }

    /// Discriminator-tag id of `adt[args]`.
    pub fn tag(&mut self, adt: MemberId, args: &[Type]) -> FuncId {
        self.ensure(adt, args);
        self.tag[&(adt, args.to_vec())]
    }

    /// The builtin `Option` ADT's declaration id.
    pub fn option_adt(&self) -> MemberId {
        self.option_adt.expect("Option prelude not injected")
    }

    /// The reduction rules minted so far, to inject into a context's runner.
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    /// Display name for a minted id (`None` if `f` is not allocator-minted).
    pub fn name(&self, f: FuncId) -> Option<&str> {
        self.names.get(&f).map(String::as_str)
    }

    /// Mint the instance `adt[args]` (tag + all constructors + all projections +
    /// rules) if not already present.
    fn ensure(&mut self, adt: MemberId, args: &[Type]) {
        if self.tag.contains_key(&(adt, args.to_vec())) {
            return;
        }
        let counts = self
            .shapes
            .get(&adt)
            .unwrap_or_else(|| panic!("unknown ADT head {}", adt.0))
            .clone();
        let label = self.label(adt, args);

        let tag_id = self.mint(format!("{label}@tag"));
        self.tag.insert((adt, args.to_vec()), tag_id);

        let mut ctor_tags = HashMap::new();
        for (variant, &fields) in counts.iter().enumerate() {
            let cons_id = self.mint(format!("{label}#{variant}"));
            self.cons.insert((adt, args.to_vec(), variant), cons_id);
            ctor_tags.insert(cons_id, variant);
            for field in 0..fields {
                let proj_id = self.mint(format!("{label}#{variant}.{field}"));
                self.proj
                    .insert((adt, args.to_vec(), variant, field), proj_id);
                self.rules.push(proj_rule(proj_id, cons_id, field));
            }
        }
        self.rules.push(tag_rule(tag_id, ctor_tags));
    }

    fn mint(&mut self, name: String) -> FuncId {
        let id = FuncId(self.next);
        self.next += 1;
        self.names.insert(id, name);
        id
    }

    /// A readable label for `adt[args]`, e.g. `Option` or `Box[Int]`.
    fn label(&self, adt: MemberId, args: &[Type]) -> String {
        let head = self
            .head_names
            .get(&adt)
            .cloned()
            .unwrap_or_else(|| format!("d{}", adt.0));
        if args.is_empty() {
            head
        } else {
            let inner: Vec<String> = args.iter().map(|a| format!("{a}")).collect();
            format!("{head}[{}]", inner.join(", "))
        }
    }
}
