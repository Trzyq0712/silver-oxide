//! Verifier-side ADT id allocator.
//!
//! ADT operations (`PureInst::{AdtCons,AdtProj,AdtTag}` and predicate snapshots)
//! are interpreted as `Symbolic::FuncApp`s over **verifier-minted** function ids,
//! distinct from any VMIR declaration id — so no synthetic `@tag`/`@dtor`/
//! constructor declarations exist. Ids are allocated **lazily on first use** of a
//! **concept** `(adt-head)`; minting one mints its whole concept (tag + every
//! constructor + every projection) and appends its reduction rules.
//!
//! The e-graph is **polymorphic**, not monomorphized: a generic op gets **one** id
//! per concept, and its ground type arguments ride in the `FuncApp` operator
//! identity (the discriminant, `Symbolic::FuncApp(FuncId, Box<[Type]>, _)`), not as
//! children. Distinctness across instantiations (`Box[Int]` vs `Box[Bool]`) comes
//! from the differing discriminant — not from per-instance ids, and with no type
//! e-classes. The reductions are instantiation-agnostic (one per concept).
//!
//! The allocator is owned by `verify::verify` and threaded `&mut` through each
//! (sequential) verification unit, so a concept gets the **same** id wherever it
//! appears — required for a resource certificate's grafted nodes to
//! congruence-match the caller (`transplant` carries the id verbatim). Contexts
//! never run concurrently, so a plain `&mut` suffices (no interior mutability).

use std::collections::HashMap;

use crate::verify::analysis::ConstFold;
use crate::verify::lang::{FuncId, Symbolic};
use crate::verify::rewrite::{proj_rule, tag_rule};
use crate::vmir::{Declaration, MemberId, Program, Type};

type Rule = egg::Rewrite<Symbolic, ConstFold>;

/// Lazily allocates and names the verifier ids for polymorphic ADT
/// constructors / projections / tags, and accumulates their reduction rules.
pub struct Allocator {
    /// Next func id to mint (starts past every real declaration id, so a minted
    /// id never collides with a plain function reusing its declaration index).
    next: usize,
    /// Keyed by **concept**, not by type instantiation: one id per `(head,
    /// variant)` / `(head, variant, field)` / `head`. The e-graph is polymorphic —
    /// the ground type args ride in the `FuncApp` discriminant, so a single id
    /// serves every instantiation (distinctness comes from the differing
    /// discriminant, not from per-instance ids or type e-classes).
    cons: HashMap<(MemberId, usize), FuncId>,
    proj: HashMap<(MemberId, usize, usize), FuncId>,
    tag: HashMap<MemberId, FuncId>,
    /// Display names for minted ids (which are outside the interner).
    names: HashMap<FuncId, String>,
    rules: Vec<Rule>,
    /// Per ADT *head* (an `Adt` decl id, or a predicate's own Resource id for its
    /// snapshot ADT — see `Type::Snap`), its per-variant field counts — the shape
    /// needed to mint an instance.
    shapes: HashMap<MemberId, Vec<usize>>,
    /// Base display name per ADT head.
    head_names: HashMap<MemberId, String>,
    /// Per ADT head, the source constructor name of each variant (`None` for a
    /// synthetic variant — e.g. a snapshot's sole constructor). Drives minted-id
    /// names: `Adt::Ctor` when named, `Adt#i` when anonymous.
    variant_names: HashMap<MemberId, Vec<Option<String>>>,
    /// The builtin `Option` ADT id, if present.
    option_adt: Option<MemberId>,
    /// Verifier cost metrics, accumulated across every unit of the run (the
    /// allocator is the per-run shared state threaded into each `VerifyContext`).
    pub(crate) stats: crate::verify::VerifyStats,
}

impl Allocator {
    /// Build an allocator for `program`: records the shape of every ADT head
    /// (ADT declarations and predicate snapshots, keyed by the predicate's own
    /// Resource id) so instances can be minted on demand. Mints nothing yet.
    pub fn new(program: &Program) -> Self {
        let mut shapes = HashMap::new();
        let mut head_names = HashMap::new();
        let mut variant_names: HashMap<MemberId, Vec<Option<String>>> = HashMap::new();
        let vname = |adt: &crate::vmir::Adt| -> Vec<Option<String>> {
            adt.variants
                .iter()
                .map(|v| v.name.map(|n| program.interner.resolve(&n).to_string()))
                .collect()
        };

        // The builtin `Option` ADT (`vmir::Type::Option`): `Some(T)` (variant 0,
        // one field) and `None` (variant 1, no fields). It is not a program
        // declaration, so it gets a synthetic head id one past the last decl; its
        // values are typed `Type::Option`, never `Type::Domain(option_head, …)`,
        // so the head id is only ever a mono key (never resolved via the interner).
        let option_head = MemberId(program.decls.len());
        shapes.insert(option_head, vec![1, 0]);
        head_names.insert(option_head, "Option".to_string());
        variant_names.insert(
            option_head,
            vec![Some("Some".to_string()), Some("None".to_string())],
        );

        for (id, decl) in program.decls.iter_enumerated() {
            if let Declaration::Adt(adt) = decl {
                shapes.insert(
                    id,
                    adt.variants.iter().map(|v| v.field_types.len()).collect(),
                );
                head_names.insert(id, program.name(id).to_string());
                variant_names.insert(id, vname(adt));
            }
        }
        for (id, decl) in program.decls.iter_enumerated() {
            if let Declaration::Resource(r) = decl
                && let Some(crate::vmir::Snapshot::Concrete(adt)) = r.derive_snapshot()
            {
                // A concrete predicate's snapshot is a single-variant ADT over
                // the footprint slots, headed by the predicate's own id
                // (`Type::Snap(id)`). Derived from the body — only the variant
                // field counts are needed here. (An abstract predicate derives an
                // opaque Domain, which has no constructor to register.)
                shapes.insert(
                    id,
                    adt.variants.iter().map(|v| v.field_types.len()).collect(),
                );
                head_names.insert(id, format!("{}@snap", program.name(id)));
                variant_names.insert(id, vname(&adt));
            }
        }
        Allocator {
            // Mint func ids past the synthetic `Option` head, so neither a plain
            // function (which reuses its decl index) nor the head id collides.
            next: program.decls.len() + 1,
            cons: HashMap::new(),
            proj: HashMap::new(),
            tag: HashMap::new(),
            names: HashMap::new(),
            rules: Vec::new(),
            shapes,
            head_names,
            variant_names,
            option_adt: Some(option_head),
            stats: Default::default(),
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
            variant_names: HashMap::new(),
            option_adt: None,
            stats: Default::default(),
        }
    }

    /// Consume the allocator, returning the accumulated verifier cost metrics.
    pub(crate) fn into_stats(self) -> crate::verify::VerifyStats {
        self.stats
    }

    /// Constructor id for variant `variant` of `adt` (minting the concept on first
    /// use). Polymorphic — one id for every instantiation; the ground type args
    /// ride in the `FuncApp` discriminant, never key the id.
    pub fn cons(&mut self, adt: MemberId, variant: usize) -> FuncId {
        self.ensure(adt);
        self.cons[&(adt, variant)]
    }

    /// Field-`field` projection id of variant `variant` of `adt`.
    pub fn proj(&mut self, adt: MemberId, variant: usize, field: usize) -> FuncId {
        self.ensure(adt);
        self.proj[&(adt, variant, field)]
    }

    /// Discriminator-tag id of `adt`.
    pub fn tag(&mut self, adt: MemberId) -> FuncId {
        self.ensure(adt);
        self.tag[&adt]
    }

    /// The builtin `Option` ADT's (synthetic) head id.
    pub fn option_adt(&self) -> MemberId {
        self.option_adt.expect("builtin Option head not registered")
    }

    // ---- Builtin `Option` resolution -------------------------------------
    // `Option[T]` is a builtin parametric type (`vmir::Type::Option`). These are
    // the dedicated way to request its monomorphic instance, rather than open-
    // coding `cons`/`proj` against `option_adt()`. (Future `Seq`/`Set` follow the
    // same shape.)

    /// `Option[elem]` as a vmir type (the builtin parametric `Type::Option`).
    pub fn option_type(&self, elem: Type) -> Type {
        Type::Option(Box::new(elem))
    }

    /// Constructor id of `Some` (variant 0) of `Option`.
    pub fn option_some(&mut self) -> FuncId {
        let opt = self.option_adt();
        self.cons(opt, 0)
    }

    /// Constructor id of `None` (variant 1) of `Option`.
    pub fn option_none(&mut self) -> FuncId {
        let opt = self.option_adt();
        self.cons(opt, 1)
    }

    /// Projection id recovering the `Some` payload of `Option`.
    pub fn option_value(&mut self) -> FuncId {
        let opt = self.option_adt();
        self.proj(opt, 0, 0)
    }

    /// The reduction rules minted so far, to inject into a context's runner.
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    /// Display name for a minted id (`None` if `f` is not allocator-minted).
    pub fn name(&self, f: FuncId) -> Option<&str> {
        self.names.get(&f).map(String::as_str)
    }

    /// Mint the **concept** `adt` (tag + all constructors + all projections +
    /// reduction rules) if not already present. One concept covers every
    /// instantiation; the ground type args live in the `FuncApp` discriminant, so
    /// the reductions are instantiation-agnostic.
    fn ensure(&mut self, adt: MemberId) {
        if self.tag.contains_key(&adt) {
            return;
        }
        let counts = self
            .shapes
            .get(&adt)
            .unwrap_or_else(|| panic!("unknown ADT head {}", adt.0))
            .clone();
        let label = self.label(adt);

        let tag_id = self.mint(format!("{label}@tag"));
        self.tag.insert(adt, tag_id);

        let mut ctor_tags = HashMap::new();
        for (variant, &fields) in counts.iter().enumerate() {
            // `Adt::Ctor` for a named constructor, `Adt::#i` for an anonymous one.
            let cons_label = match self.variant_name(adt, variant) {
                Some(name) => format!("{label}::{name}"),
                None => format!("{label}::#{variant}"),
            };
            let cons_id = self.mint(cons_label.clone());
            self.cons.insert((adt, variant), cons_id);
            ctor_tags.insert(cons_id, variant);
            for field in 0..fields {
                let proj_id = self.mint(format!("{cons_label}.{field}"));
                self.proj.insert((adt, variant, field), proj_id);
                self.rules.push(proj_rule(proj_id, cons_id, field));
            }
        }
        self.rules.push(tag_rule(tag_id, ctor_tags));
    }

    /// The source constructor name of `adt`'s `variant`, if any.
    fn variant_name(&self, adt: MemberId, variant: usize) -> Option<&str> {
        self.variant_names
            .get(&adt)
            .and_then(|v| v.get(variant))
            .and_then(|n| n.as_deref())
    }

    fn mint(&mut self, name: String) -> FuncId {
        let id = FuncId(self.next);
        self.next += 1;
        self.names.insert(id, name);
        id
    }

    /// A readable label for the head `adt`, e.g. `Option` or `Box`. One id now
    /// serves every instantiation, so the label carries no type arguments.
    fn label(&self, adt: MemberId) -> String {
        self.head_names
            .get(&adt)
            .cloned()
            .unwrap_or_else(|| format!("d{}", adt.0))
    }
}
