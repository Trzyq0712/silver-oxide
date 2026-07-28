use std::collections::HashMap;

use crate::{
    verify::{
        analysis::ConstFold,
        cert::FunctionDefinition,
        func_registry::FuncRegistry,
        lang::{FuncId, Symbolic},
        rewrite,
    },
    vmir::{BinOp, Declaration, Literal, MemberId, Polarity, Type},
};
use lasso::{Rodeo, Spur};
use typed_index_collections::TiVec;

pub(crate) struct VerifyContext<'a> {
    pub(crate) egraph: egg::EGraph<Symbolic, ConstFold>,
    /// Static structural rules. The ADT cons/proj/tag reductions are pulled from
    /// the [`FuncRegistry`] at saturation time (it grows as ADT concepts are
    /// minted).
    static_rules: Vec<egg::Rewrite<Symbolic, ConstFold>>,
    /// Terminating structural reductions, run after heap-producing ops to
    /// normalize (collapse snapshot towers) without a full saturation.
    static_reduce: Vec<egg::Rewrite<Symbolic, ConstFold>>,
    /// Per-unit lazy rules, minted by `assume_axioms`: the single quantifier
    /// instantiation rule (`rewrite::forall_rule` — quantifiers are e-nodes;
    /// ground axioms are pre-added to the graph instead) and one unfold rule
    /// per verified function body (one per `fn_certs` entry — see
    /// `rewrite::function_rule`).
    /// Chained into full saturation (incl. the tier-3 probe) but not `reduce`.
    pub(crate) axiom_rules: Vec<egg::Rewrite<Symbolic, ConstFold>>,
    /// Monotonic source of fresh-value ids (`Symbolic::Fresh(n)`). A plain counter
    /// now that nothing mints fresh values at saturation time — both certificate
    /// kinds are add-only recipes, so `transplant` (which threaded a shared
    /// counter) is gone.
    fresh_counter: u32,
    /// Cheap string repr for member/constructor names.
    pub(crate) interner: &'a Rodeo,
    /// Member names indexed by `MemberId` (for `member_name`/`func_name`).
    pub(crate) decls: &'a TiVec<MemberId, Declaration>,
    /// Location group tags (`Type::Addr.group`), for display resolution.
    pub(crate) groups: &'a Rodeo<Spur>,
    /// Shared verifier function-id registry (ADT cons/proj/tag ids + rules and
    /// builtin operators).
    /// Owned by `verify::verify`, threaded `&mut` through each unit so ids stay
    /// consistent across certificate grafts.
    pub(crate) alloc: &'a mut FuncRegistry,
    /// Type side-oracle: the irreducible type sources that the type-free
    /// e-graph nodes no longer carry. Keyed by stable node payloads (the
    /// `Fresh` counter and the `FuncApp` member id), so no union upkeep is
    /// needed — the visualization reads them directly to reconstruct types.
    pub(crate) fresh_types: HashMap<u32, Type>,
    pub(crate) func_ret_types: HashMap<FuncId, Type>,
    /// Verified non-recursive function bodies, keyed by `MemberId`. `assume_axioms`
    /// reads this to install one lazy unfold rule per entry into `axiom_rules`
    /// (see `rewrite::function_rule`). `None` in isolated contexts (unit tests)
    /// that never evaluate a `FunctionCall`.
    pub(crate) fn_certs: Option<&'a HashMap<MemberId, std::sync::Arc<FunctionDefinition>>>,
    /// The certificate recipe under construction, mirrored step-by-step by the
    /// eval walk of a **function or resource** body (single walk — see
    /// `cert::RecipeBuilder`). `None` for methods — they produce no
    /// certificate, so the recipe machinery costs them nothing.
    pub(crate) recipe: Option<crate::verify::cert::RecipeBuilder>,
    /// Fixpoint cache: the rule tier the live e-graph is known saturated under,
    /// with the rule-set sizes that saturation saw (ADT rules and axiom rules
    /// grow mid-unit; a grown set invalidates the fixpoint). `None` when any
    /// node/union landed since. Lets `saturate`/`reduce` skip whole runner
    /// invocations — most are re-runs on an unchanged graph.
    clean: Option<(CleanLevel, usize, usize)>,
    /// Whether the program uses `wildcard` permissions anywhere (any heap-op
    /// `Perm` with a wildcard leaf, in any body). Computed once from `decls`; a
    /// program without wildcards skips the per-subtract `contains_wildcard` scan
    /// entirely, so non-wildcard verification pays nothing for the feature.
    pub(crate) has_wildcard: bool,
    /// `SILVER_OXIDE_OOB_MEMO`: keep proven **conditional** obligations in an
    /// out-of-band set instead of unioning `pc ⇒ goal` into the `true` e-class.
    /// The union memoized the proof but dragged the whole `ite(pc.., goal, true)`
    /// chain permanently into `true` (the measured #1 growth driver — the graph
    /// has no GC). The set memoizes the *verdict* without materializing the
    /// scaffolding. Empty-pc goals still union (that path is productive:
    /// `eq-true-union`/congruence off a proven `Eq`).
    oob_memo: bool,
    /// Canonical class ids of implications already proven `true`, consulted at
    /// tier 1 when `oob_memo` is on. Keyed by `egraph.find(imp)`: two distinct
    /// obligations only share a class via congruence — which means their goals
    /// and pcs are pairwise equal, i.e. the *same* obligation — so a hit is
    /// sound; a stale leader after an unrelated merge only causes a safe
    /// re-prove.
    proven_imps: std::collections::HashSet<egg::Id>,
    /// The current method block's control cube (the shared pc of all its insts),
    /// as live-graph literal ids. Set by [`Self::begin_block`]; the scratch
    /// assumes it. Empty outside a method block (functions/resources don't use
    /// the scratch).
    current_cube: Vec<(egg::Id, Polarity)>,
    /// Whether we are inside a method block walk — gates the scratch on
    /// (functions/resources keep the per-obligation clone path).
    in_block: bool,
    /// The live per-block scratch, built lazily on the block's first tier-3
    /// obligation and discarded at block exit. `None` when no obligation has
    /// needed it yet (or outside a method block).
    scratch: Option<BlockScratch>,
}

/// A parallel "scratch" e-graph for one method block: a clone of ground taken at
/// build time with the block cube assumed, kept in sync with ground through the
/// [`VerifyContext::add`]/[`VerifyContext::union`] hooks. It saturates under the
/// full rule set (independently of ground), so it can discharge every obligation
/// in the block without re-cloning ground per obligation.
///
/// Id-space handling: ids present at build time are identical in both graphs
/// (clone preserves them), so a ground id below `watermark` translates to itself.
/// Ids minted after the build are mirrored through the `add`/`union` hooks into
/// `map`. A ground id at-or-above `watermark` that is *not* in the map is a
/// rule-derived operand the scratch never received (e.g. a `find`-canonical
/// leader produced by a ground `reduce`/`saturate`): [`VerifyContext::tr`]
/// imports it on demand (extract a ground representative, re-add into the
/// scratch), so the scratch is a valid clone base under any ground state.
struct BlockScratch {
    egraph: egg::EGraph<Symbolic, ConstFold>,
    /// ground id → scratch id, for mints recorded since the clone.
    map: HashMap<egg::Id, egg::Id>,
    /// Ground e-node count (`total_size`) at build time — the id-space boundary:
    /// a ground id `< watermark` existed in the clone (identity-valid in the
    /// scratch). `total_size` only ever under-counts after a rebuild, which is
    /// safe here (a pre-build id then just gets re-imported, a no-op via
    /// hash-consing).
    watermark: usize,
    /// The `true` literal's ground id at build time — identity-valid in the
    /// scratch. Canonicalize with `find` before comparing (saturation merges it
    /// into a larger class).
    true_id: egg::Id,
    /// Set on every mirrored `add`/`union` and every import; cleared by a
    /// saturation. Avoids re-saturating an unchanged scratch across consecutive
    /// obligations.
    dirty: bool,
}

impl BlockScratch {
    /// Fast translate: `Some(scratch id)` for a mapped or pre-build id; `None`
    /// when a post-build ground id is unmapped and so must be imported by
    /// [`VerifyContext::tr`].
    fn fast_translate(&self, g: egg::Id) -> Option<egg::Id> {
        if let Some(&s) = self.map.get(&g) {
            Some(s)
        } else if usize::from(g) < self.watermark {
            Some(g)
        } else {
            None
        }
    }
}

/// Whether any declaration uses a `wildcard` permission (a heap-op `Perm` with
/// a wildcard leaf). Scanned once per unit at [`VerifyContext::new`]; lets a
/// wildcard-free program skip the per-subtract `contains_wildcard` walk.
fn decls_have_wildcard(decls: &TiVec<MemberId, Declaration>) -> bool {
    use crate::vmir::{HeapInst, Inst, InstKind};
    fn insts_wild(insts: &[Inst]) -> bool {
        insts.iter().any(|i| match &i.kind {
            InstKind::Heap(
                HeapInst::Combine { perm, .. }
                | HeapInst::Inhale { perm, .. }
                | HeapInst::Exhale { perm, .. }
                | HeapInst::Fold { perm, .. }
                | HeapInst::Unfold { perm, .. },
            ) => perm.has_wildcard(),
            _ => false,
        })
    }
    decls.iter().any(|d| match d {
        Declaration::Method(m) => insts_wild(&m.flatten()),
        Declaration::Function(f) => f.body.as_ref().is_some_and(|b| insts_wild(&b.insts)),
        Declaration::Resource(r) => r.body.as_ref().is_some_and(|b| insts_wild(&b.insts)),
        _ => false,
    })
}

/// How much of the rule set the live e-graph is saturated under. `Reduce`'s
/// set (terminating reductions + ADT) is a subset of `Full`'s, so `Full`
/// satisfies a `reduce()` request but not vice versa.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum CleanLevel {
    Reduce,
    Full,
}

impl<'a> VerifyContext<'a> {
    pub(crate) fn new(
        interner: &'a Rodeo,
        decls: &'a TiVec<MemberId, Declaration>,
        groups: &'a Rodeo<Spur>,
        alloc: &'a mut FuncRegistry,
    ) -> Self {
        Self {
            egraph: {
                // Fresh graph, fresh id space: remembered instantiations from
                // the previous unit are meaningless.
                rewrite::new_memo_unit();
                egg::EGraph::new(ConstFold::new(alloc.ctor_table()))
            },
            static_rules: rewrite::rules(),
            static_reduce: rewrite::reduce_rules(),
            axiom_rules: Vec::new(),
            fresh_counter: 0,
            interner,
            decls,
            groups,
            alloc,
            fresh_types: HashMap::new(),
            func_ret_types: HashMap::new(),
            fn_certs: None,
            recipe: None,
            clean: None,
            has_wildcard: decls_have_wildcard(decls),
            oob_memo: std::env::var_os("SILVER_OXIDE_OOB_MEMO").is_some(),
            proven_imps: std::collections::HashSet::new(),
            current_cube: Vec::new(),
            in_block: false,
            scratch: None,
        }
    }

    /// The fixpoint-cache tag for the current rule sets (their sizes — growth
    /// invalidates a recorded fixpoint).
    fn clean_tag(&self, level: CleanLevel) -> (CleanLevel, usize, usize) {
        (level, self.alloc.rules().len(), self.axiom_rules.len())
    }

    /// Whether the live graph is known saturated at `level` (or stronger) under
    /// the *current* rule sets.
    fn is_clean(&self, level: CleanLevel) -> bool {
        matches!(self.clean, Some((l, adt, ax))
            if l >= level && adt == self.alloc.rules().len() && ax == self.axiom_rules.len())
    }

    /// Union two e-classes in the live graph — the sanctioned mutation path
    /// (invalidates the fixpoint cache). Callers still `rebuild()` after a
    /// batch of unions.
    pub(crate) fn union(&mut self, a: egg::Id, b: egg::Id) -> bool {
        let merged = self.egraph.union(a, b);
        if merged {
            self.clean = None;
        }
        if self.scratch.is_some() {
            // Mirror into the block scratch. A same-typed conflict there (the
            // cube made this union contradictory) folds to `Inconsistent`, not a
            // panic — that just makes the block's goals vacuously provable.
            let (ta, tb) = (self.tr(a), self.tr(b));
            let sc = self.scratch.as_mut().unwrap();
            sc.egraph.union(ta, tb);
            sc.dirty = true;
        }
        merged
    }

    /// Translate a **ground** id into the current block scratch's id space.
    /// Identity outside a scratch. Fast path (a mapped or pre-build id) is O(1);
    /// otherwise the ground term at `g` is imported into the scratch (extract a
    /// representative e-node, translate its children, re-add), so the scratch is
    /// a valid clone base even when a lazy/structural ground has surfaced
    /// rule-derived ids as operands.
    fn tr(&mut self, g: egg::Id) -> egg::Id {
        let g = self.egraph.find(g);
        match self.scratch.as_ref() {
            None => return g,
            Some(sc) => {
                if let Some(s) = sc.fast_translate(g) {
                    return s;
                }
            }
        }
        use egg::Language as _;
        let node = self.egraph[g].nodes[0].clone();
        let kids: Vec<egg::Id> = node.children().to_vec();
        let tkids: Vec<egg::Id> = kids.iter().map(|c| self.tr(*c)).collect();
        let mut snode = node;
        for (slot, tk) in snode.children_mut().iter_mut().zip(tkids) {
            *slot = tk;
        }
        let sc = self.scratch.as_mut().unwrap();
        let s = sc.egraph.add(snode);
        sc.map.insert(g, s);
        sc.dirty = true;
        s
    }

    /// Mirror a ground `add` of `node` (which produced ground id `ground_id`)
    /// into the block scratch, translating its children through [`Self::tr`].
    /// Idempotent per ground class.
    fn mirror_add(&mut self, ground_id: egg::Id, node: Symbolic) {
        let key = self.egraph.find(ground_id);
        if self.scratch.as_ref().unwrap().map.contains_key(&key) {
            self.scratch.as_mut().unwrap().dirty = true;
            return;
        }
        use egg::Language as _;
        let kids: Vec<egg::Id> = node.children().to_vec();
        let tkids: Vec<egg::Id> = kids.iter().map(|c| self.tr(*c)).collect();
        let mut snode = node;
        for (slot, tk) in snode.children_mut().iter_mut().zip(tkids) {
            *slot = tk;
        }
        let sc = self.scratch.as_mut().unwrap();
        let s = sc.egraph.add(snode);
        sc.map.insert(key, s);
        sc.dirty = true;
    }

    /// Whether the e-graph has reached a contradiction (some e-class merged
    /// conflicting same-typed literals). Once inconsistent, every goal is
    /// vacuously provable — used by [`Self::prove_under_pc`] as the implicit
    /// channel through which an over-permissioned field location proves `false`.
    pub(crate) fn is_inconsistent(&self) -> bool {
        self.egraph.classes().any(|c| c.data.is_inconsistent())
    }

    /// Display name for a member id. Registry-minted ids (outside the interner)
    /// resolve via the registry's name table.
    pub(crate) fn member_name(&self, m: MemberId) -> String {
        if usize::from(m) < self.decls.len() {
            self.interner.resolve(&self.decls[m].name()).to_string()
        } else {
            format!("d{}", m.0)
        }
    }

    /// Display name for an e-graph function id: a real declaration index resolves
    /// via the interner; an allocator-minted id via its name table.
    pub(crate) fn func_name(&self, f: FuncId) -> String {
        if f.0 < self.decls.len() {
            self.interner
                .resolve(&self.decls[MemberId::from(f.0)].name())
                .to_string()
        } else {
            self.alloc
                .name(f)
                .map(str::to_string)
                .unwrap_or_else(|| format!("f{}", f.0))
        }
    }

    /// Render a VMIR type using [`Self::member_name`] for `Domain` heads, so
    /// verifier-synthesised types (e.g. `Option[Int]`) print without panicking
    /// on the interner.
    pub(crate) fn type_name(&self, ty: &Type) -> String {
        match ty {
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Real => "Real".to_string(),
            Type::Ref => "Ref".to_string(),
            Type::Addr {
                group,
                value,
                bound,
            } => format!(
                "&[{}] {} @ {bound}",
                self.groups.resolve(group),
                self.type_name(value)
            ),
            Type::Domain(id, args) => {
                let head = self.member_name(*id);
                if args.is_empty() {
                    head
                } else {
                    let inner: Vec<String> = args.iter().map(|a| self.type_name(a)).collect();
                    format!("{head}<{}>", inner.join(", "))
                }
            }
            Type::Snap(id) => format!("{}@snap", self.member_name(*id)),
            Type::Option(t) => format!("Option<{}>", self.type_name(t)),
            Type::Generic(i) => format!("?{i}"),
        }
    }

    /// Build a snapshot member `present ? Some(value) : None` over `Option[elem]`.
    /// When `present` const-folds to `true` (statically-positive permission) the
    /// `ite`/projection reductions peel it back to `value`.
    pub(crate) fn option_member(
        &mut self,
        elem: Type,
        present: egg::Id,
        value: egg::Id,
    ) -> egg::Id {
        // `Option` is a builtin parametric type; one polymorphic id each for
        // `Some`/`None` (variants 0/1). The element type is the application's ground
        // type instantiation (carried in the operator identity, not a child).
        let some_id = self.alloc.option_some();
        let none_id = self.alloc.option_none();
        let opt_ty = self.alloc.option_type(elem.clone());
        let tys: Box<[Type]> = Box::new([elem]);
        let some = self.add_func_app_id(some_id, tys.clone(), opt_ty.clone(), Box::new([value]));
        let none = self.add_func_app_id(none_id, tys, opt_ty, Box::new([]));
        self.add(Symbolic::Ite([present, some, none]))
    }

    /// Unwrap a snapshot member: `value(opt)`, the `Some` field accessor. With
    /// `opt = Some(v)` this reduces to `v`; on an opaque member it stays
    /// uninterpreted (correct — the value was never present).
    pub(crate) fn option_unwrap(&mut self, elem: Type, opt: egg::Id) -> egg::Id {
        let value_id = self.alloc.option_value();
        let tys: Box<[Type]> = Box::new([elem.clone()]);
        self.add_func_app_id(value_id, tys, elem, Box::new([opt]))
    }

    /// The boolean `0 < perm` (a permission is positive). Lifts a permission
    /// amount to the snapshot's membership discriminant.
    pub(crate) fn perm_positive(&mut self, perm: egg::Id) -> egg::Id {
        let zero = self.add(Symbolic::Lit(Literal::Real(num::BigRational::from(
            num::BigInt::from(0),
        ))));
        self.add(Symbolic::Binary(BinOp::LtR, [zero, perm]))
    }

    /// Run rewrite saturation over the e-graph in place. The rule set is the
    /// static rules plus the ADT reductions minted so far by the allocator
    /// plus the per-unit axiom/function rules.
    pub(crate) fn saturate(&mut self) {
        if self.is_clean(CleanLevel::Full) {
            return;
        }
        let egraph = std::mem::take(&mut self.egraph);
        self.egraph = self.saturate_flat(egraph);
        self.alloc.stats.saturations += 1;
        self.clean = Some(self.clean_tag(CleanLevel::Full));
    }

    /// One full-rule-set run, shared by [`Self::saturate`], [`Self::run_probe`],
    /// and the block scratch. Memo scoping is ambient (see `rewrite::Memo`): live
    /// runs write the persistent base, scratch scopes an overlay.
    fn saturate_flat(
        &mut self,
        egraph: egg::EGraph<Symbolic, ConstFold>,
    ) -> egg::EGraph<Symbolic, ConstFold> {
        let (egraph, iterations) = run_rules(
            egraph,
            self.static_rules
                .iter()
                .chain(self.alloc.rules())
                .chain(self.axiom_rules.iter()),
            None,
        );
        self.alloc.stats.record_run(&iterations);
        egraph
    }

    /// Run only the terminating structural reductions in place. Used after
    /// `fold`/`unfold` to collapse snapshot towers (so repeated round-trips
    /// don't grow the e-graph) without the cost/divergence risk of full
    /// saturation.
    pub(crate) fn reduce(&mut self) {
        if self.is_clean(CleanLevel::Reduce) {
            return;
        }
        let egraph = std::mem::take(&mut self.egraph);
        let (egraph, iterations) = run_rules(
            egraph,
            self.static_reduce.iter().chain(self.alloc.rules()),
            None,
        );
        self.egraph = egraph;
        self.alloc.stats.reduces += 1;
        self.alloc.stats.record_run(&iterations);
        self.clean = Some(self.clean_tag(CleanLevel::Reduce));
    }

    pub(crate) fn add(&mut self, node: Symbolic) -> egg::Id {
        let before = self.egraph.total_size();
        // Keep `node` for the scratch mirror only when a scratch is live (the
        // clone is not free — most adds happen with no scratch and pay nothing).
        if self.scratch.is_some() {
            let id = self.egraph.add(node.clone());
            if self.egraph.total_size() != before {
                self.clean = None;
            }
            self.mirror_add(id, node);
            id
        } else {
            let id = self.egraph.add(node);
            if self.egraph.total_size() != before {
                self.clean = None;
            }
            id
        }
    }

    /// The `true` boolean-literal e-class.
    pub(crate) fn true_(&mut self) -> egg::Id {
        self.add(Symbolic::Lit(Literal::Bool(true)))
    }

    /// The `false` boolean-literal e-class.
    pub(crate) fn false_(&mut self) -> egg::Id {
        self.add(Symbolic::Lit(Literal::Bool(false)))
    }

    /// Add a `FuncApp` over an already-allocated [`FuncId`] (a plain function,
    /// or an ADT constructor/projection/tag id from the allocator). Also used by
    /// grafting, which carries the id verbatim. `type_args` is the ground type
    /// instantiation — part of the node's operator identity (discriminant), not a
    /// child.
    pub(crate) fn add_func_app_id(
        &mut self,
        id: FuncId,
        type_args: Box<[Type]>,
        ret_ty: Type,
        args: Box<[egg::Id]>,
    ) -> egg::Id {
        self.func_ret_types.entry(id).or_insert(ret_ty);
        self.add(Symbolic::FuncApp(id, type_args, args))
    }

    pub(crate) fn fresh_symbolic_value(&mut self, ty: Type) -> egg::Id {
        let id = self.fresh_counter;
        self.fresh_counter += 1;
        self.fresh_types.insert(id, ty);
        self.add(Symbolic::Fresh(id))
    }

    /// Mint a fresh `wildcard` permission: a [`Symbolic::Wildcard`] (a symbolic
    /// `Real`) assumed strictly positive (`0 < w`). Viper's `wildcard` — an
    /// unspecified positive share. Its upper bound (`w ≤ 1` for a field via the
    /// location axiom, `w < held` at exhale) is imposed elsewhere. The distinct
    /// node lets an exhale recognise a wildcard-bearing permission (see
    /// `heap_subtract`).
    pub(crate) fn fresh_wildcard(&mut self) -> egg::Id {
        let w = self.add(Symbolic::Wildcard(crate::verify::lang::fresh_wildcard_id()));
        let pos = self.perm_positive(w);
        let true_ = self.true_();
        self.union(pos, true_);
        // No eager `rebuild()`: the wildcard is minted mid-heap-op and every heap
        // op rebuilds downstream (obligation proving / `assume_location_axioms`)
        // before `0 < w` is queried. Rebuilding per mint dominated the cost.
        w
    }

    /// Build `antecedents ==> consequent` as a right-associative chain of `Ite`
    /// muxers with fallback `true` (vacuous truth). No boolean AND tree.
    /// `antecedents` must be in innermost-first fold order. A positive literal
    /// puts the running term in the true-branch (`true` in the false-branch); a
    /// negative literal swaps the branches.
    pub(crate) fn implication(
        &mut self,
        consequent: egg::Id,
        antecedents: impl Iterator<Item = (egg::Id, Polarity)>,
    ) -> egg::Id {
        let true_ = self.true_();
        let mut imp = consequent;
        for (id, pol) in antecedents {
            imp = match pol {
                Polarity::Positive => self.add(Symbolic::Ite([id, imp, true_])),
                Polarity::Negative => self.add(Symbolic::Ite([id, true_, imp])),
            };
        }
        imp
    }

    /// Assume `fact` holds under `guards` — the **only** sanctioned way to record
    /// an assumption in the live e-graph. Merges `guards ==> fact` with `true`
    /// (via [`Self::implication`]), never `fact` itself: a raw `union(fact,
    /// true)` would assert `fact` on *every* path, including those where its
    /// guards do not hold, letting the verifier assume what it must prove (a
    /// resource inhaled only inside an `if` arm, an `assume` under a branch, a
    /// predicate `unfold`ed conditionally). With empty `guards` this degenerates
    /// to an unconditional assumption, which is correct only when the fact truly
    /// holds on all paths (e.g. a domain axiom).
    ///
    /// `guards` are in innermost-first fold order, matching [`Self::implication`].
    pub(crate) fn assume_guarded(
        &mut self,
        fact: egg::Id,
        guards: impl Iterator<Item = (egg::Id, Polarity)>,
    ) {
        let imp = self.implication(fact, guards);
        let true_ = self.true_();
        self.union(imp, true_);
        self.egraph.rebuild();
    }

    /// [`Self::assume_guarded`] for several facts sharing one `guards`, with a
    /// single `rebuild()` at the end (rebuild dominates, so batching matters when
    /// a heap op assumes more than one fact — e.g. a wildcard exhale's
    /// `needed < held` and `0 < held − needed`).
    pub(crate) fn assume_all_guarded(
        &mut self,
        facts: impl IntoIterator<Item = egg::Id>,
        guards: &[(egg::Id, Polarity)],
    ) {
        let true_ = self.true_();
        for fact in facts {
            let imp = self.implication(fact, guards.iter().copied());
            self.union(imp, true_);
        }
        self.egraph.rebuild();
    }

    /// Prove `goal == true` under the hypotheses `pc_lits`, using a throwaway
    /// clone of the e-graph so the assumptions never touch live state. On
    /// success, commit the proven implication `pc ==> goal` into the live graph
    /// (so it can fire later once the PC is established) and return `true`.
    ///
    /// A PC literal whose value already folds to the opposite boolean means the
    /// path is unsatisfiable: the goal then holds vacuously, so we short-circuit
    /// to `true` (and still commit the vacuously-true implication). This also
    /// avoids `ConstFold`'s conflicting-value panic when unioning into the
    /// `true`/`false` eclass.
    /// Prove `pc ⇒ goal` against the live e-graph, escalating through three
    /// tiers (cheapest first) and **memoizing** the result:
    /// 1. is the implication already known `true`? (O(1) — a prior identical
    ///    obligation merged it, or it's trivial);
    /// 2. else saturate the live graph (only **unconditional** facts live there)
    ///    and re-check — proves any unconditionally-true goal, no clone;
    /// 3. else clone, assume the path condition, saturate the clone, and check
    ///    `goal == true` — the only tier that clones, for genuinely
    ///    path-conditional goals.
    ///
    /// On success the implication is merged with `true` in the live graph so the
    /// next identical obligation hits tier 1. (Tiers 1/2 already have it merged.)
    pub(crate) fn prove_under_pc(
        &mut self,
        goal: egg::Id,
        pc_lits: &[(egg::Id, Polarity)],
    ) -> bool {
        self.alloc.stats.prove_calls += 1;
        let imp = self.implication(goal, pc_lits.iter().rev().copied());
        let true_ = self.true_();

        // Tier 1: already true (memoized / trivial). O(1) — checked before the
        // O(classes) inconsistency scan, which most calls never need. Under
        // `oob_memo` a proven *conditional* obligation lives in `proven_imps`
        // rather than the `true` class, so consult it too.
        if self.egraph.find(imp) == self.egraph.find(true_)
            || (self.oob_memo && self.proven_imps.contains(&self.egraph.find(imp)))
        {
            return true;
        }
        // Tier 0: the held facts are contradictory (e.g. a field location holds
        // > 1/1 permission) — every goal is vacuously provable.
        if self.is_inconsistent() {
            return true;
        }
        // Tier 2: saturate the live graph and re-check (no clone). Saturation can
        // also expose a contradiction, so re-check inconsistency too.
        self.saturate();
        if self.is_inconsistent() || self.egraph.find(imp) == self.egraph.find(true_) {
            return true;
        }

        // Inside a method block, discharge tier-3 against the per-block scratch
        // graph (reused across the block's obligations) instead of cloning ground
        // per obligation. The scratch is the strictly better clone base: warm,
        // cube-assumed, and kept in sync with ground. Its `tr` translation imports
        // any ground operand it is missing (`find` can surface rule-derived leader
        // ids the mirror never received), so it is always a valid clone base.
        //
        // Functions/resources have no CFG — a whole-body scratch would just equal
        // ground — so they keep the per-obligation clone path below, load-bearing
        // there for function-precondition, division side-condition, and
        // `acc`-non-negativity obligations.
        if self.in_block {
            let proven = self.prove_via_scratch(goal, pc_lits);
            if proven {
                self.record_proven(imp, true_, pc_lits.is_empty());
            }
            return proven;
        }

        // Tier 3 shortcut: if every PC literal already carries its required
        // polarity in the just-saturated live graph, assuming the PC adds
        // nothing — the probe would re-saturate an identical graph and reach
        // the tier-2 verdict again. Skip straight to tier 3.5 / the function
        // case split (an empty-pc goal — a branching function's exit post —
        // is exactly the shape that reaches here).
        //
        // Only functions/resources reach here (method obligations returned via the
        // scratch above), and their tier-2 always ran the full rule set, so the
        // shortcut's premise (the live graph is fully saturated) holds.
        if pc_lits.iter().all(|(id, pol)| {
            matches!(
                self.egraph[*id].data.known(),
                Some(Literal::Bool(b)) if *b == matches!(pol, Polarity::Positive)
            )
        }) {
            let probe = self.egraph.clone();
            let proven = self.tier35(&probe, goal) || self.split_prove(&probe, goal);
            if proven {
                self.record_proven(imp, true_, pc_lits.is_empty());
            }
            return proven;
        }

        // Tier 3: clone, assume the path condition, saturate the clone, check.
        let mut probe = self.egraph.clone();
        let true_p = probe.add(Symbolic::Lit(Literal::Bool(true)));
        let false_p = probe.add(Symbolic::Lit(Literal::Bool(false)));
        let mut unsat_pc = false;
        for (id, pol) in pc_lits {
            let want_true = matches!(pol, Polarity::Positive);
            match probe[*id].data.known() {
                Some(Literal::Bool(b)) if *b != want_true => {
                    // PC literal contradicts its required polarity → off-path,
                    // so `pc ⇒ goal` is vacuously true. (Guard also avoids a
                    // `true == false` ConstFold conflict from the union below.)
                    unsat_pc = true;
                    break;
                }
                _ => {
                    probe.union(*id, if want_true { true_p } else { false_p });
                }
            }
        }
        self.alloc.stats.prove_tier3 += 1;
        let proven = if unsat_pc {
            true
        } else {
            let probe = self.run_probe(probe);
            if probe.find(goal) == probe.find(true_p) {
                true
            } else if self.tier35(&probe, goal) {
                // Tier 3.5: non-forking ite-goal decomposition.
                true
            } else {
                // Function case split on a goal-structural ite condition.
                self.split_prove(&probe, goal)
            }
        };

        // Persist the result so future identical obligations hit tier 1.
        if proven {
            self.record_proven(imp, true_, pc_lits.is_empty());
        }
        proven
    }

    /// Enter a method block: record its control cube (shared pc of all its
    /// insts) and drop any previous block's scratch (sibling cubes are mutually
    /// exclusive, so it cannot be reused). The scratch itself is (re)built lazily
    /// on the block's first tier-3 obligation.
    pub(crate) fn begin_block(&mut self, cube: Vec<(egg::Id, Polarity)>) {
        self.current_cube = cube;
        self.in_block = true;
        self.scratch = None;
    }

    /// Leave the block walk (after the last block, or before a non-block walk):
    /// discard the scratch and clear block state.
    pub(crate) fn end_block(&mut self) {
        self.current_cube.clear();
        self.in_block = false;
        self.scratch = None;
    }

    /// Build the block scratch if absent: clone ground, assume the block cube.
    /// Ids present now are identical in both graphs (clone preserves them), so
    /// the translation map starts empty.
    fn ensure_scratch(&mut self) {
        if self.scratch.is_some() {
            return;
        }
        let true_id = self.true_();
        let false_id = self.false_();
        let cube = std::mem::take(&mut self.current_cube);
        let mut egraph = self.egraph.clone();
        // Id-space boundary = the clone's e-node count *before* the cube unions
        // (which only merge, never add ids) and any later rebuild (which can only
        // shrink `total_size`). Ground ids below it are identity-valid here.
        let watermark = egraph.total_size();
        for (id, pol) in &cube {
            let lit = if matches!(pol, Polarity::Positive) {
                true_id
            } else {
                false_id
            };
            // Same-typed conflict ⇒ `Inconsistent` (not a panic): a contradictory
            // cube marks the block path infeasible, so its goals hold vacuously.
            egraph.union(*id, lit);
        }
        egraph.rebuild();
        self.current_cube = cube;
        self.scratch = Some(BlockScratch {
            egraph,
            map: HashMap::new(),
            watermark,
            true_id,
            dirty: true,
        });
        self.alloc.stats.block_scratch_clones += 1;
    }

    /// Saturate the block scratch under the full rule set if it changed since the
    /// last saturation. Counted separately from the live/probe saturations.
    fn saturate_scratch(&mut self) {
        if !self.scratch.as_ref().is_some_and(|s| s.dirty) {
            return;
        }
        let _scope = rewrite::ScratchScope::enter();
        let mut sc = self.scratch.take().expect("scratch live");
        let before = self.alloc.stats.sat_iterations;
        sc.egraph = self.saturate_flat(sc.egraph);
        self.alloc.stats.block_scratch_saturations += 1;
        self.alloc.stats.block_scratch_iterations += self.alloc.stats.sat_iterations - before;
        sc.dirty = false;
        self.scratch = Some(sc);
    }

    /// Tier-3 against the per-block scratch. The scratch already has the block
    /// cube assumed and saturated, so an obligation whose pc is fully implied by
    /// the cube is discharged with no per-obligation clone (a "free hit").
    /// Obligations carrying extra pc literals (a perm-`Select` branch condition)
    /// clone the *warm* scratch and assume only those, then saturate.
    fn prove_via_scratch(&mut self, goal: egg::Id, pc_lits: &[(egg::Id, Polarity)]) -> bool {
        self.ensure_scratch();
        // Translate goal + pc into scratch space first: `tr` may *import* ground
        // operands (a lazy/structural ground surfaces rule-canonical leaders),
        // which dirties the scratch — so import before the saturation below.
        let tg = self.tr(goal);
        let tpc: Vec<(egg::Id, Polarity)> =
            pc_lits.iter().map(|(id, p)| (self.tr(*id), *p)).collect();
        self.saturate_scratch();

        let sc = self.scratch.as_ref().expect("scratch live");
        // A contradictory cube (or a mirrored union that conflicts under it)
        // makes every goal vacuously provable.
        if sc.egraph.classes().any(|c| c.data.is_inconsistent()) {
            return true;
        }
        if sc.egraph.find(tg) == sc.egraph.find(sc.true_id) {
            self.alloc.stats.block_scratch_freehits += 1;
            return true;
        }
        let all_sat = tpc.iter().all(|(tid, pol)| {
            matches!(
                sc.egraph[sc.egraph.find(*tid)].data.known(),
                Some(Literal::Bool(b)) if *b == matches!(pol, Polarity::Positive)
            )
        });
        let probe_base = sc.egraph.clone();

        // Free hit: the cube already implies the pc — no extra assumption needed,
        // go straight to the goal-structural decompositions on the warm scratch.
        if all_sat {
            self.alloc.stats.block_scratch_freehits += 1;
            return self.tier35(&probe_base, tg) || self.split_prove(&probe_base, tg);
        }

        // Extra literals: assume them on a clone of the warm scratch.
        let mut probe = probe_base;
        let true_p = probe.add(Symbolic::Lit(Literal::Bool(true)));
        let false_p = probe.add(Symbolic::Lit(Literal::Bool(false)));
        for (id, pol) in &tpc {
            let want_true = matches!(pol, Polarity::Positive);
            match probe[*id].data.known() {
                // Off-path literal ⇒ `pc ⇒ goal` holds vacuously.
                Some(Literal::Bool(b)) if *b != want_true => return true,
                _ => {
                    probe.union(*id, if want_true { true_p } else { false_p });
                }
            }
        }
        probe.rebuild();
        let probe = self.run_probe(probe);
        if probe.find(tg) == probe.find(true_p) {
            true
        } else if self.tier35(&probe, tg) {
            true
        } else {
            self.split_prove(&probe, tg)
        }
    }

    /// Whether `cond` already folds to a boolean literal in the **live** graph —
    /// a pure `known()` lookup, no clone. Used by the Stage-4 join merge as a
    /// cheap early drop of a dead arm; when it returns `None` the arm is kept as
    /// a structural `Select` and the dead branch is discharged later by the
    /// per-leaf perm proof (its pc becomes `block_cube ∧ ¬edge`, contradictory
    /// when the cube implies the edge, so the leaf holds vacuously). Assuming the
    /// cube in a scratch clone here would be one full graph clone *per join* —
    /// measured as the dominant cost on struct-heavy CFGs — and buys nothing the
    /// structural proof does not already get.
    pub(crate) fn fold_under_pc(&mut self, cond: egg::Id) -> Option<bool> {
        match self.egraph[self.egraph.find(cond)].data.known() {
            Some(Literal::Bool(b)) => Some(*b),
            _ => None,
        }
    }

    /// Persist a proven obligation so future identical ones hit tier 1.
    ///
    /// Default (and always for an **empty-pc** goal, where `imp == goal`): union
    /// `imp` with `true`. That path is *productive* — a proven `Eq`/discriminator
    /// goal must collapse its argument classes via `eq-true-union` /
    /// `contra-congruence` — and it is not the growth problem.
    ///
    /// Under `oob_memo`, a **conditional** obligation (`imp` is an
    /// `ite(pc.., goal, true)` chain) is instead recorded out of band. Unioning
    /// it would drag the whole chain permanently into the `true` class — the
    /// measured #1 growth driver — while the verdict is all we need for the memo.
    /// We lose auto-propagation of `goal` once its pc later lands unconditionally,
    /// at the cost of a re-prove; soundness/completeness are unaffected.
    fn record_proven(&mut self, imp: egg::Id, true_: egg::Id, pc_empty: bool) {
        if self.oob_memo && !pc_empty {
            let canon = self.egraph.find(imp);
            self.proven_imps.insert(canon);
        } else {
            self.union(imp, true_);
            self.egraph.rebuild();
        }
    }

    /// Tier 3.5 — **non-forking `ite`-goal decomposition**. When the goal's
    /// class holds an `ite` with a *`true` constant arm*, that arm's world is
    /// already discharged, so the goal reduces to proving the **other** arm
    /// under the corresponding condition polarity — **one** probe, never a fork:
    ///
    /// - `ite(c, true, e)  ⟸  e` proven under `¬c`
    /// - `ite(c, e, true)  ⟸  e` proven under `c`   (this is `c ⟹ e`, i.e. a
    ///   guarded fact / implication under a branch)
    ///
    /// Unlike a syntactic reader (which `ite-reduce` already subsumes), this
    /// *assumes* the one condition and re-saturates the single surviving arm —
    /// half of a tier-4 split, with the split variable read off the goal rather
    /// than searched, and only one branch explored. It then loops on the
    /// surviving arm, so a nested guard chain `c₁ ⟹ c₂ ⟹ … ⟹ φ` telescopes
    /// by accumulating assumptions, one per iteration. The two `false`-constant
    /// shapes are omitted: they need `¬c`/`c` to hold outright (a conjunction,
    /// not an assumption), which `ite-reduce` + saturation already deliver.
    ///
    /// Terminates without a depth cap: each iteration assumes one
    /// *previously-unknown* condition, and the e-graph has finitely many; the
    /// `assumed` set makes that explicit and stops a re-pick that would not make
    /// progress. `SILVER_OXIDE_NO_TIER35=1` disables it.
    fn tier35(&mut self, probe: &egg::EGraph<Symbolic, ConstFold>, goal: egg::Id) -> bool {
        if std::env::var_os("SILVER_OXIDE_NO_TIER35").is_some() {
            return false;
        }
        // One working graph threaded across the chain, so its ids stay stable
        // and `assumed` (a set of condition classes) is a sound progress guard.
        let mut work = probe.clone();
        let mut goal = goal;
        let mut assumed: std::collections::HashSet<egg::Id> = std::collections::HashSet::new();
        loop {
            let g = work.find(goal);
            if Self::known_bool_class(&work, g, true) {
                self.alloc.stats.prove_tier35 += 1;
                return true;
            }
            // Pick a `true`-constant-arm ite: the surviving arm is the *other*
            // branch, to be proven under the condition that reaches it.
            let mut plan: Option<(egg::Id, bool, egg::Id)> = None;
            for node in &work[g].nodes {
                let Symbolic::Ite([c, x, y]) = node else {
                    continue;
                };
                let (c, x, y) = (work.find(*c), work.find(*x), work.find(*y));
                // Prefer the positive implication `c ⟹ e` (assume `c`, the
                // as-written direction) over its negated dual `¬c ⟹ e`.
                if Self::known_bool_class(&work, y, true) {
                    plan = Some((c, true, x)); // ite(c, e, true) ⟸ e under c
                    break;
                }
                if Self::known_bool_class(&work, x, true) {
                    plan = Some((c, false, y)); // ite(c, true, e) ⟸ e under ¬c
                    break;
                }
            }
            let Some((cond, want, branch)) = plan else {
                return false;
            };
            // If the condition already can't take `want`, the constant-`true`
            // arm is the only reachable one — the goal holds outright.
            if Self::known_bool_class(&work, cond, !want) {
                self.alloc.stats.prove_tier35 += 1;
                return true;
            }
            // Progress guard: assuming a condition already assumed on this chain
            // would re-saturate an identical graph — give up instead of looping.
            if !assumed.insert(work.find(cond)) {
                return false;
            }
            let lit = work.add(Symbolic::Lit(Literal::Bool(want)));
            work.union(cond, lit);
            work.rebuild();
            work = self.run_probe(work);
            goal = branch;
        }
    }

    /// Whether e-class `id` folds to the boolean literal `b` in `probe`.
    fn known_bool_class(probe: &egg::EGraph<Symbolic, ConstFold>, id: egg::Id, b: bool) -> bool {
        matches!(probe[probe.find(id)].data.known(), Some(Literal::Bool(v)) if *v == b)
    }

    /// Whether a saturated probe discharges `goal`: either the goal is merged
    /// with `true`, or the probe's assumptions are contradictory so the goal
    /// holds vacuously (this is what closes an unreachable case's branch).
    fn probe_holds(probe: &egg::EGraph<Symbolic, ConstFold>, goal: egg::Id) -> bool {
        if probe.classes().any(|c| c.data.is_inconsistent()) {
            return true;
        }
        let Some(true_p) = probe.lookup(Symbolic::Lit(Literal::Bool(true))) else {
            return false;
        };
        probe.find(goal) == probe.find(true_p)
    }

    /// **Function-body case split.** The e-graph cannot reason by cases: an
    /// `ite` whose condition is an unconstrained boolean stays opaque, so a
    /// fact that holds in *both* branches is never concluded on its own.
    ///
    /// The block-merge fork discharges every *method* CFG join structurally
    /// (per-leaf proving through the path condition — see the block walker), so
    /// the obligations that still reach here come from **branching pure
    /// functions**: a `?:` whose arms establish `result` under different
    /// conditions (`x>=0 ? x : -x` with `ensures result>=0`), or an arm calling
    /// a function whose precondition only holds on that branch. Silicon forks
    /// the path per branch; we case-split the goal instead.
    ///
    /// Unlike the retired method-oriented split, the candidate conditions are
    /// read off **the goal term only** — not the whole path-condition cone —
    /// and there is no probe budget or iterative deepening: a function goal
    /// nests only a handful of conditions. The split is depth-first, guarded for
    /// termination by an `assumed` set (finitely many distinct conditions, none
    /// re-split twice on one path).
    fn split_prove(&mut self, probe: &egg::EGraph<Symbolic, ConstFold>, goal: egg::Id) -> bool {
        self.alloc.stats.prove_tier4 += 1;
        let mut assumed: std::collections::HashSet<egg::Id> = std::collections::HashSet::new();
        if self.split_goal(probe, goal, &mut assumed) {
            self.alloc.stats.prove_splits += 1;
            return true;
        }
        false
    }

    /// Prove `goal` by case analysis on an undecided condition drawn from the
    /// goal's own `ite` structure: assume each polarity, re-saturate, and either
    /// close the branch outright or recurse on a further condition. Both arms
    /// must close. `assumed` blocks re-splitting a condition already fixed on
    /// this path, which bounds the recursion.
    fn split_goal(
        &mut self,
        probe: &egg::EGraph<Symbolic, ConstFold>,
        goal: egg::Id,
        assumed: &mut std::collections::HashSet<egg::Id>,
    ) -> bool {
        for cond in split_candidates(probe, &[goal]) {
            if assumed.contains(&probe.find(cond)) {
                continue;
            }
            let mut all_closed = true;
            for want_true in [true, false] {
                let mut branch = probe.clone();
                let lit = branch.add(Symbolic::Lit(Literal::Bool(want_true)));
                branch.union(cond, lit);
                branch.rebuild();
                let branch = self.run_probe(branch);
                if !Self::probe_holds(&branch, goal) {
                    assumed.insert(probe.find(cond));
                    let closed = self.split_goal(&branch, goal, assumed);
                    assumed.remove(&probe.find(cond));
                    if !closed {
                        all_closed = false;
                        break;
                    }
                }
            }
            if all_closed {
                return true;
            }
        }
        false
    }

    /// Saturate a detached probe e-graph with the full rule set, inside a
    /// scratch memo scope (its instantiations die with the probe; the live
    /// base memo lets it skip rebuilding every already-live instance).
    fn run_probe(
        &mut self,
        probe: egg::EGraph<Symbolic, ConstFold>,
    ) -> egg::EGraph<Symbolic, ConstFold> {
        let _scope = crate::verify::rewrite::ScratchScope::enter();
        let iters_before = self.alloc.stats.sat_iterations;
        let out = self.saturate_flat(probe);
        self.alloc.stats.probe_saturations += 1;
        self.alloc.stats.probe_iterations += self.alloc.stats.sat_iterations - iters_before;
        out
    }

    /// Resolve which of `chunks` sits at address `addr`, consulting aliasing
    /// that may only hold under the path condition `pc_lits`.
    ///
    /// Fast path (what normal framing hits): a canonical match in the **live**
    /// graph — the address `add`ed for the read is congruent to a held chunk's
    /// address. Zero extra cost, no clone.
    ///
    /// Slow path (a miss, and only then): clone, assume the path condition, and
    /// saturate. An assumed branch literal such as `x == y` fires
    /// `eq-true-union`, which merges `x` and `y`; congruence then merges `f(x)`
    /// and `f(y)`, so the chunk `acc(x.f)` produced answers a read of `y.f`.
    /// This is what lets a predicate body like `acc(x.f) && x == y && y.f == 10`
    /// frame its `y.f` deref (guarded by the `x == y` branch literal).
    ///
    /// The returned chunk's `perm`/`value` ids are live-graph ids (the probe is
    /// a clone that never touches live state), so they are valid to use — and
    /// discharge obligations over — in the live graph.
    pub(crate) fn chunk_under_pc<'c>(
        &mut self,
        chunks: &'c [crate::verify::heap::Chunk],
        addr: egg::Id,
        pc_lits: &[(egg::Id, Polarity)],
    ) -> Option<&'c crate::verify::heap::Chunk> {
        let canon = self.egraph.find(addr);
        if let Some(c) = chunks.iter().find(|c| self.egraph.find(c.addr) == canon) {
            return Some(c);
        }
        // No unconditional match. Aliasing under the path condition can only help
        // if there is one; a truly-unheld location stays a miss.
        if pc_lits.is_empty() {
            return None;
        }
        let mut probe = self.egraph.clone();
        for (id, pol) in pc_lits {
            let want_true = matches!(pol, Polarity::Positive);
            // An unsatisfiable path condition makes every read vacuous — leave
            // the resolution to the (vacuous-pc) obligation check, don't invent
            // a chunk here.
            if matches!(probe[*id].data.known(), Some(Literal::Bool(b)) if *b != want_true) {
                return None;
            }
            let lit = probe.add(Symbolic::Lit(Literal::Bool(want_true)));
            probe.union(*id, lit);
        }
        probe.rebuild();
        let probe = self.run_probe(probe);
        let canon = probe.find(addr);
        chunks.iter().find(move |c| probe.find(c.addr) == canon)
    }

    /// Run `f` with `self.egraph` swapped for a scratch clone of the live
    /// graph, restoring the live graph — and its fixpoint cache, which `f`'s
    /// scratch runs would otherwise clobber — afterwards. The whole extent is
    /// a scratch memo scope.
    pub(crate) fn with_scratch_graph<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let _scope = crate::verify::rewrite::ScratchScope::enter();
        let live = self.egraph.clone();
        let clean = self.clean;
        let out = f(self);
        self.egraph = live;
        self.clean = clean;
        out
    }
}

/// The `ite` conditions worth splitting on: those reachable from `roots` (the
/// goal term) whose truth value is undecided — a `ConstFold`-known condition
/// would make one branch vacuous. Breadth-first from the goal, so the
/// conditions structurally nearest it — the ones that actually gate it — come
/// first; no further ranking.
fn split_candidates(probe: &egg::EGraph<Symbolic, ConstFold>, roots: &[egg::Id]) -> Vec<egg::Id> {
    use egg::Language as _;
    let mut visited: std::collections::HashSet<egg::Id> = std::collections::HashSet::new();
    let mut seen: std::collections::HashSet<egg::Id> = std::collections::HashSet::new();
    let mut out = Vec::new();
    let mut queue: std::collections::VecDeque<egg::Id> =
        roots.iter().map(|id| probe.find(*id)).collect();

    while let Some(id) = queue.pop_front() {
        if !visited.insert(id) {
            continue;
        }
        // A class with a known constant value is opaque to the split search:
        // its nodes are equalities/arithmetic *residue* (e.g. the `1/1` class
        // accretes every cancelled borrow/give-back pair `(x−p)+p`), and no
        // condition reachable only through it can change the goal — the value
        // here is already decided. Descending it only floods the candidate list.
        if probe[id].data.known().is_some() {
            continue;
        }
        for node in &probe[id].nodes {
            if let Symbolic::Ite([c, _, _]) = node {
                let c = probe.find(*c);
                if probe[c].data.known().is_none() && seen.insert(c) {
                    out.push(c);
                }
            }
            for child in node.children() {
                queue.push_back(probe.find(*child));
            }
        }
    }
    out
}

/// One egg run over `rules`. Returns the graph and the iteration log — the
/// caller records the log into the stats once the rule borrow is released.
fn run_rules<'r>(
    egraph: egg::EGraph<Symbolic, ConstFold>,
    rules: impl IntoIterator<Item = &'r egg::Rewrite<Symbolic, ConstFold>>,
    iter_limit: Option<usize>,
) -> (egg::EGraph<Symbolic, ConstFold>, Vec<egg::Iteration<()>>) {
    // Explicit limits: egg's defaults (30 iterations, 10k nodes) are SILENT
    // truncation points — a run that hits one simply stops mid-saturation and
    // the caller sees an ordinary "not proven", which surfaced as a false
    // insufficient-permission at ~20 match arms (one tower level collapses per
    // iteration, so deep-but-terminating collapses need iterations ∝ depth).
    let runner = egg::Runner::default()
        .with_scheduler(egg::SimpleScheduler)
        .with_node_limit(100_000)
        .with_iter_limit(iter_limit.unwrap_or(100))
        .with_egraph(egraph);
    let runner = runner.run(rules);
    (runner.egraph, runner.iterations)
}
