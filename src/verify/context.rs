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
        Declaration::Method(m) => insts_wild(&m.insts),
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
        merged
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
        self.add(Symbolic::Binary(BinOp::Lt, [zero, perm]))
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

    /// One full-rule-set run, shared by [`Self::saturate`] and
    /// [`Self::run_probe`]. Memo scoping is ambient (see `rewrite::Memo`):
    /// live runs write the persistent base, scratch scopes an overlay.
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
        let id = self.egraph.add(node);
        if self.egraph.total_size() != before {
            self.clean = None;
        }
        id
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

        // Tier 3 shortcut: if every PC literal already carries its required
        // polarity in the just-saturated live graph, assuming the PC adds
        // nothing — the probe would re-saturate an identical graph and reach
        // the tier-2 verdict again. Skip straight to the tier-4 case split
        // (an empty-pc goal — a method's exit exhale after a CFG join — is
        // exactly the shape that needs one).
        if pc_lits.iter().all(|(id, pol)| {
            matches!(
                self.egraph[*id].data.known(),
                Some(Literal::Bool(b)) if *b == matches!(pol, Polarity::Positive)
            )
        }) {
            let probe = self.egraph.clone();
            let proven = self.tier35(&probe, goal) || self.split_prove(&probe, goal, &[goal]);
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
                // Tier 4: prove by case analysis on an ite condition.
                let roots: Vec<egg::Id> = std::iter::once(goal)
                    .chain(pc_lits.iter().map(|(id, _)| *id))
                    .collect();
                self.split_prove(&probe, goal, &roots)
            }
        };

        // Persist the result so future identical obligations hit tier 1.
        if proven {
            self.record_proven(imp, true_, pc_lits.is_empty());
        }
        proven
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
    fn known_bool_class(
        probe: &egg::EGraph<Symbolic, ConstFold>,
        id: egg::Id,
        b: bool,
    ) -> bool {
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

    /// Tier 4 — **case split**. The e-graph cannot reason by cases: an `ite`
    /// whose condition is an unconstrained boolean stays opaque, so a fact that
    /// holds in *both* branches is never concluded. That is exactly what a CFG
    /// join leaves behind — the held permission is a sum of branch-scaled
    /// `ite(flag, p, 0)` terms, and the exit exhale needs it under a disjunction
    /// of the flags. Pick an undecided `ite` condition from the cone of the goal
    /// and the path condition, and prove the goal twice — assuming it, and
    /// assuming its negation. If both branches close, the goal holds.
    ///
    /// Searched by **iterative deepening**: every candidate is tried at depth 1
    /// before any pair at depth 2, so a goal needing one split (the common
    /// case) costs at most `2·|candidates|` probe saturations, and a
    /// mis-ordered candidate costs one level, not a subtree. `SPLIT_BUDGET`
    /// caps total probe saturations per goal so an unprovable goal degrades
    /// gracefully.
    fn split_prove(
        &mut self,
        probe: &egg::EGraph<Symbolic, ConstFold>,
        goal: egg::Id,
        roots: &[egg::Id],
    ) -> bool {
        self.alloc.stats.prove_tier4 += 1;
        // Diagnostic kill switch: run with SILVER_OXIDE_NO_TIER4=1 to measure
        // which members/goals depend on the case split (everything else in the
        // prove path is unaffected).
        if std::env::var_os("SILVER_OXIDE_NO_TIER4").is_some() {
            return false;
        }
        let mut budget = SPLIT_BUDGET;
        for depth in 1..=SPLIT_DEPTH {
            if self.split_tree(probe, goal, roots, depth, &mut budget) {
                self.alloc.stats.prove_splits += 1;
                return true;
            }
            if budget == 0 {
                break;
            }
        }
        false
    }

    /// Prove `goal` by a case tree of at most `depth` nested splits: a branch
    /// that does not close outright recurses (both arms must close).
    fn split_tree(
        &mut self,
        probe: &egg::EGraph<Symbolic, ConstFold>,
        goal: egg::Id,
        roots: &[egg::Id],
        depth: usize,
        budget: &mut usize,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        let candidates = split_candidates(probe, roots);
        if crate::verify::viz::dump_perm_enabled() {
            eprintln!(
                "[split-dump] depth {depth}: {} candidates, budget {budget}",
                candidates.len()
            );
        }
        for cond in candidates {
            if *budget < 2 {
                return false;
            }
            let mut all_closed = true;
            for want_true in [true, false] {
                if *budget == 0 {
                    return false;
                }
                *budget -= 1;
                let mut branch = probe.clone();
                let lit = branch.add(Symbolic::Lit(Literal::Bool(want_true)));
                branch.union(cond, lit);
                branch.rebuild();
                let branch = self.run_probe(branch);
                if !Self::probe_holds(&branch, goal)
                    && !self.split_tree(&branch, goal, roots, depth - 1, budget)
                {
                    all_closed = false;
                    break;
                }
            }
            if all_closed {
                if crate::verify::viz::dump_perm_enabled() {
                    eprintln!(
                        "[split-dump] goal closed by splitting on:\n{}",
                        crate::verify::viz::dump_term(self, cond, 4),
                    );
                }
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
        self.saturate_flat(probe)
    }

    /// Collapse a permission **sum of `ite`s that share conditions** into a
    /// single nested `ite`, by repeatedly applying the sound identity
    /// `ite(c, a, x) + ite(c, b, y) ≡ ite(c, a+b, x+y)` (and the const-folding
    /// `k + ite(...)`). This is what a CFG join over an N-arm `match` needs: the
    /// held permission is a nested **indicator partition**
    /// `ite(c_0, 1, ite(c_1, 1, … 0))`-shaped sum with one summand per arm, and
    /// merging the same-condition summands collapses it to `ite(∨c_k, 1, 0)` in
    /// O(N) steps — the exact permission the exit exhale needs, discharged
    /// **without any case split** and scaling to any arm count.
    ///
    /// Returns a value-equal e-class built fresh (not unioned into `id`), so it
    /// is used only where asked (the failure path of a permission comparison),
    /// never perturbing the live graph on passing code. `budget` caps added
    /// nodes.
    pub(crate) fn merge_ite_sum(&mut self, id: egg::Id, budget: &mut usize) -> egg::Id {
        // Flatten the `+` spine into a list of summands (only `+`, not `-` —
        // a partition is all-additive; a `-` summand is left opaque).
        let mut summands = Vec::new();
        self.flatten_plus(self.egraph.find(id), &mut summands, &mut Vec::new());
        self.merge_summands(summands, budget)
    }

    fn flatten_plus(&self, id: egg::Id, out: &mut Vec<egg::Id>, seen: &mut Vec<egg::Id>) {
        let id = self.egraph.find(id);
        if seen.contains(&id) {
            out.push(id);
            return;
        }
        if self.egraph[id].data.known().is_some() {
            out.push(id);
            return;
        }
        seen.push(id);
        // A class holding an `ite` node is a partition **summand leaf** — do not
        // descend a `+` node it may also hold (that `+` is cancellation residue,
        // e.g. `x = (x - p) + p`, often self-referential; descending it pulls a
        // spurious zero-valued term into the sum and defeats the collapse).
        let has_ite = self
            .egraph[id]
            .nodes
            .iter()
            .any(|n| matches!(n, Symbolic::Ite(_)));
        let plus = if has_ite {
            None
        } else {
            self.egraph[id].nodes.iter().find_map(|n| match n {
                Symbolic::Binary(BinOp::Plus, k) => Some(*k),
                _ => None,
            })
        };
        match plus {
            Some([a, b]) => {
                self.flatten_plus(a, out, seen);
                self.flatten_plus(b, out, seen);
            }
            None => out.push(id),
        }
        seen.pop();
    }

    /// Sum a list of summands, merging any two that share an outer `ite`
    /// condition via `ite(c,a,x)+ite(c,b,y) => ite(c, a+b, x+y)`, then recursing
    /// into the merged arms. Const summands fold together.
    fn merge_summands(&mut self, summands: Vec<egg::Id>, budget: &mut usize) -> egg::Id {
        use num::BigRational;
        // The outer `ite` condition of a class, if any (const classes = leaf).
        let cond_of = |cx: &Self, x: egg::Id| -> Option<egg::Id> {
            if cx.egraph[x].data.known().is_some() {
                return None;
            }
            cx.egraph[x].nodes.iter().find_map(|n| match n {
                Symbolic::Ite([c, _, _]) => Some(cx.egraph.find(*c)),
                _ => None,
            })
        };
        // Partition summands by their outer condition; const/opaque ones pool.
        let mut const_sum = BigRational::from(num::BigInt::from(0));
        let mut has_const = false;
        let mut opaque: Vec<egg::Id> = Vec::new();
        // Preserve first-seen order of conditions for a stable rebuild.
        let mut groups: Vec<(egg::Id, Vec<egg::Id>)> = Vec::new();
        for s in summands {
            let s = self.egraph.find(s);
            if let Some(Literal::Real(r)) = self.egraph[s].data.known() {
                const_sum += r;
                has_const = true;
                continue;
            }
            match cond_of(self, s) {
                Some(c) => match groups.iter_mut().find(|(gc, _)| *gc == c) {
                    Some((_, v)) => v.push(s),
                    None => groups.push((c, vec![s])),
                },
                None => opaque.push(s),
            }
        }
        // Rebuild: sum of (per-condition merged ites) + opaque + const.
        let mut terms: Vec<egg::Id> = Vec::new();
        for (c, members) in groups {
            if members.len() == 1 {
                terms.push(members[0]);
                continue;
            }
            if *budget == 0 {
                // Out of budget: fall back to a plain (unmerged) sum of the
                // members themselves — value-equal by construction. (Summing
                // their *then* arms is NOT: it drops the conditions and the
                // else sides.)
                let mut acc = members[0];
                for &m in &members[1..] {
                    acc = self.add(Symbolic::Binary(BinOp::Plus, [acc, m]));
                }
                terms.push(acc);
                continue;
            }
            // Merge all same-condition members: collect their then/else arms,
            // recurse on each side.
            let mut thens = Vec::new();
            let mut elses = Vec::new();
            for m in members {
                if let Some((_, t, e)) = self.egraph[m].nodes.iter().find_map(|n| match n {
                    Symbolic::Ite([mc, t, e]) if self.egraph.find(*mc) == c => Some((*mc, *t, *e)),
                    _ => None,
                }) {
                    thens.push(t);
                    elses.push(e);
                }
            }
            *budget = budget.saturating_sub(1);
            let t = self.merge_summands(thens, budget);
            let e = self.merge_summands(elses, budget);
            terms.push(self.add(Symbolic::Ite([c, t, e])));
        }
        terms.extend(opaque);
        if has_const {
            terms.push(self.add(Symbolic::Lit(Literal::Real(const_sum))));
        }
        if terms.is_empty() {
            return self.add(Symbolic::Lit(Literal::Real(BigRational::from(num::BigInt::from(0)))));
        }
        let mut acc = terms[0];
        for &t in &terms[1..] {
            acc = self.add(Symbolic::Binary(BinOp::Plus, [acc, t]));
        }
        acc
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

/// How many nested `ite` conditions tier 4 may split on. A CFG join of an
/// n-way branch needs up to n-1 nested splits (one per excluded arm); 3 covers
/// the 4-variant enums in the Prusti output.
const SPLIT_DEPTH: usize = 3;

/// Cap on probe saturations per tier-4 goal: an unprovable goal stops costing
/// time instead of exploring the full case tree. Sized empirically: the widest
/// provable goal in the Prusti benchmark (`m_rect_normalize`'s mid-body
/// exhale, a depth-2 tree over a ~20-condition cone) needs ~350 probes;
/// raising further buys nothing (the one remaining failure is
/// budget-insensitive up to 2048) and each failing goal burns the full cap.
const SPLIT_BUDGET: usize = 384;

/// The `ite` conditions worth splitting on: those in the **cone** of `roots`
/// (the goal and the path-condition literals) whose truth value is undecided
/// (a `ConstFold`-known condition would make one branch vacuous). The cone,
/// not the whole e-graph: a saturated probe holds hundreds of `ite`s with no
/// bearing on the goal, and trying each is what makes naive splitting
/// exponential. Breadth-first from the roots, so the conditions structurally
/// nearest the goal — the ones that actually gate it — are tried first; no
/// further ranking.
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
        // here is already decided. Descending it floods the candidate list
        // (its residue grows with program size, pushing the useful candidate
        // past the split budget — the N=20 match-arm cliff).
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
    let mut runner = egg::Runner::default()
        .with_scheduler(egg::SimpleScheduler)
        .with_node_limit(100_000)
        .with_iter_limit(iter_limit.unwrap_or(100))
        .with_egraph(egraph);
    let runner = runner.run(rules);
    (runner.egraph, runner.iterations)
}
