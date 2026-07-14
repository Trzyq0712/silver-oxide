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
    /// Per-unit lazy-instantiation rules for **generic** domain axioms (one per
    /// axiom, minted by `assume_axioms`; ground axioms are pre-added instead),
    /// pure `forall`s (one per quantifier), and verified function bodies (one
    /// per already-certified `fn_certs` entry — see `rewrite::function_rule`).
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
    /// Ordered log of heap-reconstruction events (`FromSnap`/`Unfold` slot
    /// addresses), recorded during a **function** body walk so the post-walk
    /// purification pass can rebuild each `Deref`'s value as a pure recipe term
    /// (`unwrap(proj_i(snap))`). `None` for methods and resources — they never
    /// purify. See `declaration::purify_function`.
    pub(crate) heap_events: Option<Vec<crate::verify::declaration::HeapEvent>>,
    /// Fixpoint cache: the rule tier the live e-graph is known saturated under,
    /// with the rule-set sizes that saturation saw (ADT rules and axiom rules
    /// grow mid-unit; a grown set invalidates the fixpoint). `None` when any
    /// node/union landed since. Lets `saturate`/`reduce` skip whole runner
    /// invocations — most are re-runs on an unchanged graph.
    clean: Option<(CleanLevel, usize, usize)>,
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
            egraph: egg::EGraph::new(ConstFold::new(alloc.ctor_table())),
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
            heap_events: None,
            clean: None,
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
        crate::verify::rewrite::new_memo_generation();
        self.egraph = self.saturate_flat(egraph);
        self.alloc.stats.saturations += 1;
        self.clean = Some(self.clean_tag(CleanLevel::Full));
    }

    /// One full-rule-set run, shared by [`Self::saturate`] and
    /// [`Self::run_probe`]. The instantiation memo generation is the caller's
    /// to set.
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
        crate::verify::rewrite::new_memo_generation();
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
        // O(classes) inconsistency scan, which most calls never need.
        if self.egraph.find(imp) == self.egraph.find(true_) {
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
        // the tier-2 verdict again. Fail without paying the clone.
        if pc_lits.iter().all(|(id, pol)| {
            matches!(
                self.egraph[*id].data.known(),
                Some(Literal::Bool(b)) if *b == matches!(pol, Polarity::Positive)
            )
        }) {
            return false;
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
            probe.find(goal) == probe.find(true_p)
        };

        // Persist the result so future identical obligations hit tier 1.
        if proven {
            self.union(imp, true_);
            self.egraph.rebuild();
        }
        proven
    }

    /// Saturate a detached probe e-graph with the full rule set.
    fn run_probe(
        &mut self,
        probe: egg::EGraph<Symbolic, ConstFold>,
    ) -> egg::EGraph<Symbolic, ConstFold> {
        crate::verify::rewrite::new_memo_generation();
        self.saturate_flat(probe)
    }
}

/// One egg run over `rules`. Returns the graph and the iteration log — the
/// caller records the log into the stats once the rule borrow is released.
fn run_rules<'r>(
    egraph: egg::EGraph<Symbolic, ConstFold>,
    rules: impl IntoIterator<Item = &'r egg::Rewrite<Symbolic, ConstFold>>,
    iter_limit: Option<usize>,
) -> (egg::EGraph<Symbolic, ConstFold>, Vec<egg::Iteration<()>>) {
    let mut runner = egg::Runner::default()
        .with_scheduler(egg::SimpleScheduler)
        .with_egraph(egraph);
    if let Some(limit) = iter_limit {
        runner = runner.with_iter_limit(limit);
    }
    let runner = runner.run(rules);
    (runner.egraph, runner.iterations)
}
