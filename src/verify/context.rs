use std::collections::HashMap;

use egg::{EGraph, Id};

use crate::{
    verify::{
        analysis::ConstFold,
        func_registry::FuncRegistry,
        heap::{Chunk, Heap, LocationKind},
        lang::{FuncId, Symbolic},
        rewrite,
    },
    vmir::{BinOp, Declaration, Literal, MemberId, Polarity, Type},
};
use lasso::{Rodeo, Spur};
use typed_index_collections::TiVec;

/// A resource's well-formedness proof, kept for **reuse at call sites**: the
/// saturated proof e-graph (carrying every proven merge) plus the root
/// e-classes needed to re-attach it. Grafting this into a caller's e-graph
/// (formal params → actual args) transfers the proven facts for free, without
/// re-walking or re-saturating the resource body.
pub(crate) struct ResourceCertificate {
    pub(crate) egraph: EGraph<Symbolic, ConstFold>,
    pub(crate) fresh_types: HashMap<u32, Type>,
    pub(crate) func_ret_types: HashMap<FuncId, Type>,
    /// Formal-param e-classes, in order (the call's args substitute these).
    pub(crate) params: Vec<Id>,
    /// Result heap-delta chunks as `(kind, addr, perm, value)` — the **merged**
    /// (accounting) view, chunks keyed by congruent address with perms summed.
    /// The `LocationKind` is captured at build (VMIR-sourced) so grafting groups
    /// them without inference. Used by inhale/exhale grafting (`graft_certificate`).
    pub(crate) delta: Vec<(LocationKind, Id, Id, Id)>,
    /// **Unmerged, program-ordered** footprint: one `(kind, addr, perm, value)`
    /// per syntactic `acc`, in body order. Aliased accs (same address) stay
    /// separate, so the snapshot keeps one member per acc; `value` is the merged
    /// chunk value at that address, so aliased slots share it. Used by
    /// fold/unfold (the snapshot layout).
    pub(crate) footprint: Vec<(LocationKind, Id, Id, Id)>,
    /// Result boolean e-class.
    pub(crate) bool_id: Id,
}

/// A (non-recursive, heap-free) function's verified body, kept for **inlining at
/// call sites**: the saturated body e-graph plus the roots needed to re-attach
/// it. Grafting it (formal params → actual args) yields the e-class of the
/// function's result expression, which the caller `union`s with the uninterpreted
/// `FuncApp` node to install the definitional equality `f(args) == body`.
pub(crate) struct FunctionCertificate {
    pub(crate) egraph: EGraph<Symbolic, ConstFold>,
    pub(crate) fresh_types: HashMap<u32, Type>,
    pub(crate) func_ret_types: HashMap<FuncId, Type>,
    /// Formal-param e-classes, in order (the call's args substitute these).
    pub(crate) params: Vec<Id>,
    /// The body's result e-class.
    pub(crate) result: Id,
}

impl ResourceCertificate {
    fn src(&self) -> TransplantSrc<'_> {
        TransplantSrc {
            egraph: &self.egraph,
            fresh_types: &self.fresh_types,
            func_ret_types: &self.func_ret_types,
        }
    }
}

impl FunctionCertificate {
    fn src(&self) -> TransplantSrc<'_> {
        TransplantSrc {
            egraph: &self.egraph,
            fresh_types: &self.fresh_types,
            func_ret_types: &self.func_ret_types,
        }
    }
}

/// The read-only slice of a certificate that [`transplant`] copies from: the
/// source e-graph and its type side-oracles. Lets grafting be shared between
/// [`ResourceCertificate`] and [`FunctionCertificate`].
struct TransplantSrc<'a> {
    egraph: &'a EGraph<Symbolic, ConstFold>,
    fresh_types: &'a HashMap<u32, Type>,
    func_ret_types: &'a HashMap<FuncId, Type>,
}

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
    /// axiom, minted by `assume_axioms`; ground axioms are pre-added instead).
    /// Chained into full saturation (incl. the tier-3 probe) but not `reduce`.
    pub(crate) axiom_rules: Vec<egg::Rewrite<Symbolic, ConstFold>>,
    fresh_counter: usize,
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
    /// Verified non-recursive function bodies, keyed by `MemberId`. Read from the
    /// shared `eval_pure_inst` to inline (`union`) a call's body definition. `None`
    /// in isolated contexts (unit tests) that never evaluate a `FunctionCall`.
    pub(crate) fn_certs: Option<&'a HashMap<MemberId, FunctionCertificate>>,
}

impl<'a> VerifyContext<'a> {
    pub(crate) fn new(
        interner: &'a Rodeo,
        decls: &'a TiVec<MemberId, Declaration>,
        groups: &'a Rodeo<Spur>,
        alloc: &'a mut FuncRegistry,
    ) -> Self {
        Self {
            egraph: egg::EGraph::default(),
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
        }
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
    /// static rules plus the ADT reductions minted so far by the allocator.
    pub(crate) fn saturate(&mut self) {
        let rules: Vec<_> = self
            .static_rules
            .iter()
            .chain(self.alloc.rules())
            .chain(self.axiom_rules.iter())
            .cloned()
            .collect();
        let egraph = std::mem::take(&mut self.egraph);
        let runner = egg::Runner::default().with_egraph(egraph).run(&rules);
        self.alloc.stats.saturations += 1;
        self.alloc.stats.record_run(&runner.iterations);
        self.egraph = runner.egraph;
    }

    /// Run only the terminating structural reductions in place. Used after
    /// `fold`/`unfold` to collapse snapshot towers (so repeated round-trips
    /// don't grow the e-graph) without the cost/divergence risk of full
    /// saturation.
    pub(crate) fn reduce(&mut self) {
        let rules: Vec<_> = self
            .static_reduce
            .iter()
            .chain(self.alloc.rules())
            .cloned()
            .collect();
        let egraph = std::mem::take(&mut self.egraph);
        let runner = egg::Runner::default().with_egraph(egraph).run(&rules);
        self.alloc.stats.reduces += 1;
        self.alloc.stats.record_run(&runner.iterations);
        self.egraph = runner.egraph;
    }

    pub(crate) fn add(&mut self, node: Symbolic) -> egg::Id {
        self.egraph.add(node)
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
        self.egraph.add(Symbolic::FuncApp(id, type_args, args))
    }

    /// Graft a resource certificate into this (caller) e-graph, substituting the
    /// certificate's formal params for `args`. Returns the grafted result heap
    /// delta, boolean e-class, and the transplanted **footprint** slots
    /// `(perm, value)` in program order — the snapshot layout a snapshot-yielding
    /// inhale/exhale builds its `cons` from (the footprint values share e-classes
    /// with the delta chunk values, so they bind to the caller's heap values
    /// through the usual union/subtract accounting). Every merge proven in the
    /// certificate transfers for free (reconstruction is keyed by certificate
    /// e-class), so the caller never re-derives or re-saturates the resource's
    /// facts.
    pub(crate) fn graft_certificate(
        &mut self,
        cert: &ResourceCertificate,
        args: &[egg::Id],
    ) -> (Heap, egg::Id, Vec<(Id, Id)>) {
        self.alloc.stats.cert_grafts += 1;
        let mut subst: HashMap<Id, Id> = HashMap::new();
        for (p, a) in cert.params.iter().zip(args) {
            subst.insert(cert.egraph.find(*p), *a);
        }
        let mut memo: HashMap<Id, Transplanted> = HashMap::new();
        let src = cert.src();
        let mut delta = Heap::empty();
        for (kind, addr, perm, value) in &cert.delta {
            let a = transplant(self, &src, *addr, &subst, &mut memo);
            let p = transplant(self, &src, *perm, &subst, &mut memo);
            let v = transplant(self, &src, *value, &subst, &mut memo);
            delta = delta.with_chunk(kind, Chunk::new(a, p, v));
        }
        let bool_id = transplant(self, &src, cert.bool_id, &subst, &mut memo);
        // The memo is shared, so a footprint value lands in the same caller
        // e-class as its delta chunk value.
        let footprint: Vec<(Id, Id)> = cert
            .footprint
            .iter()
            .map(|(_, _, perm, value)| {
                let p = transplant(self, &src, *perm, &subst, &mut memo);
                let v = transplant(self, &src, *value, &subst, &mut memo);
                (p, v)
            })
            .collect();
        self.egraph.rebuild();
        (delta, bool_id, footprint)
    }

    /// Seed a footprint-graft substitution with the call's `args` bound to the
    /// cert's formal params (keyed in the cert's id space). `fold`/`unfold` grow
    /// this map slot-by-slot with each slot's actual value (see
    /// [`graft_footprint_slot`](Self::graft_footprint_slot)) so that
    /// value-dependent addresses — e.g. an inner predicate `P(this.f)` whose
    /// argument is a field read — resolve against the real field values.
    pub(crate) fn footprint_param_subst(
        &self,
        cert: &ResourceCertificate,
        args: &[Id],
    ) -> HashMap<Id, Id> {
        let mut subst: HashMap<Id, Id> = HashMap::new();
        for (p, a) in cert.params.iter().zip(args) {
            subst.insert(cert.egraph.find(*p), *a);
        }
        subst
    }

    /// Transplant one footprint slot's `(addr, perm)` into this e-graph under
    /// `subst` (the call's params plus any already-resolved earlier-slot values).
    /// The caller binds `cert.egraph.find(slot.value) -> actual` after reading the
    /// slot, so a later slot's value-dependent address resolves correctly.
    pub(crate) fn graft_footprint_slot(
        &mut self,
        cert: &ResourceCertificate,
        addr: Id,
        perm: Id,
        subst: &HashMap<Id, Id>,
    ) -> (Id, Id) {
        let mut memo: HashMap<Id, Transplanted> = HashMap::new();
        let src = cert.src();
        let a = transplant(self, &src, addr, subst, &mut memo);
        let p = transplant(self, &src, perm, subst, &mut memo);
        self.egraph.rebuild();
        (a, p)
    }

    /// Transplant a predicate cert's body boolean for `args`, substituting each
    /// footprint slot's cert value with the caller's actual `values` (so the
    /// body's pure facts are expressed over the fold/unfold-site values).
    pub(crate) fn graft_pred_bool(
        &mut self,
        cert: &ResourceCertificate,
        args: &[Id],
        values: &[Id],
    ) -> Id {
        let mut subst: HashMap<Id, Id> = HashMap::new();
        for (p, a) in cert.params.iter().zip(args) {
            subst.insert(cert.egraph.find(*p), *a);
        }
        // Substitute per-acc (layout) slot value with the fold/unfold-site value.
        // Aliased slots share their cert value, and the caller supplies the same
        // (per-location) value for each, so the inserts agree.
        for (slot, &v) in cert.footprint.iter().zip(values) {
            // `slot.3` is the footprint value e-class (`(kind, addr, perm, value)`).
            subst.insert(cert.egraph.find(slot.3), v);
        }
        let mut memo: HashMap<Id, Transplanted> = HashMap::new();
        let src = cert.src();
        let b = transplant(self, &src, cert.bool_id, &subst, &mut memo);
        self.egraph.rebuild();
        b
    }

    /// Inline a verified function body at a call site: transplant the cert's
    /// result e-class under `params → args`, yielding the caller-space e-class of
    /// the function's body expression. The caller `union`s this with the
    /// uninterpreted `FuncApp(f, args)` node to install `f(args) == body`.
    pub(crate) fn graft_function(&mut self, cert: &FunctionCertificate, args: &[Id]) -> Id {
        self.alloc.stats.cert_grafts += 1;
        let mut subst: HashMap<Id, Id> = HashMap::new();
        for (p, a) in cert.params.iter().zip(args) {
            subst.insert(cert.egraph.find(*p), *a);
        }
        let mut memo: HashMap<Id, Transplanted> = HashMap::new();
        let src = cert.src();
        let result = transplant(self, &src, cert.result, &subst, &mut memo);
        self.egraph.rebuild();
        result
    }

    pub(crate) fn fresh_symbolic_value(&mut self, ty: Type) -> egg::Id {
        let id = self.fresh_counter as u32;
        self.fresh_counter += 1;
        self.fresh_types.insert(id, ty);
        self.egraph.add(Symbolic::Fresh(id))
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

        // Tier 0: the held facts are contradictory (e.g. a field location holds
        // > 1/1 permission) — every goal is vacuously provable.
        if self.is_inconsistent() {
            return true;
        }
        // Tier 1: already true (memoized / trivial).
        if self.egraph.find(imp) == self.egraph.find(true_) {
            return true;
        }
        // Tier 2: saturate the live graph and re-check (no clone). Saturation can
        // also expose a contradiction, so re-check inconsistency too.
        self.saturate();
        if self.is_inconsistent() || self.egraph.find(imp) == self.egraph.find(true_) {
            return true;
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
            let rules: Vec<_> = self
                .static_rules
                .iter()
                .chain(self.alloc.rules())
                .chain(self.axiom_rules.iter())
                .cloned()
                .collect();
            let runner = egg::Runner::default().with_egraph(probe).run(&rules);
            self.alloc.stats.record_run(&runner.iterations);
            let probe = runner.egraph;
            probe.find(goal) == probe.find(true_p)
        };

        // Persist the result so future identical obligations hit tier 1.
        if proven {
            self.egraph.union(imp, true_);
            self.egraph.rebuild();
        }
        proven
    }
}

/// Copy a certificate e-class (and everything it reaches) into `caller`,
/// substituting formal params per `subst`, memoized by certificate e-class.
/// Two-phase per e-class (reserve a placeholder, then union every rebuilt node
/// into it) so cycles terminate and **all merges in the e-class collapse to one
/// caller e-class** — that is how proven equalities transfer for free.
/// Per-e-class transplant state: `InProgress` while its nodes are being rebuilt
/// (carrying a lazily-minted back-edge placeholder iff a cycle is hit), then
/// `Done` with the resulting caller e-class.
enum Transplanted {
    InProgress(Option<Id>),
    Done(Id),
}

fn transplant(
    caller: &mut VerifyContext<'_>,
    src: &TransplantSrc<'_>,
    id: Id,
    subst: &HashMap<Id, Id>,
    memo: &mut HashMap<Id, Transplanted>,
) -> Id {
    let cc = src.egraph.find(id);
    if let Some(&a) = subst.get(&cc) {
        return a;
    }
    let cc_ty = || {
        infer_type(
            src.egraph,
            src.fresh_types,
            src.func_ret_types,
            cc,
            &mut HashMap::new(),
        )
        .unwrap_or(Type::Int)
    };
    match memo.get(&cc) {
        Some(Transplanted::Done(a)) => return *a,
        // Cyclic back-edge: this class is still being built. Mint a placeholder
        // (once) for the cycle to point at; it's unioned with the result below.
        Some(Transplanted::InProgress(Some(ph))) => return *ph,
        Some(Transplanted::InProgress(None)) => {
            let ph = caller.fresh_symbolic_value(cc_ty());
            memo.insert(cc, Transplanted::InProgress(Some(ph)));
            return ph;
        }
        None => {}
    }
    memo.insert(cc, Transplanted::InProgress(None));

    let nodes = src.egraph[cc].nodes.clone();
    let mut built: Vec<Id> = Vec::with_capacity(nodes.len());
    for node in &nodes {
        let b = match node {
            // A fresh value has no structure to rebuild — mint a fresh of the
            // same type. (Acyclic classes thus get NO redundant placeholder.)
            Symbolic::Fresh(_) => caller.fresh_symbolic_value(cc_ty()),
            Symbolic::Lit(l) => caller.add(Symbolic::Lit(l.clone())),
            Symbolic::Binary(op, [l, r]) => {
                let l = transplant(caller, src, *l, subst, memo);
                let r = transplant(caller, src, *r, subst, memo);
                caller.add(Symbolic::Binary(*op, [l, r]))
            }
            Symbolic::Ite([a, b, c]) => {
                let a = transplant(caller, src, *a, subst, memo);
                let b = transplant(caller, src, *b, subst, memo);
                let c = transplant(caller, src, *c, subst, memo);
                caller.add(Symbolic::Ite([a, b, c]))
            }
            Symbolic::RealCast(x) => {
                let x = transplant(caller, src, *x, subst, memo);
                caller.add(Symbolic::RealCast(x))
            }
            Symbolic::FuncApp(m, tys, fargs) => {
                let fargs: Box<[Id]> = fargs
                    .iter()
                    .map(|a| transplant(caller, src, *a, subst, memo))
                    .collect();
                let ret = src.func_ret_types.get(m).cloned().unwrap_or(Type::Int);
                // The ground type instantiation has no e-class — copy it verbatim.
                caller.add_func_app_id(*m, tys.clone(), ret, fargs)
            }
        };
        built.push(b);
    }

    // egg classes always have ≥1 node; unify all rebuilt nodes (and the back-edge
    // placeholder, if a cycle minted one) into a single representative.
    let rep = built[0];
    for &b in &built[1..] {
        caller.egraph.union(rep, b);
    }
    if let Some(Transplanted::InProgress(Some(ph))) = memo.get(&cc) {
        let ph = *ph;
        caller.egraph.union(rep, ph);
    }
    let rep = caller.egraph.find(rep);
    memo.insert(cc, Transplanted::Done(rep));
    rep
}

/// Reconstruct an e-class's type from the type-free e-graph (memoized,
/// cycle-safe, best-effort): `Lit`→literal type, `RealCast`→Real,
/// `Binary`→`Bool` for comparisons else operand type, `Ite`→branch type, and
/// the irreducible `Fresh`/`FuncApp` sources from the supplied side-oracle maps.
/// Shared by grafting and the visualization.
pub(crate) fn infer_type(
    egraph: &EGraph<Symbolic, ConstFold>,
    fresh_types: &HashMap<u32, Type>,
    func_ret_types: &HashMap<FuncId, Type>,
    id: Id,
    memo: &mut HashMap<Id, Option<Type>>,
) -> Option<Type> {
    let canon = egraph.find(id);
    if let Some(t) = memo.get(&canon) {
        return t.clone();
    }
    memo.insert(canon, None); // seed for cycles
    let nodes = egraph[canon].nodes.clone();
    let mut result = None;
    for node in &nodes {
        let t = match node {
            Symbolic::Lit(l) => Some(lit_type(l)),
            Symbolic::RealCast(_) => Some(Type::Real),
            Symbolic::Fresh(u) => fresh_types.get(u).cloned(),
            // Addresses are ordinary func apps: a field/predicate address function
            // records its `Addr{..}` return type in `func_ret_types` like any other.
            Symbolic::FuncApp(f, _, _) => func_ret_types.get(f).cloned(),
            Symbolic::Binary(op, [l, _]) => match op {
                BinOp::Eq | BinOp::Lt => Some(Type::Bool),
                _ => infer_type(egraph, fresh_types, func_ret_types, *l, memo),
            },
            Symbolic::Ite([_, then, _]) => {
                infer_type(egraph, fresh_types, func_ret_types, *then, memo)
            }
        };
        if t.is_some() {
            result = t;
            break;
        }
    }
    memo.insert(canon, result.clone());
    result
}

/// Type of a literal value.
pub(crate) fn lit_type(lit: &Literal) -> Type {
    match lit {
        Literal::Null => Type::Ref,
        Literal::Bool(_) => Type::Bool,
        Literal::Int(_) => Type::Int,
        Literal::Real(_) => Type::Real,
    }
}
