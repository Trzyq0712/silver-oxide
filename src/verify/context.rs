use std::collections::HashMap;

use egg::{EGraph, Id};

use crate::{
    verify::{
        analysis::ConstFold,
        heap::{Chunk, Heap},
        lang::{FuncId, LocId, Symbolic},
        mono::Allocator,
        rewrite,
    },
    vmir::{BinOp, Bound, FunctionCall, Literal, MemberId, Polarity, Type},
};
use lasso::Rodeo;

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
    /// Result heap-delta chunks as `(addr, perm, value)` e-classes — the
    /// **merged** (accounting) view, chunks keyed by congruent address with
    /// perms summed. Used by inhale/exhale grafting (`graft_certificate`).
    pub(crate) delta: Vec<(Id, Id, Id)>,
    /// **Unmerged, program-ordered** footprint: one `(addr, perm, value)` per
    /// syntactic `acc`, in body order. Aliased accs (same address) stay
    /// separate, so the snapshot keeps one member per acc; `value` is the merged
    /// chunk value at that address, so aliased slots share it. Used by
    /// fold/unfold (the snapshot layout).
    pub(crate) footprint: Vec<(Id, Id, Id)>,
    /// Result boolean e-class.
    pub(crate) bool_id: Id,
    /// `old(...)` reads: `(addr, value)` e-classes (in cert id-space) of each
    /// `Deref` against the ctx slot `HeapVal::Temp(0)`. At a graft site the
    /// caller binds `value` to its concrete pre-state heap value at `addr`, so a
    /// postcondition like `r == old(x.f)` connects to the real pre-value. Empty
    /// for self-framed resources.
    pub(crate) old_reads: Vec<(Id, Id)>,
}

pub(crate) struct VerifyContext<'a> {
    pub(crate) egraph: egg::EGraph<Symbolic, ConstFold>,
    /// Static structural rules. The ADT cons/proj/tag reductions are pulled from
    /// the [`Allocator`] at saturation time (it grows as instances are minted).
    static_rules: Vec<egg::Rewrite<Symbolic, ConstFold>>,
    /// Terminating structural reductions, run after heap-producing ops to
    /// normalize (collapse snapshot towers) without a full saturation.
    static_reduce: Vec<egg::Rewrite<Symbolic, ConstFold>>,
    fresh_counter: usize,
    pub(crate) interner: &'a Rodeo<MemberId>,
    /// Shared verifier id allocator (minted ADT cons/proj/tag ids + their rules).
    /// Owned by `verify::verify`, threaded `&mut` through each unit so ids stay
    /// consistent across certificate grafts.
    pub(crate) alloc: &'a mut Allocator,
    /// Type side-oracle: the irreducible type sources that the type-free
    /// e-graph nodes no longer carry. Keyed by stable node payloads (the
    /// `Fresh` counter and the `FuncApp` member id), so no union upkeep is
    /// needed — the visualization reads them directly to reconstruct types.
    pub(crate) fresh_types: HashMap<u32, Type>,
    pub(crate) func_ret_types: HashMap<FuncId, Type>,
    /// Location declarations by member id (the heap-address functions). A chunk
    /// whose address is a `Symbolic::Location(m, _)` is bounded/non-aliased per
    /// `locations[m]`.
    pub(crate) locations: HashMap<MemberId, LocationInfo>,
}

/// Verifier-side view of a `Declaration::Location`.
#[derive(Debug, Clone)]
pub(crate) struct LocationInfo {
    pub(crate) bound: Bound,
    /// Held value type `T` (the location value is `Addr<T>`).
    pub(crate) ret: Type,
    pub(crate) arity: usize,
}

impl<'a> VerifyContext<'a> {
    pub(crate) fn new(
        interner: &'a Rodeo<MemberId>,
        alloc: &'a mut Allocator,
        locations: HashMap<MemberId, LocationInfo>,
    ) -> Self {
        Self {
            egraph: egg::EGraph::default(),
            static_rules: rewrite::rules(),
            static_reduce: rewrite::reduce_rules(),
            fresh_counter: 0,
            interner,
            alloc,
            fresh_types: HashMap::new(),
            func_ret_types: HashMap::new(),
            locations,
        }
    }

    /// Add a location application `f(args)` (an address of type `Addr<ret>`),
    /// recording its result type in the side-oracle for type inference.
    pub(crate) fn add_location(&mut self, member: MemberId, args: Box<[egg::Id]>) -> egg::Id {
        // A location reuses its declaration's index as its `LocId`.
        self.add_location_id(LocId(usize::from(member)), args)
    }

    /// Add a `Location` over an already-allocated [`LocId`] (used by grafting,
    /// which carries the id verbatim).
    pub(crate) fn add_location_id(&mut self, id: LocId, args: Box<[egg::Id]>) -> egg::Id {
        self.egraph.add(Symbolic::Location(id, args))
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
        if usize::from(m) < self.interner.len() {
            self.interner.resolve(&m).to_string()
        } else {
            format!("d{}", m.0)
        }
    }

    /// Display name for an e-graph function id: a real declaration index resolves
    /// via the interner; an allocator-minted id via its name table.
    pub(crate) fn func_name(&self, f: FuncId) -> String {
        if f.0 < self.interner.len() {
            self.interner.resolve(&MemberId::from(f.0)).to_string()
        } else {
            self.alloc
                .name(f)
                .map(str::to_string)
                .unwrap_or_else(|| format!("f{}", f.0))
        }
    }

    /// Display name for an e-graph location id (always a real location decl).
    pub(crate) fn loc_name(&self, l: LocId) -> String {
        if l.0 < self.interner.len() {
            self.interner.resolve(&MemberId::from(l.0)).to_string()
        } else {
            format!("loc{}", l.0)
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
            Type::Addr(t) => format!("&{}", self.type_name(t)),
            Type::Domain(id, args) => {
                let head = self.member_name(*id);
                if args.is_empty() {
                    head
                } else {
                    let inner: Vec<String> = args.iter().map(|a| self.type_name(a)).collect();
                    format!("{head}[{}]", inner.join(", "))
                }
            }
            Type::Snap(id) => format!("{}@snap", self.member_name(*id)),
            Type::Option(t) => format!("Option[{}]", self.type_name(t)),
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
        // `Option` is a builtin parametric type; request its instance through the
        // allocator's dedicated `option_*` path (`Some` = variant 0, `None` = 1).
        let some_id = self.alloc.option_some(elem.clone());
        let none_id = self.alloc.option_none(elem.clone());
        let opt_ty = self.alloc.option_type(elem);
        let some = self.add_func_app_id(some_id, opt_ty.clone(), Box::new([value]));
        let none = self.add_func_app_id(none_id, opt_ty, Box::new([]));
        self.add(Symbolic::Ite([present, some, none]))
    }

    /// Unwrap a snapshot member: `value(opt)`, the `Some` field accessor. With
    /// `opt = Some(v)` this reduces to `v`; on an opaque member it stays
    /// uninterpreted (correct — the value was never present).
    pub(crate) fn option_unwrap(&mut self, elem: Type, opt: egg::Id) -> egg::Id {
        let value_id = self.alloc.option_value(elem.clone());
        self.add_func_app_id(value_id, elem, Box::new([opt]))
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
            .cloned()
            .collect();
        let egraph = std::mem::take(&mut self.egraph);
        let runner = egg::Runner::default().with_egraph(egraph).run(&rules);
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

    /// Add a `FuncApp`, recording its return type in the side-oracle so the
    /// viz can color the result (the node itself is type-free).
    pub(crate) fn add_func_app(
        &mut self,
        fc: &FunctionCall,
        ret_ty: Type,
        args: Box<[egg::Id]>,
    ) -> egg::Id {
        // A plain function reuses its declaration's index as its `FuncId`.
        self.add_func_app_id(FuncId(usize::from(fc.function)), ret_ty, args)
    }

    /// Add a `FuncApp` over an already-allocated [`FuncId`] (a plain function,
    /// or an ADT constructor/projection/tag id from the allocator). Also used by
    /// grafting, which carries the id verbatim.
    pub(crate) fn add_func_app_id(
        &mut self,
        id: FuncId,
        ret_ty: Type,
        args: Box<[egg::Id]>,
    ) -> egg::Id {
        self.func_ret_types.entry(id).or_insert(ret_ty);
        self.egraph.add(Symbolic::FuncApp(id, args))
    }

    /// Graft a resource certificate into this (caller) e-graph, substituting the
    /// certificate's formal params for `args`. Returns the grafted result heap
    /// delta and boolean e-class. Every merge proven in the certificate
    /// transfers for free (reconstruction is keyed by certificate e-class), so
    /// the caller never re-derives or re-saturates the resource's facts.
    pub(crate) fn graft_certificate(
        &mut self,
        cert: &ResourceCertificate,
        args: &[egg::Id],
        old_ctx: Option<&Heap>,
    ) -> (Heap, egg::Id) {
        let mut subst: HashMap<Id, Id> = HashMap::new();
        for (p, a) in cert.params.iter().zip(args) {
            subst.insert(cert.egraph.find(*p), *a);
        }
        let mut memo: HashMap<Id, Transplanted> = HashMap::new();
        let mut delta = Heap::empty();
        for &(addr, perm, value) in &cert.delta {
            let a = transplant(self, cert, addr, &subst, &mut memo);
            let p = transplant(self, cert, perm, &subst, &mut memo);
            let v = transplant(self, cert, value, &subst, &mut memo);
            delta = delta.with_chunk(a, Chunk::new(p, v));
        }
        let bool_id = transplant(self, cert, cert.bool_id, &subst, &mut memo);
        // Bind each `old(...)` read to the caller's concrete pre-state value at
        // the (transplanted) address, so the cert's symbolic pre-value unifies
        // with the real one.
        if let Some(ctx_heap) = old_ctx {
            for &(addr, value) in &cert.old_reads {
                let a = transplant(self, cert, addr, &subst, &mut memo);
                let v = transplant(self, cert, value, &subst, &mut memo);
                let a_canon = self.egraph.find(a);
                let caller_val = ctx_heap
                    .entries()
                    .find_map(|(k, c)| (self.egraph.find(k) == a_canon).then_some(c.value))
                    .unwrap_or_else(|| self.fresh_symbolic_value(Type::Int));
                self.egraph.union(v, caller_val);
            }
        }
        self.egraph.rebuild();
        (delta, bool_id)
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
        let a = transplant(self, cert, addr, subst, &mut memo);
        let p = transplant(self, cert, perm, subst, &mut memo);
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
            subst.insert(cert.egraph.find(slot.2), v);
        }
        let mut memo: HashMap<Id, Transplanted> = HashMap::new();
        let b = transplant(self, cert, cert.bool_id, &subst, &mut memo);
        self.egraph.rebuild();
        b
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
        let proven = if unsat_pc {
            true
        } else {
            let rules: Vec<_> = self
                .static_rules
                .iter()
                .chain(self.alloc.rules())
                .cloned()
                .collect();
            let runner = egg::Runner::default().with_egraph(probe).run(&rules);
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
    cert: &ResourceCertificate,
    id: Id,
    subst: &HashMap<Id, Id>,
    memo: &mut HashMap<Id, Transplanted>,
) -> Id {
    let cc = cert.egraph.find(id);
    if let Some(&a) = subst.get(&cc) {
        return a;
    }
    let cc_ty = || {
        infer_type(
            &cert.egraph,
            &cert.fresh_types,
            &cert.func_ret_types,
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

    let nodes = cert.egraph[cc].nodes.clone();
    let mut built: Vec<Id> = Vec::with_capacity(nodes.len());
    for node in &nodes {
        let b = match node {
            // A fresh value has no structure to rebuild — mint a fresh of the
            // same type. (Acyclic classes thus get NO redundant placeholder.)
            Symbolic::Fresh(_) => caller.fresh_symbolic_value(cc_ty()),
            Symbolic::Lit(l) => caller.add(Symbolic::Lit(l.clone())),
            Symbolic::Binary(op, [l, r]) => {
                let l = transplant(caller, cert, *l, subst, memo);
                let r = transplant(caller, cert, *r, subst, memo);
                caller.add(Symbolic::Binary(*op, [l, r]))
            }
            Symbolic::Ite([a, b, c]) => {
                let a = transplant(caller, cert, *a, subst, memo);
                let b = transplant(caller, cert, *b, subst, memo);
                let c = transplant(caller, cert, *c, subst, memo);
                caller.add(Symbolic::Ite([a, b, c]))
            }
            Symbolic::RealCast(x) => {
                let x = transplant(caller, cert, *x, subst, memo);
                caller.add(Symbolic::RealCast(x))
            }
            Symbolic::FuncApp(m, fargs) => {
                let fargs: Box<[Id]> = fargs
                    .iter()
                    .map(|a| transplant(caller, cert, *a, subst, memo))
                    .collect();
                let ret = cert.func_ret_types.get(m).cloned().unwrap_or(Type::Int);
                caller.add_func_app_id(*m, ret, fargs)
            }
            Symbolic::Location(m, fargs) => {
                let fargs: Box<[Id]> = fargs
                    .iter()
                    .map(|a| transplant(caller, cert, *a, subst, memo))
                    .collect();
                caller.add_location_id(*m, fargs)
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
            Symbolic::FuncApp(f, _) => func_ret_types.get(f).cloned(),
            // Address types (`Addr<T>`) are reconstructed by `heap_acc` from the
            // location declaration, not here.
            Symbolic::Location(..) => None,
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
