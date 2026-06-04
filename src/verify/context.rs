use std::collections::HashMap;

use egg::{EGraph, Id};

use crate::{
    verify::{
        analysis::ConstFold,
        heap::{Chunk, Heap},
        lang::Symbolic,
        rewrite,
    },
    vmir::{BinOp, FunctionCall, Literal, MemberId, Polarity, Type},
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
    pub(crate) func_ret_types: HashMap<MemberId, Type>,
    /// Formal-param e-classes, in order (the call's args substitute these).
    pub(crate) params: Vec<Id>,
    /// Result heap-delta chunks as `(addr, perm, value)` e-classes.
    pub(crate) delta: Vec<(Id, Id, Id)>,
    /// Result boolean e-class.
    pub(crate) bool_id: Id,
}

pub(crate) struct VerifyContext<'a> {
    pub(crate) egraph: egg::EGraph<Symbolic, ConstFold>,
    rules: Vec<egg::Rewrite<Symbolic, ConstFold>>,
    fresh_counter: usize,
    pub(crate) interner: &'a Rodeo<MemberId>,
    /// Type side-oracle: the irreducible type sources that the type-free
    /// e-graph nodes no longer carry. Keyed by stable node payloads (the
    /// `Fresh` counter and the `FuncApp` member id), so no union upkeep is
    /// needed — the visualization reads them directly to reconstruct types.
    pub(crate) fresh_types: HashMap<u32, Type>,
    pub(crate) func_ret_types: HashMap<MemberId, Type>,
}

impl<'a> VerifyContext<'a> {
    pub(crate) fn new(interner: &'a Rodeo<MemberId>) -> Self {
        Self {
            egraph: egg::EGraph::default(),
            rules: rewrite::rules(),
            fresh_counter: 0,
            interner,
            fresh_types: HashMap::new(),
            func_ret_types: HashMap::new(),
        }
    }

    /// Run rewrite saturation over the e-graph in place.
    pub(crate) fn saturate(&mut self) {
        let egraph = std::mem::take(&mut self.egraph);
        let runner = egg::Runner::default().with_egraph(egraph).run(&self.rules);
        self.egraph = runner.egraph;
    }

    pub(crate) fn add(&mut self, node: Symbolic) -> egg::Id {
        self.egraph.add(node)
    }

    /// Add a `FuncApp`, recording its return type in the side-oracle so the
    /// viz can color the result (the node itself is type-free).
    pub(crate) fn add_func_app(&mut self, fc: &FunctionCall, ret_ty: Type, args: Box<[egg::Id]>) -> egg::Id {
        self.add_func_app_id(fc.function, ret_ty, args)
    }

    /// As [`Self::add_func_app`] but from a bare member id (used by grafting).
    pub(crate) fn add_func_app_id(
        &mut self,
        member: MemberId,
        ret_ty: Type,
        args: Box<[egg::Id]>,
    ) -> egg::Id {
        self.func_ret_types.entry(member).or_insert(ret_ty);
        self.egraph.add(Symbolic::FuncApp(member, args))
    }

    /// Graft a resource certificate into this (caller) e-graph, substituting the
    /// certificate's formal params for `args`. Returns the grafted result heap
    /// delta and boolean e-class. Every merge proven in the certificate
    /// transfers for free (reconstruction is keyed by certificate e-class), so
    /// the caller never re-derives or re-saturates the resource's facts.
    pub(crate) fn graft_certificate(&mut self, cert: &ResourceCertificate, args: &[egg::Id]) -> (Heap, egg::Id) {
        let mut subst: HashMap<Id, Id> = HashMap::new();
        for (p, a) in cert.params.iter().zip(args) {
            subst.insert(cert.egraph.find(*p), *a);
        }
        let mut memo: HashMap<Id, Id> = HashMap::new();
        let mut delta = Heap::empty();
        for &(addr, perm, value) in &cert.delta {
            let a = transplant(self, cert, addr, &subst, &mut memo);
            let p = transplant(self, cert, perm, &subst, &mut memo);
            let v = transplant(self, cert, value, &subst, &mut memo);
            delta = delta.with_chunk(a, Chunk::new(p, v));
        }
        let bool_id = transplant(self, cert, cert.bool_id, &subst, &mut memo);
        self.egraph.rebuild();
        (delta, bool_id)
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
        let true_ = self.add(Symbolic::Lit(Literal::Bool(true)));
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
    pub(crate) fn prove_under_pc(
        &mut self,
        goal: egg::Id,
        pc_lits: &[(egg::Id, Polarity)],
    ) -> bool {
        let mut probe = self.egraph.clone();
        let true_ = probe.add(Symbolic::Lit(Literal::Bool(true)));
        let false_ = probe.add(Symbolic::Lit(Literal::Bool(false)));

        let mut proven = false;
        let mut unsat_pc = false;
        for (id, pol) in pc_lits {
            let want_true = matches!(pol, Polarity::Positive);
            match &probe[*id].data.value {
                Some(Literal::Bool(b)) if *b != want_true => {
                    // PC literal contradicts its required polarity → off-path.
                    unsat_pc = true;
                    break;
                }
                _ => {
                    probe.union(*id, if want_true { true_ } else { false_ });
                }
            }
        }

        if unsat_pc {
            proven = true;
        } else {
            let runner = egg::Runner::default()
                .with_egraph(probe)
                .run(&self.rules);
            let probe = runner.egraph;
            if probe.find(goal) == probe.find(true_) {
                proven = true;
            }
        }

        if proven {
            let imp = self.implication(goal, pc_lits.iter().rev().copied());
            let true_live = self.add(Symbolic::Lit(Literal::Bool(true)));
            self.egraph.union(imp, true_live);
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
fn transplant(
    caller: &mut VerifyContext<'_>,
    cert: &ResourceCertificate,
    id: Id,
    subst: &HashMap<Id, Id>,
    memo: &mut HashMap<Id, Id>,
) -> Id {
    let cc = cert.egraph.find(id);
    if let Some(&a) = subst.get(&cc) {
        return a;
    }
    if let Some(&a) = memo.get(&cc) {
        return a;
    }
    // Reserve a typed placeholder up front (handles cyclic references).
    let ty = infer_type(
        &cert.egraph,
        &cert.fresh_types,
        &cert.func_ret_types,
        cc,
        &mut HashMap::new(),
    )
    .unwrap_or(Type::Int);
    let placeholder = caller.fresh_symbolic_value(ty);
    memo.insert(cc, placeholder);

    let nodes = cert.egraph[cc].nodes.clone();
    for node in &nodes {
        let built = match node {
            // The placeholder already stands in for a fresh value.
            Symbolic::Fresh(_) => continue,
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
        };
        caller.egraph.union(placeholder, built);
    }
    placeholder
}

/// Reconstruct an e-class's type from the type-free e-graph (memoized,
/// cycle-safe, best-effort): `Lit`→literal type, `RealCast`→Real,
/// `Binary`→`Bool` for comparisons else operand type, `Ite`→branch type, and
/// the irreducible `Fresh`/`FuncApp` sources from the supplied side-oracle maps.
/// Shared by grafting and the visualization.
pub(crate) fn infer_type(
    egraph: &EGraph<Symbolic, ConstFold>,
    fresh_types: &HashMap<u32, Type>,
    func_ret_types: &HashMap<MemberId, Type>,
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
            Symbolic::FuncApp(m, _) => func_ret_types.get(m).cloned(),
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
