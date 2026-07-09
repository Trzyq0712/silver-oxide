//! Verification certificates and the e-class **transplanter**.
//!
//! A certificate is a resource's or function's verified body, captured once and
//! re-attached ("grafted") at each call site by [`transplant`], which copies a
//! source e-class and everything it reaches into a destination e-graph under a
//! formal-param → actual-arg substitution.
//!
//! NOTE (Phase 4, planned): transplanting copies *every merge* inside a
//! reachable e-class, not just the term structure — see the plan's Finding
//! B/C. Both certificate kinds are slated to become add-only *term recipes*
//! rebuilt with `build_instance`, at which point this module's transplanter is
//! deleted.

use std::collections::HashMap;

use egg::{EGraph, Id};

use crate::verify::analysis::ConstFold;
use crate::verify::heap::LocationKind;
use crate::verify::lang::{FuncId, Symbolic};
use crate::verify::rewrite::AxiomInst;
use crate::verify::types::infer_type;
use crate::vmir::{Type, Val};

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

/// A (non-recursive) function's verified body as a **pure term recipe** — the
/// definition `f(params) == <steps>[res]`, add-only. Unlike a certificate this
/// imports **no e-classes**: the function unfold rule rebuilds `steps` at each
/// call site with [`build_instance`](crate::verify::rewrite::build_instance)
/// (params → args), so precondition-derived merges from the body's verification
/// never ride along (Finding B). `steps` is in dense recipe-temp space (params at
/// `Val::Temp(0..n_params)`, one slot per step); `res` is the result Val.
#[derive(Clone)]
pub(crate) struct FunctionDefinition {
    pub(crate) n_params: usize,
    pub(crate) steps: Vec<AxiomInst>,
    pub(crate) res: Val,
}

impl ResourceCertificate {
    pub(crate) fn src(&self) -> TransplantSrc<'_> {
        TransplantSrc {
            egraph: &self.egraph,
            fresh_types: &self.fresh_types,
            func_ret_types: &self.func_ret_types,
        }
    }
}

/// The read-only slice of a [`ResourceCertificate`] that [`transplant`] copies
/// from: the source e-graph and its type side-oracles. (Functions no longer
/// transplant — they carry a [`FunctionDefinition`] recipe instead.)
pub(crate) struct TransplantSrc<'a> {
    egraph: &'a EGraph<Symbolic, ConstFold>,
    fresh_types: &'a HashMap<u32, Type>,
    func_ret_types: &'a HashMap<FuncId, Type>,
}

/// Per-e-class transplant state: `InProgress` while its nodes are being rebuilt
/// (carrying a lazily-minted back-edge placeholder iff a cycle is hit), then
/// `Done` with the resulting caller e-class.
pub(crate) enum Transplanted {
    InProgress(Option<Id>),
    Done(Id),
}

/// The destination-side side-oracles [`transplant`] updates as it mints fresh
/// values and copies `FuncApp` nodes — mirrors [`TransplantSrc`] but for the
/// write side. `None` (passed by the saturation-time function-unfold applier,
/// which has no `VerifyContext` access) means freshly-minted ids simply don't
/// get a recorded display type; `infer_type`'s existing best-effort fallback
/// (`unwrap_or(Type::Int)`) absorbs the gap. A `Symbolic::FuncApp` enode itself
/// carries no return-type field, so this is purely a display/`infer_type`
/// side-table, never a correctness concern.
pub(crate) struct TransplantSink<'a> {
    pub(crate) fresh_types: &'a mut HashMap<u32, Type>,
    pub(crate) func_ret_types: &'a mut HashMap<FuncId, Type>,
}

/// Mint a fresh placeholder value shared-counter-side (see
/// [`VerifyContext::fresh_counter`](crate::verify::context::VerifyContext)'s doc
/// comment for why this must be a single monotonic counter across the whole
/// unit, including any rewrite applier that transplants during saturation).
fn mint_fresh(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    fresh_counter: &std::sync::Arc<std::sync::Mutex<u32>>,
    sink: &mut Option<&mut TransplantSink<'_>>,
    ty: Type,
) -> Id {
    let id = {
        let mut c = fresh_counter.lock().unwrap();
        let v = *c;
        *c += 1;
        v
    };
    if let Some(sink) = sink {
        sink.fresh_types.insert(id, ty);
    }
    egraph.add(Symbolic::Fresh(id))
}

/// Copy a certificate e-class (and everything it reaches) into `egraph`,
/// substituting formal params per `subst`, memoized by certificate e-class.
/// Two-phase per e-class (reserve a placeholder, then union every rebuilt node
/// into it) so cycles terminate and **all merges in the e-class collapse to one
/// caller e-class** — that is how proven equalities transfer for free.
pub(crate) fn transplant(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    fresh_counter: &std::sync::Arc<std::sync::Mutex<u32>>,
    sink: &mut Option<&mut TransplantSink<'_>>,
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
            let ph = mint_fresh(egraph, fresh_counter, sink, cc_ty());
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
            Symbolic::Fresh(_) => mint_fresh(egraph, fresh_counter, sink, cc_ty()),
            Symbolic::Lit(l) => egraph.add(Symbolic::Lit(l.clone())),
            Symbolic::Binary(op, [l, r]) => {
                let l = transplant(egraph, fresh_counter, sink, src, *l, subst, memo);
                let r = transplant(egraph, fresh_counter, sink, src, *r, subst, memo);
                egraph.add(Symbolic::Binary(*op, [l, r]))
            }
            Symbolic::Ite([a, b, c]) => {
                let a = transplant(egraph, fresh_counter, sink, src, *a, subst, memo);
                let b = transplant(egraph, fresh_counter, sink, src, *b, subst, memo);
                let c = transplant(egraph, fresh_counter, sink, src, *c, subst, memo);
                egraph.add(Symbolic::Ite([a, b, c]))
            }
            Symbolic::RealCast(x) => {
                let x = transplant(egraph, fresh_counter, sink, src, *x, subst, memo);
                egraph.add(Symbolic::RealCast(x))
            }
            Symbolic::FuncApp(m, tys, fargs) => {
                let fargs: Box<[Id]> = fargs
                    .iter()
                    .map(|a| transplant(egraph, fresh_counter, sink, src, *a, subst, memo))
                    .collect();
                // The ground type instantiation has no e-class — copy it verbatim.
                let node = egraph.add(Symbolic::FuncApp(*m, tys.clone(), fargs));
                if let Some(sink) = sink {
                    let ret = src.func_ret_types.get(m).cloned().unwrap_or(Type::Int);
                    sink.func_ret_types.entry(*m).or_insert(ret);
                }
                node
            }
        };
        built.push(b);
    }

    // egg classes always have ≥1 node; unify all rebuilt nodes (and the back-edge
    // placeholder, if a cycle minted one) into a single representative.
    let rep = built[0];
    for &b in &built[1..] {
        egraph.union(rep, b);
    }
    if let Some(Transplanted::InProgress(Some(ph))) = memo.get(&cc) {
        let ph = *ph;
        egraph.union(rep, ph);
    }
    let rep = egraph.find(rep);
    memo.insert(cc, Transplanted::Done(rep));
    rep
}
