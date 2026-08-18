//! Axiom recipes and instance building: the pure forms an axiom or function body
//! is recorded as (`AxiomPure`/`AxiomInst`), and the machinery that materializes
//! one into the e-graph under a substitution.
//!
//! Independent of quantifiers — `forall` triggering (see `super::forall`) is one
//! consumer of `build_instance`, and function unfolding is another.


use egg::{
    EGraph, Id, SearchMatches, Searcher, Subst, Var,
};

use crate::verify::analysis::ConstFold;
use crate::verify::lang::{Discriminant, FuncId, RecipeId, Symbolic};
use crate::vmir::{BinOp, Literal, Polarity, Type, Val};

use super::*;

/// A pure step of a prepared body. Mirrors the `PureInst` subset legal in an
/// axiom, with every callee resolved to its verifier `FuncId` up front (the
/// applier has no registry access) and its type arguments ground (only ADTs are
/// generic, and their instantiations are fixed at translation).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum AxiomPure {
    Binary(BinOp, Val, Val),
    Ternary(Val, Val, Val),
    RealCast(Val),
    App {
        func: FuncId,
        type_args: Vec<Type>,
        args: Vec<Val>,
    },
}

/// One instruction of a prepared body: a value-producing pure step, an
/// assumption (stitched from a callee's `#ensures`) merged with `true`, or a
/// nested `forall` — materialized as a [`Symbolic::Forall`] node whose capture
/// children are resolved through the *enclosing* instance's temps, so an outer
/// instantiation bakes its σ into the inner quantifier and the generic rule picks
/// the new node up on the next iteration.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum AxiomInst {
    Val(AxiomPure),
    Assume(Val),
    Forall {
        recipe: RecipeId,
        caps: Vec<Val>,
    },
    /// A callee's `f%pre(args)` presence token, materialized alongside the
    /// application it accompanies (the eval walk's `declaration.rs` counterpart
    /// adds both at a value-position call). Like [`Self::Assume`] it occupies **no**
    /// temp slot: its value is never read, so temp numbering stays the inst
    /// numbering of the body it was prepared from.
    ///
    /// `guards` is the **body-internal** path condition of the call that produced
    /// the token (a `forall` body's `i > 0 ==> g(i) == ..` puts `i > 0` here), in
    /// body-temp space, outermost-first. Released as `guards ==> token` inside the
    /// enclosing gate, so instantiating the quantifier at a σ where the condition
    /// fails does not fire the callee's own axioms.
    Token {
        func: FuncId,
        args: Vec<Val>,
        guards: Vec<(Val, Polarity)>,
    },
}

/// Searcher: any e-class containing an application of the trigger function
/// (type-blind — every ground instantiation lives in one `classes_by_op`
/// bucket, as in [`UnaryAppSearcher`]). σ extraction happens in the applier,
/// which re-reads the matched e-class's nodes (an egg `Subst` cannot carry
/// types).
pub(super) struct AxiomTriggerSearcher {
    pub(super) func: FuncId,
}

impl Searcher<Symbolic, ConstFold> for AxiomTriggerSearcher {
    fn search_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        limit: usize,
    ) -> Vec<SearchMatches<'_, Symbolic>> {
        let Some(ids) = egraph.classes_for_op(&Discriminant::FuncApp(self.func)) else {
            return vec![];
        };
        let mut ms = Vec::new();
        let mut limit = limit;
        for eclass in ids {
            if limit == 0 {
                break;
            }
            if let Some(m) = self.search_eclass_with_limit(egraph, eclass, limit) {
                limit -= m.substs.len();
                ms.push(m);
            }
        }
        ms
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _limit: usize,
    ) -> Option<SearchMatches<'_, Symbolic>> {
        let hit = egraph[eclass]
            .nodes
            .iter()
            .any(|n| matches!(n, Symbolic::FuncApp(f, _, _) if *f == self.func));
        hit.then(|| SearchMatches {
            eclass,
            // One empty subst: the applier extracts σ from the e-class itself.
            substs: vec![Subst::default()],
            ast: None,
        })
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Add a prepared body (of an axiom, a quantifier, or a function definition) to
/// the e-graph, seeding the value slots with `vals_seed` (the captures ++
/// bound-variable σ for a quantifier, the arguments for a function definition;
/// empty for a closed axiom). Runs the body's `Assume`s (merging each with
/// `true`) and returns the changed e-classes together with the body's `res`
/// e-class id. The caller decides how to discharge `res` (an axiom merges it
/// with `true`; a quantifier guards it; a function unfold unions it with the
/// call e-class).
pub(crate) fn build_instance(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    insts: &[AxiomInst],
    res: &Val,
    vals_seed: &[Id],
    changed: &mut Vec<Id>,
) -> Id {
    let vals = build_instance_vals(egraph, insts, vals_seed, changed);
    resolve_val(egraph, &vals, res)
}

/// [`build_instance`], additionally releasing the truth of each temp in
/// `token_steps` — the orphan `g%pre(gargs)` tokens a resource recipe carries
/// (see [`BodyRecipe::token_steps`](crate::verify::cert::BodyRecipe::token_steps)).
/// Rebuilding a step only *adds* the token node, which makes `g` materializable;
/// merging it with `true` is what activates `g`'s own axioms, and is what lets a
/// contract-introduced function application unfold at a client.
///
/// No *outer* gate here — a resource graft has no enclosing `f%pre` truth to
/// inherit, and the call-site pc gating exists to confine a function's *facts*,
/// not a resource footprint. Each token's own **body-internal** guards do apply
/// though: a call under a condition inside the resource body must not release its
/// callee's axioms where that condition fails.
pub(crate) fn build_instance_releasing_tokens(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    insts: &[AxiomInst],
    res: &Val,
    vals_seed: &[Id],
    token_steps: &[crate::verify::cert::TokenStep],
    changed: &mut Vec<Id>,
) -> Id {
    // Most recipes propagate no callee token, and then this *is* `build_instance`.
    if token_steps.is_empty() {
        return build_instance(egraph, insts, res, vals_seed, changed);
    }
    let vals = build_instance_vals(egraph, insts, vals_seed, changed);
    for ts in token_steps {
        let tok = resolve_val(egraph, &vals, &ts.token);
        let rel = fold_guards(egraph, &vals, &ts.guards, tok);
        let true_ = egraph.add(Symbolic::Lit(Literal::Bool(true)));
        if egraph.union(rel, true_) {
            changed.push(egraph.find(rel));
        }
    }
    resolve_val(egraph, &vals, res)
}

/// Resolve a recipe-space `Val` against a built instance's temp slots.
pub(super) fn resolve_val(egraph: &mut EGraph<Symbolic, ConstFold>, vals: &[Id], v: &Val) -> Id {
    match v {
        Val::Temp(n) => vals[*n],
        Val::Literal(lit) => egraph.add(Symbolic::Lit(lit.clone())),
    }
}

/// [`build_instance`], but returning the **full** temp-slot map (seed ++ one
/// `Id` per step) so the caller can resolve several recipe values against one
/// built instance (a function definition's `res` plus its exported facts).
pub(crate) fn build_instance_vals(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    insts: &[AxiomInst],
    vals_seed: &[Id],
    changed: &mut Vec<Id>,
) -> Vec<Id> {
    build_instance_vals_impl(egraph, insts, vals_seed, changed, None)
}

/// [`build_instance_vals`] with the enclosing release gate, so a `g%pre` token
/// the body propagates is released as `token_guard ==> g%pre(gargs)` rather than
/// outright. Pass the guard the enclosing release itself sits behind: a
/// function unfold's `f%pre(fargs)` class, or a quantifier's own e-class. `None`
/// releases the propagated token unguarded (status quo).
pub(crate) fn build_instance_vals_guarded(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    insts: &[AxiomInst],
    vals_seed: &[Id],
    changed: &mut Vec<Id>,
    token_guard: Option<Id>,
) -> Vec<Id> {
    build_instance_vals_impl(egraph, insts, vals_seed, changed, token_guard)
}

/// [`build_instance_vals`] with an optional `token_guard` (see
/// [`build_instance_vals_guarded`]). `token_guard = None` releases any propagated
/// token unguarded.
pub(super) fn build_instance_vals_impl(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    insts: &[AxiomInst],
    vals_seed: &[Id],
    changed: &mut Vec<Id>,
    token_guard: Option<Id>,
) -> Vec<Id> {
    let mut vals: Vec<Id> = vals_seed.to_vec();
    fn get(egraph: &mut EGraph<Symbolic, ConstFold>, vals: &[Id], v: &Val) -> Id {
        resolve_val(egraph, vals, v)
    }
    let true_of =
        |egraph: &mut EGraph<Symbolic, ConstFold>| egraph.add(Symbolic::Lit(Literal::Bool(true)));
    for inst in insts {
        match inst {
            AxiomInst::Val(p) => {
                let id = match p {
                    AxiomPure::Binary(op, l, r) => {
                        let l = get(egraph, &vals, l);
                        let r = get(egraph, &vals, r);
                        egraph.add(Symbolic::Binary(*op, [l, r]))
                    }
                    AxiomPure::Ternary(c, t, e) => {
                        let c = get(egraph, &vals, c);
                        let t = get(egraph, &vals, t);
                        let e = get(egraph, &vals, e);
                        egraph.add(Symbolic::Ite([c, t, e]))
                    }
                    AxiomPure::RealCast(v) => {
                        let v = get(egraph, &vals, v);
                        egraph.add(Symbolic::RealCast(v))
                    }
                    AxiomPure::App {
                        func,
                        type_args,
                        args,
                    } => {
                        let tys: Box<[Type]> = type_args.iter().cloned().collect();
                        let args: Box<[Id]> = args.iter().map(|v| get(egraph, &vals, v)).collect();
                        egraph.add(Symbolic::FuncApp(*func, tys, args))
                    }
                };
                vals.push(id);
            }
            AxiomInst::Assume(v) => {
                let id = get(egraph, &vals, v);
                let t = true_of(egraph);
                if egraph.union(id, t) {
                    changed.push(egraph.find(id));
                }
            }
            AxiomInst::Forall { recipe, caps } => {
                let caps: Box<[Id]> = caps.iter().map(|v| get(egraph, &vals, v)).collect();
                let id = egraph.add(Symbolic::Forall(*recipe, caps));
                vals.push(id);
            }
            AxiomInst::Token { func, args, guards } => {
                // A nested callee's `g%pre(gargs)` (Silicon's
                // `bodyPreconditionPropagation`). Adding the node is what lets `g`
                // materialize when *this* body is unfolded; releasing its truth is
                // what lets `g`'s own axioms fire. Under `token_guard` the release
                // is `outer ==> g%pre(gargs)`, so a propagated token is never
                // truer than the release it rode in on — when the outer token is
                // absent or already true the guard is `None` and the nested token
                // becomes true outright, which is the old presence⇒release
                // behavior.
                let args: Box<[Id]> = args.iter().map(|v| get(egraph, &vals, v)).collect();
                let tok = egraph.add(Symbolic::FuncApp(*func, Box::new([]), args));
                // Body-internal guards inside the enclosing gate, matching the
                // function case's `outer ==> (b ==> g%pre(..))`.
                let guarded = fold_guards(egraph, &vals, guards, tok);
                let t = true_of(egraph);
                let rel = match token_guard {
                    Some(g) => egraph.add(Symbolic::Ite([g, guarded, t])),
                    None => guarded,
                };
                if egraph.union(rel, t) {
                    changed.push(egraph.find(rel));
                }
            }
        }
    }
    vals
}
