//! `ite` reduction: the fused rule that decomposes and collapses conditionals.
//!
//! One rule rather than a dozen, driven by a `classes_by_op` bucket scan instead
//! of a dozen pattern searches. It does two different kinds of inference over the
//! same node loop: **decomposition** (the class's known value constrains its
//! parts) and **reduction** (the parts' known values collapse the class).


use egg::{
    Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Searcher, Subst, Symbol, Var,
};

use crate::verify::analysis::ConstFold;
use crate::verify::lang::{Discriminant, Symbolic};
use crate::vmir::Literal;

use super::*;

/// Searcher for the fused ite rule: every e-class holding an `Ite` node, via
/// the `classes_by_op` bucket (no whole-graph scan). One empty subst per class;
/// the applier re-reads the nodes.
pub(super) struct IteBucketSearcher;

impl Searcher<Symbolic, ConstFold> for IteBucketSearcher {
    fn search_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        limit: usize,
    ) -> Vec<SearchMatches<'_, Symbolic>> {
        let Some(classes) = egraph.classes_for_op(&Discriminant::Ite) else {
            return vec![];
        };
        classes
            .take(limit)
            .map(|eclass| SearchMatches {
                eclass,
                substs: vec![Subst::default()],
                ast: None,
            })
            .collect()
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _limit: usize,
    ) -> Option<SearchMatches<'_, Symbolic>> {
        egraph[eclass]
            .nodes
            .iter()
            .any(|n| matches!(n, Symbolic::Ite(..)))
            .then(|| SearchMatches {
                eclass,
                substs: vec![Subst::default()],
                ast: None,
            })
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// The known boolean of a class, per `ConstFold`. Subsumes matching a literal
/// node (the analysis is seeded by literals), so this fires at least wherever
/// the old `true`/`false` patterns did.
pub(super) fn known_bool(egraph: &EGraph<Symbolic, ConstFold>, class: Id) -> Option<bool> {
    match egraph[class].data.known() {
        Some(Literal::Bool(b)) => Some(*b),
        _ => None,
    }
}

pub(super) struct IteReduceApplier;

/// Measurement gate for the two nested same-condition `ite` shapes
/// (`ite(c, ite(c, x, y), _)` and its mirror). Set `SILVER_OXIDE_NO_NESTED_ITE=1`
/// to drop them and cost out the nested branch-class scan.
pub(super) fn nested_ite_shapes_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SILVER_OXIDE_NO_NESTED_ITE").is_none())
}

impl Applier<Symbolic, ConstFold> for IteReduceApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Collect the unions first: node inspection needs `&egraph`.
        enum Target {
            Class(Id),
            True,
            False,
        }
        let mut unions: Vec<(Id, Target)> = Vec::new();
        let self_lit = known_bool(egraph, eclass);
        for node in &egraph[eclass].nodes {
            let Symbolic::Ite([c, t, e]) = node else {
                continue;
            };
            let (c, t, e) = (egraph.find(*c), egraph.find(*t), egraph.find(*e));
            let (t_lit, e_lit) = (known_bool(egraph, t), known_bool(egraph, e));
            // Decompositions: the *class's* proven boolean constrains the parts.
            match self_lit {
                // (a && b) proven true => a, b each true.  a && b is a ? b : false.
                Some(true) if e_lit == Some(false) => {
                    unions.push((c, Target::True));
                    unions.push((t, Target::True));
                }
                // (!x) proven true => x false.  !x is x ? false : true.
                Some(true) if t_lit == Some(false) && e_lit == Some(true) => {
                    unions.push((c, Target::False));
                }
                // (!x) proven false => x true.  Mirror of the arm above; this is
                // how Prusti spells a taken branch (`switchInt` emits
                // `if (value(t) == false) { else } else { then }`, so the arm where
                // the guard holds sits under a negation proven false).
                Some(false) if t_lit == Some(false) && e_lit == Some(true) => {
                    unions.push((c, Target::True));
                }
                // (a || b) proven false => a, b each false.  a || b is a ? true : b.
                Some(false) if t_lit == Some(true) => {
                    unions.push((c, Target::False));
                    unions.push((e, Target::False));
                }
                _ => {}
            }
            // The same decomposition at **any** pinned value, not just booleans
            // and not just literals: if the class's value is pinned to `V` and an
            // arm's is pinned to something [`Fingerprint::differs_from`] separates
            // from `V`, that arm cannot be the one taken, so the condition is
            // pinned to the other side. When *both* arms disagree with `V` the two
            // unions pin `c` to both polarities, which is exactly the
            // contradiction — `ite(c, 1, 2) ≡ 0` is refuted without ever splitting
            // on `c`, and that is how a division guard survives a branch join
            // (`d = c ? 1 : 2` then `d != 0`).
            //
            // The **constructor** half of the fingerprint is what inverts a Prusti
            // enum-snapshot tower: `p_Shape_snap`'s body is a nested ite of
            // `s_Shape_k_cons(..)` arms, and once a snapshot round-trip
            // (`make_generic_Shape` / `make_concrete_Shape`) equates the whole
            // tower with one `s_Shape_1_cons(..)`, each non-matching arm pins its
            // guard false and `ite(false, _, e) ⇒ e` exposes the next level, one
            // per saturation iteration. The bottom arm is a ground constructor, so
            // the last step pins the *matching* guard true — recovering
            // `discr == cons(1)`, which is the permission gate on the variant's
            // footprint. Identical arms (`ite(c, x, x)`) and same-constructor arms
            // pin nothing, which is right: neither says anything about `c`.
            if let Some(self_fp) = egraph[eclass].data.fingerprint() {
                let arm_differs = |arm: Id| {
                    egraph[arm]
                        .data
                        .fingerprint()
                        .is_some_and(|fp| fp.differs_from(&self_fp))
                };
                if arm_differs(t) {
                    unions.push((c, Target::False));
                }
                if arm_differs(e) {
                    unions.push((c, Target::True));
                }
            }
            match known_bool(egraph, c) {
                // ite(true, x, y) => x
                Some(true) => unions.push((eclass, Target::Class(t))),
                // ite(false, x, y) => y
                Some(false) => unions.push((eclass, Target::Class(e))),
                None => {}
            }
            // c ? x : x => x
            if t == e {
                unions.push((eclass, Target::Class(t)));
            }
            // c ? true : false => c
            if t_lit == Some(true) && e_lit == Some(false) {
                unions.push((eclass, Target::Class(c)));
            }
            // c ? c : false => c  (b && b)
            if t == c && e_lit == Some(false) {
                unions.push((eclass, Target::Class(c)));
            }
            // c ? true : c => c  (b || b)
            if t_lit == Some(true) && e == c {
                unions.push((eclass, Target::Class(c)));
            }
            // c ? c : true => true
            if t == c && e_lit == Some(true) {
                unions.push((eclass, Target::True));
            }
            // c ? false : c => false
            if t_lit == Some(false) && e == c {
                unions.push((eclass, Target::False));
            }
            // Nested same-condition ite in one branch — `c ? (c ? x : y) : e` and
            // its mirror. Every arm collapses the whole class, so the first hit
            // makes any further match redundant: stop on the first collapse and
            // skip the else-branch scan if the then-branch produced one.
            let mut collapsed = false;
            // Large branch classes (the `true` class alone reaches ~1600 nodes on
            // enum-match) almost never hold an inner ite on the same `c`, so
            // scanning them per outer-ite per iteration was 55% of runtime. Skip
            // them — the load-bearing structural-join shape keeps its branch
            // classes tiny, and skipping a rewrite is incomplete, not unsound.
            const NESTED_SCAN_BOUND: usize = 64;
            let nested = nested_ite_shapes_enabled();
            let scan_t = nested && egraph[t].nodes.len() <= NESTED_SCAN_BOUND;
            let scan_e = nested && egraph[e].nodes.len() <= NESTED_SCAN_BOUND;
            //   c ? (c ? x : y) : e
            for inner in scan_t.then(|| &egraph[t].nodes).into_iter().flatten() {
                let Symbolic::Ite([c2, x, y]) = inner else {
                    continue;
                };
                if egraph.find(*c2) != c {
                    continue;
                }
                // c ? (c ? x : y) : x => x
                if egraph.find(*x) == e {
                    unions.push((eclass, Target::Class(e)));
                    collapsed = true;
                    break;
                }
                // c ? (c ? x : y) : y => c ? x : y
                if egraph.find(*y) == e {
                    unions.push((eclass, Target::Class(t)));
                    collapsed = true;
                    break;
                }
            }
            // Nested same-condition ite in the false branch:
            //   c ? t : (c ? x : y)
            if !collapsed && scan_e {
                for inner in &egraph[e].nodes {
                    let Symbolic::Ite([c2, x, y]) = inner else {
                        continue;
                    };
                    if egraph.find(*c2) != c {
                        continue;
                    }
                    // c ? x : (c ? y : x) => x
                    if egraph.find(*y) == t {
                        unions.push((eclass, Target::Class(t)));
                        break;
                    }
                    // c ? x : (c ? x : y) => c ? x : y
                    if egraph.find(*x) == t {
                        unions.push((eclass, Target::Class(e)));
                        break;
                    }
                }
            }
        }

        let mut changed = Vec::new();
        for (source, target) in unions {
            let target = match target {
                Target::Class(id) => id,
                Target::True => egraph.add(Symbolic::Lit(Literal::Bool(true))),
                Target::False => egraph.add(Symbolic::Lit(Literal::Bool(false))),
            };
            if egraph.union(source, target) {
                changed.push(egraph.find(source));
            }
        }
        changed
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}


/// Terminating `ite` simplifications, shared by the saturation rule set and the
/// post-`fold`/`unfold` reduction set. Under an assumed branch literal these
/// reduce a gated permission `b ? p : 0` to `p` (resp. `0`).
///
/// Fused into **one** rule that scans the `Ite` op bucket once per iteration and
/// node-checks every shape: as twelve `rw!` patterns they cost ~70% of all search
/// time, since the nested two-level patterns pay a backtracking cross-product
/// over a bucket holding thousands of classes. The fused pass is linear in the
/// bucket (plus the two branch classes' nodes) and union-only.
///
/// Shapes (c ⋄ t ⋄ e over one node, plus one nested level):
/// - `ite(true, x, y) ⇒ x`, `ite(false, x, y) ⇒ y` (via `ConstFold` on `c`)
/// - `ite(c, x, x) ⇒ x`
/// - `ite(c, true, false) ⇒ c`
/// - `ite(c, c, false) ⇒ c`, `ite(c, true, c) ⇒ c`
/// - `ite(c, c, true) ⇒ true`, `ite(c, false, c) ⇒ false`
/// - `ite(c, ite(c, x, y), x) ⇒ x`, `ite(c, x, ite(c, y, x)) ⇒ x`
/// - `ite(c, ite(c, x, y), y) ⇒ ite(c, x, y)`, `ite(c, x, ite(c, x, y)) ⇒ ite(c, x, y)`
pub(super) fn terminating_ite_rules() -> Vec<Rule> {
    vec![Rewrite::new("ite-reduce", IteBucketSearcher, IteReduceApplier).expect("ite rule")]
}


















