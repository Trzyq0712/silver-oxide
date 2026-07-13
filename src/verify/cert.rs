//! Verified-body **definitions**: a function's or resource's body captured once
//! as an add-only **term recipe** and rebuilt at each call site with
//! [`build_instance`](crate::verify::rewrite::build_instance) (formal params →
//! actual args). Unlike the earlier e-graph certificates these import **no
//! e-classes**, so a merge proven during the body's own verification (e.g. a
//! precondition equality) never rides along into a caller — the caller re-derives
//! whatever it needs itself. See the plan's Findings B/C.

use egg::{EGraph, Id};

use crate::verify::analysis::ConstFold;
use crate::verify::heap::LocationKind;
use crate::verify::lang::Symbolic;
use crate::verify::rewrite::AxiomInst;
use crate::vmir::{Polarity, Type, Val};
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
    /// The body's result value — `None` for an **abstract** function, whose
    /// synthesized definition carries only `facts` (its guarded post axiom)
    /// and installs no definitional union.
    pub(crate) res: Option<Val>,
    /// The function's limited-twin id `f'`, `Some` iff the function is
    /// (mutually) recursive. When set, its unfold rule additionally frames
    /// `f(x) == f'(x)` at every full occurrence, and the recipe's own in-SCC
    /// recursive calls already target `f'` (uninterpreted) so unfolding halts
    /// after one level. `None` for a non-recursive function (unchanged behavior).
    pub(crate) limited: Option<crate::verify::lang::FuncId>,
    /// Guarded facts this function's verification established, replayed at
    /// every occurrence of `f(args)` (Silicon's `bodyProp`/`post` axioms).
    /// Derived from the body's `Assert` insts — each was *proven* under
    /// `pre ∧ pc`, so replaying it guarded is unconditionally sound. Empty for
    /// a heap-dependent function (its pre-token encoding is deferred).
    pub(crate) facts: Vec<Fact>,
}

/// One exported fact of a [`FunctionDefinition`]: `guards ⟹ cond`, both over
/// the definition's recipe-temp space. `guards` is outermost-first — the
/// pre-token (the function's own `f#requires(params)` application) first, then
/// the originating assert's path condition — and is folded innermost-first at
/// replay, matching `VerifyContext::implication`.
#[derive(Clone)]
pub(crate) struct Fact {
    pub(crate) guards: Vec<(Val, Polarity)>,
    pub(crate) cond: Val,
    /// The exit-post fact (`f#requires(params) ⟹ f#ensures(params, f(params))`,
    /// with `f'` for a recursive function). Additionally replayed at
    /// limited-twin occurrences (Silicon triggers `post` on `f'`), which is
    /// what makes induction over a recursive call work; body-derived facts must
    /// NOT be — replaying them on `f'` would re-mention `f'` at smaller args,
    /// an unbounded matching loop.
    pub(crate) post: bool,
}

/// One seed slot of a [`BodyRecipe`]: resolved at graft time to an actual arg or
/// an earlier footprint slot's (caller-supplied) value.
#[derive(Clone, Debug)]
pub(crate) enum SeedRef {
    Param(usize),
    /// The value of footprint slot `i` — supplied at graft time (fresh on inhale,
    /// read from the heap on fold/exhale, projected from a snapshot on
    /// unfold/from_snap). A value-dependent inner address (`list(this.next)`)
    /// references an earlier slot's value this way.
    SlotValue(usize),
}

/// A self-contained pure recipe rebuilt at a call site with
/// [`build_instance`](crate::verify::rewrite::build_instance). Its `steps` live
/// in dense recipe-temp space: `Val::Temp(0..seed_refs.len())` are the seed
/// (resolved per `seed_refs`), then one temp per step. `res` is the output Val.
#[derive(Clone)]
pub(crate) struct BodyRecipe {
    pub(crate) seed_refs: Vec<SeedRef>,
    pub(crate) steps: Vec<AxiomInst>,
    pub(crate) res: Val,
}

impl BodyRecipe {
    /// Rebuild this recipe in `egraph`, resolving each seed slot via `resolve`.
    /// Add-only (imports no e-classes). `changed` accumulates altered classes.
    pub(crate) fn build(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        resolve: impl Fn(&SeedRef) -> Id,
        changed: &mut Vec<Id>,
    ) -> Id {
        let seed: Vec<Id> = self.seed_refs.iter().map(resolve).collect();
        crate::verify::rewrite::build_instance(egraph, &self.steps, &self.res, &seed, changed)
    }
}

/// One footprint slot of a [`ResourceDefinition`]: its location kind and element
/// type, plus recipes for its address and permission (over the params and any
/// earlier slot values — see [`SeedRef`]).
#[derive(Clone)]
pub(crate) struct SlotRecipe {
    pub(crate) kind: LocationKind,
    pub(crate) elem: Type,
    pub(crate) addr: BodyRecipe,
    pub(crate) perm: BodyRecipe,
}

/// A resource's verified body as a **pure term recipe**. Each call site rebuilds
/// the footprint addresses, permissions, and body boolean from these recipes
/// (params → args, slot values supplied by the caller), importing no e-classes;
/// the caller re-derives any merge it needs via its own
/// `heap_union`/`assume_location_axioms` (Finding C).
#[derive(Clone)]
pub(crate) struct ResourceDefinition {
    pub(crate) footprint: Vec<SlotRecipe>,
    /// The body boolean over the params and every footprint slot value.
    pub(crate) bool: BodyRecipe,
}
