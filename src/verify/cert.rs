//! Verified-body **definitions**: a function's or resource's body captured once
//! as an add-only **term recipe** and rebuilt at each call site with
//! [`build_instance`](crate::verify::rewrite::build_instance) (formal params →
//! actual args). Unlike the earlier e-graph certificates these import **no
//! e-classes**, so a merge proven during the body's own verification (e.g. a
//! precondition equality) never rides along into a caller — the caller re-derives
//! whatever it needs itself. See the plan's Findings B/C.

use egg::{EGraph, Id};

use crate::verify::analysis::ConstFold;
use crate::verify::error::VerifyError;
use crate::verify::heap::LocationKind;
use crate::verify::lang::{FuncId, Symbolic};
use crate::verify::rewrite::{AxiomInst, AxiomPure};
use crate::vmir::{MemberId, Polarity, Type, Val};
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

    /// [`Self::build`], but every `wildcard` leaf is replaced by `wildcard_repl`
    /// (a positive constant) rather than a fresh wildcard. Used to build a
    /// wildcard footprint slot's **presence** indicator without polluting the
    /// persistent graph — see [`build_instance_subst`](crate::verify::rewrite::build_instance_subst).
    pub(crate) fn build_wildcard_as(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        resolve: impl Fn(&SeedRef) -> Id,
        changed: &mut Vec<Id>,
        wildcard_repl: Id,
    ) -> Id {
        let seed: Vec<Id> = self.seed_refs.iter().map(resolve).collect();
        crate::verify::rewrite::build_instance_subst(
            egraph,
            &self.steps,
            &self.res,
            &seed,
            changed,
            wildcard_repl,
        )
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

/// One step of a [`RecipeBuilder`] stream: either a **seed** (a footprint
/// slot's value placeholder, resolved at graft time — resources only) or an
/// ordinary pure step. Temps are dense over the combined stream, so a seed can
/// be introduced mid-body without renumbering.
enum RecipeStep {
    Seed(SeedRef),
    Inst(AxiomInst),
}

/// Post-fact metadata of a function under verification: how to recognize and
/// re-shape the exit `assert f#ensures(..)` into the exported `post` fact
/// `ens(params, f(params))` (with the limited twin `f'` when recursive).
pub(crate) struct PostMeta {
    /// The `#ensures` contract function's member (spotted via `callee_of`).
    pub(crate) ensures_member: MemberId,
    /// Its verifier `FuncId`.
    pub(crate) ensures_func: FuncId,
    /// This function's own id in the fact — the limited twin for a recursive
    /// function (Silicon triggers `post` on `f'`), the full id otherwise.
    pub(crate) self_func: FuncId,
    /// The ensures link's argument shape (`Val` in body-temp space, or the
    /// function's own result).
    pub(crate) args: Vec<crate::vmir::ContractArg>,
}

/// The recipe under construction during a function's or resource's **single**
/// eval walk: pure steps are mirrored into this stream as the body is
/// evaluated, so the certificate falls out of verification itself (no second
/// purify walk to keep in arm-parity). Recipe-temp space: `Temp(0..n_params)`
/// are the params (identity), then one temp per step.
pub(crate) struct RecipeBuilder {
    n_params: usize,
    steps: Vec<RecipeStep>,
    /// Guarded facts exported so far (`Assert`s and nested pre-tokens).
    pub(crate) facts: Vec<Fact>,
    /// Body-temp index of each `FunctionCall` → callee (post-assert detection).
    callee_of: std::collections::HashMap<usize, MemberId>,
    /// This function's pre-token application (`f#requires(params)` /
    /// `R#pre(params, s)`), args over the params (recipe identity). `None` for
    /// a function without a precondition (facts unguarded) and for resources.
    guard_app: Option<(FuncId, Vec<Val>)>,
    /// The memoized pre-token step, emitted on first use.
    pre_guard: Option<Val>,
    /// In-SCC callees (a recursion cycle's members), lowered to their limited
    /// twin so a downstream unfold halts after one level.
    recursive_scc: Option<std::collections::HashSet<MemberId>>,
    /// Exit-post shaping — functions with an ensures link only.
    pub(crate) post_meta: Option<PostMeta>,
    /// Footprint slots recorded by a resource body's `acc`s, in body order:
    /// the slot's location kind, element type, and the recipe temps of its
    /// address and permission (sliced into standalone [`SlotRecipe`]s at the
    /// end of the walk).
    pub(crate) pending_slots: Vec<(LocationKind, Type, Val, Val)>,
    /// This recipe is a **spec** body — a contract function (`#requires` /
    /// `#ensures`), i.e. a lowered pre/postcondition. Its nested function calls
    /// are spec-position occurrences (Silicon's limited symbol), so they emit **no**
    /// precondition-propagation token: when this body is unfolded at a client the
    /// callees stay dormant, discharged by congruence rather than by unfolding.
    /// A regular function body (value position) sets this `false` and propagates.
    spec: bool,
}

impl RecipeBuilder {
    pub(crate) fn new(
        n_params: usize,
        guard_app: Option<(FuncId, Vec<Val>)>,
        recursive_scc: Option<std::collections::HashSet<MemberId>>,
        post_meta: Option<PostMeta>,
    ) -> Self {
        Self {
            n_params,
            steps: Vec::new(),
            facts: Vec::new(),
            callee_of: std::collections::HashMap::new(),
            guard_app,
            pre_guard: None,
            recursive_scc,
            post_meta,
            pending_slots: Vec::new(),
            spec: false,
        }
    }

    /// Mark this recipe as a spec (contract-function) body — suppresses
    /// precondition-propagation token emission (see [`Self::spec`]).
    pub(crate) fn mark_spec(&mut self) {
        self.spec = true;
    }

    /// Whether this is a spec (contract-function) recipe body.
    pub(crate) fn is_spec(&self) -> bool {
        self.spec
    }

    fn next_temp(&self) -> Val {
        Val::Temp(self.n_params + self.steps.len())
    }

    pub(crate) fn emit(&mut self, p: AxiomPure) -> Val {
        let v = self.next_temp();
        self.steps.push(RecipeStep::Inst(AxiomInst::Val(p)));
        v
    }

    pub(crate) fn emit_forall(
        &mut self,
        recipe: crate::verify::lang::RecipeId,
        caps: Vec<Val>,
    ) -> Val {
        let v = self.next_temp();
        self.steps
            .push(RecipeStep::Inst(AxiomInst::Forall { recipe, caps }));
        v
    }

    pub(crate) fn emit_seed(&mut self, s: SeedRef) -> Val {
        let v = self.next_temp();
        self.steps.push(RecipeStep::Seed(s));
        v
    }

    pub(crate) fn record_callee(&mut self, body_temp: usize, callee: MemberId) {
        self.callee_of.insert(body_temp, callee);
    }

    pub(crate) fn callee_at(&self, body_temp: usize) -> Option<MemberId> {
        self.callee_of.get(&body_temp).copied()
    }

    pub(crate) fn is_recursive_callee(&self, m: MemberId) -> bool {
        self.recursive_scc.as_ref().is_some_and(|s| s.contains(&m))
    }

    /// This function's pre-token as a recipe step, emitted once on first use.
    /// Its args are over the params (recipe identity), so no translation.
    pub(crate) fn guard(&mut self) -> Option<Val> {
        let (func, args) = self.guard_app.as_ref()?;
        if self.pre_guard.is_none() {
            let (func, args) = (*func, args.clone());
            self.pre_guard = Some(self.emit(AxiomPure::App {
                func,
                type_args: Vec::new(),
                args,
            }));
        }
        self.pre_guard.clone()
    }

    /// Export a guarded fact: the pre-token first (emitted on demand), then the
    /// caller-supplied (already recipe-translated) path-condition guards.
    pub(crate) fn export_fact(&mut self, pc: Vec<(Val, Polarity)>, cond: Val, post: bool) {
        let mut guards: Vec<(Val, Polarity)> = Vec::new();
        if let Some(g) = self.guard() {
            guards.push((g, Polarity::Positive));
        }
        guards.extend(pc);
        self.facts.push(Fact { guards, cond, post });
    }

    /// Whether an `Assert`ed value is the exit `assert f#ensures(..)` — a body
    /// temp holding a call to the ensures contract member.
    pub(crate) fn is_post_assert(&self, val: &Val) -> bool {
        let Some(pm) = self.post_meta.as_ref() else {
            return false;
        };
        matches!(val, Val::Temp(n) if self.callee_at(*n) == Some(pm.ensures_member))
    }

    /// Export the exit-post fact `ens(params, f(params))` (with the limited
    /// twin for a recursive function): the fact expresses the result as the
    /// application itself — not the rebuilt body — so at a recursive unroll's
    /// `f'(smaller)` occurrence the fact talks about that very node (Silicon's
    /// `post` axiom). `args` are the ensures link's arguments, already
    /// recipe-translated; `None` marks the `Result` slot.
    pub(crate) fn export_post_fact(&mut self, pc: Vec<(Val, Polarity)>, args: Vec<Option<Val>>) {
        let pm = self.post_meta.as_ref().expect("post fact needs post_meta");
        let (self_func, ens_func) = (pm.self_func, pm.ensures_func);
        let params: Vec<Val> = (0..self.n_params).map(Val::Temp).collect();
        let self_app = self.emit(AxiomPure::App {
            func: self_func,
            type_args: Vec::new(),
            args: params,
        });
        let args = args
            .into_iter()
            .map(|a| a.unwrap_or_else(|| self_app.clone()))
            .collect();
        let cond = self.emit(AxiomPure::App {
            func: ens_func,
            type_args: Vec::new(),
            args,
        });
        self.export_fact(pc, cond, true);
    }

    /// Consume the builder into a function definition's parts. A function
    /// stream contains no `Seed` steps (params are pre-seeded), so it converts
    /// 1:1 — facts index into the same shared stream, as before.
    pub(crate) fn into_function_parts(self) -> Result<(Vec<AxiomInst>, Vec<Fact>), VerifyError> {
        let steps = self
            .steps
            .into_iter()
            .map(|s| match s {
                RecipeStep::Inst(i) => Ok(i),
                RecipeStep::Seed(_) => Err(VerifyError::Unimplemented(
                    "purify: seed step in a function recipe",
                )),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok((steps, self.facts))
    }

    /// Slice the self-contained [`BodyRecipe`] computing `out` from the shared
    /// stream: backward closure over the step DAG, reached params/seeds become
    /// `seed_refs`, reached steps re-emit densely in original (topological)
    /// order. Unlike the old `RTree` flatten, shared subterms stay shared.
    pub(crate) fn slice(&self, out: &Val) -> Result<BodyRecipe, VerifyError> {
        let Val::Temp(root) = out else {
            return Ok(BodyRecipe {
                seed_refs: Vec::new(),
                steps: Vec::new(),
                res: out.clone(),
            });
        };
        let n = self.n_params + self.steps.len();
        let mut reach = vec![false; n];
        let mut stack = vec![*root];
        while let Some(i) = stack.pop() {
            if reach[i] {
                continue;
            }
            reach[i] = true;
            if i < self.n_params {
                continue;
            }
            if let RecipeStep::Inst(inst) = &self.steps[i - self.n_params] {
                for_each_operand(inst, |v| {
                    if let Val::Temp(j) = v {
                        stack.push(*j);
                    }
                });
            }
        }
        // Seeds first (ascending stream order), then reached steps.
        let mut seed_refs: Vec<SeedRef> = Vec::new();
        let mut new_val: Vec<Option<Val>> = vec![None; n];
        for i in 0..n {
            if !reach[i] {
                continue;
            }
            let seed = if i < self.n_params {
                Some(SeedRef::Param(i))
            } else if let RecipeStep::Seed(s) = &self.steps[i - self.n_params] {
                Some(s.clone())
            } else {
                None
            };
            if let Some(s) = seed {
                new_val[i] = Some(Val::Temp(seed_refs.len()));
                seed_refs.push(s);
            }
        }
        let base = seed_refs.len();
        let mut steps: Vec<AxiomInst> = Vec::new();
        for i in self.n_params..n {
            if !reach[i] {
                continue;
            }
            let RecipeStep::Inst(inst) = &self.steps[i - self.n_params] else {
                continue;
            };
            // Operands precede their use (the stream is topologically sorted),
            // so they are translated before this step's slot is assigned.
            let translated = map_operands(inst, |v| match v {
                Val::Temp(j) => new_val[*j].clone().expect("operand precedes its use"),
                Val::Literal(l) => Val::Literal(l.clone()),
            });
            new_val[i] = Some(Val::Temp(base + steps.len()));
            steps.push(translated);
        }
        let res = new_val[*root].clone().expect("root is reached");
        Ok(BodyRecipe {
            seed_refs,
            steps,
            res,
        })
    }
}

/// Visit each `Val` operand of a pure recipe step.
fn for_each_operand(inst: &AxiomInst, mut f: impl FnMut(&Val)) {
    match inst {
        AxiomInst::Val(p) => match p {
            AxiomPure::Binary(_, l, r) => {
                f(l);
                f(r);
            }
            AxiomPure::Ternary(c, t, e) => {
                f(c);
                f(t);
                f(e);
            }
            AxiomPure::RealCast(v) => f(v),
            AxiomPure::App { args, .. } => args.iter().for_each(f),
            // A fresh wildcard has no operands.
            AxiomPure::Wildcard => {}
        },
        AxiomInst::Forall { caps, .. } => caps.iter().for_each(f),
        AxiomInst::Assume(v) => f(v),
    }
}

/// Rebuild a pure recipe step with each `Val` operand translated by `tr`.
fn map_operands(inst: &AxiomInst, tr: impl Fn(&Val) -> Val) -> AxiomInst {
    match inst {
        AxiomInst::Val(p) => AxiomInst::Val(match p {
            AxiomPure::Binary(op, l, r) => AxiomPure::Binary(*op, tr(l), tr(r)),
            AxiomPure::Ternary(c, t, e) => AxiomPure::Ternary(tr(c), tr(t), tr(e)),
            AxiomPure::RealCast(v) => AxiomPure::RealCast(tr(v)),
            AxiomPure::App {
                func,
                type_args,
                args,
            } => AxiomPure::App {
                func: *func,
                type_args: type_args.clone(),
                args: args.iter().map(&tr).collect(),
            },
            AxiomPure::Wildcard => AxiomPure::Wildcard,
        }),
        AxiomInst::Forall { recipe, caps } => AxiomInst::Forall {
            recipe: *recipe,
            caps: caps.iter().map(&tr).collect(),
        },
        AxiomInst::Assume(v) => AxiomInst::Assume(tr(v)),
    }
}
