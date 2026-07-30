use std::collections::HashMap;

use crate::vmir::display::VmirDisplay;
use crate::{
    verify::{
        cert::{FunctionDefinition, ResourceDefinition},
        context::VerifyContext,
        error::VerifyError,
        heap::{Chunk, ChunkPerm, Heap, LocationKind},
        lang::Symbolic,
        viz::Snapshotter,
    },
    vmir::{
        self, Assign, BinOp, Bound, Declaration, Function, HeapInst, HeapVal, Inst, InstKind,
        Literal, MemberId, Method, PathConds, Polarity, PureInst, Resource, Sign, Type, Val,
    },
};

struct EvalState {
    vals: Vec<egg::Id>,
    /// The VMIR `Type` of each `vals` entry, kept in lockstep. The location kind
    /// of an address operand is read straight from here (`loc_kind`) — no e-graph
    /// inference. Params seed the initial slots; every `Pure` inst pushes its type.
    val_types: Vec<Type>,
    /// Recipe provenance of each `vals` entry, kept in lockstep: the
    /// recipe-space `Val` a certificate walk associates with the body temp
    /// (`None` when no recipe is built — method bodies — or the value has no
    /// pure recipe). One counter with `vals`, so the recipe column cannot
    /// desync from the eval column.
    recipes: Vec<Option<Val>>,
    heaps: Vec<Heap>,
    /// Heap temps produced on a **provably unreachable** path (a block whose
    /// cube is refuted in the ground graph — e.g. after `bb_unreach`'s `inhale
    /// false`). The Stage-4 join merge drops such an arm outright instead of
    /// selecting a `0`-leaf against it (which would need a tier-4 exhaustiveness
    /// split). Keyed by `HeapVal::Temp` index.
    dead_heaps: std::collections::HashSet<usize>,
}

impl EvalState {
    fn new() -> Self {
        Self {
            vals: Vec::new(),
            val_types: Vec::new(),
            recipes: Vec::new(),
            heaps: Vec::new(),
            dead_heaps: std::collections::HashSet::new(),
        }
    }

    fn with_args(args: Vec<egg::Id>, arg_types: Vec<Type>) -> Self {
        debug_assert_eq!(args.len(), arg_types.len());
        // Params are the identity in recipe space.
        let recipes = (0..args.len()).map(|i| Some(Val::Temp(i))).collect();
        Self {
            vals: args,
            val_types: arg_types,
            recipes,
            heaps: Vec::new(),
            dead_heaps: std::collections::HashSet::new(),
        }
    }

    fn get_val(&self, ctx: &mut VerifyContext<'_>, val: &Val) -> egg::Id {
        match val {
            Val::Temp(n) => self.vals[*n],
            Val::Literal(lit) => ctx.add(Symbolic::Lit(lit.clone())),
        }
    }

    /// The recipe-space term of a body operand: a temp's tracked provenance
    /// (`None` if it has none), a literal as itself.
    fn recipe_of(&self, val: &Val) -> Option<Val> {
        match val {
            Val::Temp(n) => self.recipes[*n].clone(),
            Val::Literal(lit) => Some(Val::Literal(lit.clone())),
        }
    }

    /// `recipe_of` for a certificate-walk operand that must have a recipe.
    fn require_recipe(&self, val: &Val, what: &'static str) -> Result<Val, VerifyError> {
        self.recipe_of(val).ok_or(VerifyError::Unimplemented(what))
    }

    /// The path condition translated into recipe space (guards of an exported
    /// fact). Errors if a guard value has no recipe.
    fn recipe_pc(&self, pc: &PathConds) -> Result<Vec<(Val, Polarity)>, VerifyError> {
        pc.conds
            .iter()
            .map(|(v, p)| {
                self.require_recipe(v, "purify: path-condition value without a recipe")
                    .map(|r| (r, *p))
            })
            .collect()
    }

    /// The location kind of an address operand, from its tracked VMIR type. A
    /// non-`Temp` or non-`Addr`-typed operand has no kind (`None`).
    fn loc_kind(&self, val: &Val) -> Option<LocationKind> {
        match val {
            Val::Temp(n) => LocationKind::from_addr_type(&self.val_types[*n]),
            Val::Literal(_) => None,
        }
    }

    fn push_val(&mut self, id: egg::Id, ty: Type, recipe: Option<Val>) {
        self.vals.push(id);
        self.val_types.push(ty);
        self.recipes.push(recipe);
    }
    fn push_heap(&mut self, heap: Heap) {
        self.heaps.push(heap);
    }
}

/// Render a single instruction (method or resource body) for error context.
fn format_inst(
    inst: &Inst,
    decls: &typed_index_collections::TiVec<MemberId, Declaration>,
    interner: &lasso::Rodeo,
    groups: &lasso::Rodeo<lasso::Spur>,
    val_base: usize,
    heap_base: usize,
) -> String {
    VmirDisplay::new(
        (val_base, heap_base, std::slice::from_ref(inst)),
        decls,
        interner,
        groups,
    )
    .to_string()
    .trim()
    .to_string()
}

/// Heap-fetch is monomorphic — `HeapVal` carries no ctx-heap variant. The
/// caller-supplied ctx heap of a resource body lives at
/// `state.heaps[0]` by convention (mirroring how params occupy the
/// initial `vals` slots).
fn get_heap(state: &EvalState, hv: &HeapVal) -> Heap {
    match hv {
        HeapVal::Empty => Heap::empty(),
        HeapVal::Temp(n) => state.heaps[*n].clone(),
    }
}

/// Whether a heap operand was produced on a provably-unreachable path (see
/// [`EvalState::dead_heaps`]).
fn heapval_dead(state: &EvalState, hv: &HeapVal) -> bool {
    matches!(hv, HeapVal::Temp(n) if state.dead_heaps.contains(n))
}

/// Heaps to visualize for an instruction, labeled as in VMIR (`h0`, `h1`, …).
/// For a heap `combine` this is the base operand plus the result; for any other
/// instruction it is the current working heap (if any). Called after the
/// instruction has been evaluated, so the result heap sits at `heaps_before`.
fn display_heaps(state: &EvalState, kind: &InstKind, heaps_before: usize) -> Vec<(String, Heap)> {
    match kind {
        InstKind::Heap(
            HeapInst::Combine { base, .. }
            | HeapInst::Inhale { base, .. }
            | HeapInst::Exhale { base, .. },
        ) => {
            let mut res = vec![(base.to_string(), get_heap(state, base))];
            if heaps_before < state.heaps.len() {
                res.push((
                    format!("h{heaps_before}"),
                    state.heaps[heaps_before].clone(),
                ));
            }
            res
        }
        _ => state
            .heaps
            .last()
            .map(|h| (format!("h{}", state.heaps.len() - 1), h.clone()))
            .into_iter()
            .collect(),
    }
}

fn zero_real(ctx: &mut VerifyContext<'_>) -> egg::Id {
    ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())))
}

fn collect_pc_lits(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    pc: &PathConds,
) -> Vec<(egg::Id, Polarity)> {
    pc.conds
        .iter()
        .map(|(v, p)| (state.get_val(ctx, v), *p))
        .collect()
}

/// Error tag for a certificate-walk operand whose recipe is missing — cannot
/// happen for a value produced by a purifiable inst, so hitting it means an
/// unsupported source leaked into a function/resource body.
const OPERAND_RECIPE: &str = "purify: operand without a recipe";

/// Evaluate a `PureInst` into its symbolic e-class id, plus — when a
/// certificate recipe is being built (`ctx.recipe`) — the recipe-space `Val`
/// mirroring it (the single-walk replacement of the old purify pass). `pc_lits`
/// is the path condition of the owning instruction — a `Deref` consults it to
/// resolve an address that only aliases a held chunk under the branch (e.g.
/// `y.f` where `x == y` holds on this path); every other variant ignores it.
fn eval_pure_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    ty: &Type,
    pi: &PureInst,
    pc_lits: &[(egg::Id, Polarity)],
) -> Result<(egg::Id, Option<Val>), VerifyError> {
    use crate::verify::rewrite::AxiomPure;
    Ok(match pi {
        PureInst::Fresh => (ctx.fresh_symbolic_value(ty.clone()), None),
        PureInst::Binary(op, l, r) => {
            let lhs = state.get_val(ctx, l);
            let rhs = state.get_val(ctx, r);
            let id = ctx.add(Symbolic::Binary(*op, [lhs, rhs]));
            let recipe = if ctx.recipe.is_some() {
                let l = state.require_recipe(l, OPERAND_RECIPE)?;
                let r = state.require_recipe(r, OPERAND_RECIPE)?;
                let rb = ctx.recipe.as_mut().unwrap();
                Some(rb.emit(AxiomPure::Binary(*op, l, r)))
            } else {
                None
            };
            (id, recipe)
        }
        PureInst::Ternary(c, t, e) => {
            let cond = state.get_val(ctx, c);
            let then_ = state.get_val(ctx, t);
            let else_ = state.get_val(ctx, e);
            let id = ctx.add(Symbolic::Ite([cond, then_, else_]));
            let recipe = if ctx.recipe.is_some() {
                let c = state.require_recipe(c, OPERAND_RECIPE)?;
                let t = state.require_recipe(t, OPERAND_RECIPE)?;
                let e = state.require_recipe(e, OPERAND_RECIPE)?;
                let rb = ctx.recipe.as_mut().unwrap();
                Some(rb.emit(AxiomPure::Ternary(c, t, e)))
            } else {
                None
            };
            (id, recipe)
        }
        PureInst::RealCast(v) => {
            let inner = state.get_val(ctx, v);
            let id = ctx.add(Symbolic::RealCast(inner));
            let recipe = if ctx.recipe.is_some() {
                let v = state.require_recipe(v, OPERAND_RECIPE)?;
                let rb = ctx.recipe.as_mut().unwrap();
                Some(rb.emit(AxiomPure::RealCast(v)))
            } else {
                None
            };
            (id, recipe)
        }
        PureInst::Deref(hv, loc) => {
            let heap = get_heap(state, hv);
            let addr = state.get_val(ctx, loc);
            let chunk = state.loc_kind(loc).and_then(|k| {
                ctx.chunk_under_pc(heap.chunks_of(&k), addr, pc_lits)
                    .cloned()
            });
            match chunk {
                Some(c) => {
                    // The chunk's recipe provenance is the deref's pure term —
                    // per heap state, so a two-state resource reading the same
                    // address in `h0` and `h1` stays distinct.
                    let recipe = if ctx.recipe.is_some() {
                        Some(c.recipe.clone().ok_or(VerifyError::Unimplemented(
                            "purify: deref outside footprint",
                        ))?)
                    } else {
                        None
                    };
                    (c.value, recipe)
                }
                None => {
                    if ctx.recipe.is_some() {
                        return Err(VerifyError::Unimplemented(
                            "purify: deref outside footprint",
                        ));
                    }
                    (ctx.fresh_symbolic_value(ty.clone()), None)
                }
            }
        }
        PureInst::FunctionCall(fc) => {
            // A (possibly generic) Silver `function`: `type_args` are the
            // result-type vars, part of the `FuncApp` node identity (discriminant);
            // empty for a monomorphic call. Always heap-free: a heap-dependent
            // function receives its precondition snapshot as an ordinary arg.
            //
            // Just add the uninterpreted application — for abstract, heap-free,
            // and heap-dependent callees alike. A verified callee's definitional
            // equality `f(args) == body` is installed lazily by its own
            // `rewrite::function_rule` (registered into `ctx.axiom_rules` by
            // `assume_axioms` from `ctx.fn_certs`) the next time saturation runs
            // over this occurrence, not eagerly here.
            let args: Vec<egg::Id> = fc.args.iter().map(|v| state.get_val(ctx, v)).collect();
            let func_id = crate::verify::func_registry::func_id_for_member(fc.function);
            let id = ctx.add_func_app_id(
                func_id,
                fc.type_args.clone().into(),
                ty.clone(),
                args.clone().into(),
            );
            // Presence trigger (Silicon's `f%pre`, assumed only at call sites):
            // every genuine value-position call — in a method body OR a regular
            // function body (both must compute the callee's value) — mints the
            // callee's `f%pre(args)` token node, whose presence lets
            // `rewrite::function_rule` unfold the body at this occurrence. The one
            // non-value position is a **contract-function body** (a lowered
            // pre/post): its calls are handled below (no propagation), and its own
            // token is never minted by a client, so it stays dormant there.
            {
                let name = ctx.member_name(fc.function);
                let tok = ctx.alloc.fn_pre_token(fc.function, &name);
                ctx.add(Symbolic::FuncApp(tok, Box::new([]), args.into()));
            }
            let recipe = if ctx.recipe.is_some() {
                let args: Vec<Val> = fc
                    .args
                    .iter()
                    .map(|a| state.require_recipe(a, OPERAND_RECIPE))
                    .collect::<Result<_, _>>()?;
                // A recursive call (callee in this function's SCC) targets the
                // limited twin `f'` — uninterpreted, so unfolding this recipe
                // at a call site stops after one level. Every other callee
                // keeps its full id and unfolds normally.
                let recursive = ctx
                    .recipe
                    .as_ref()
                    .unwrap()
                    .is_recursive_callee(fc.function);
                let func = if recursive {
                    let name = ctx.member_name(fc.function);
                    ctx.alloc.limited(fc.function, &name)
                } else {
                    func_id
                };
                // Precondition propagation (Silicon's `bodyPreconditionPropagation`):
                // in a **value** (non-spec) body, emit the non-recursive callee's
                // `g%pre(gargs)` token as an orphan recipe step so that when *this*
                // body is unfolded (its own token present), the nested token
                // re-materializes and `g` may unfold in turn — the cascade proceeds
                // down genuine value chains. A **spec** (contract) body emits none,
                // so its callees stay dormant when it is unfolded at a client.
                let propagate = !recursive && !ctx.recipe.as_ref().unwrap().is_spec();
                let g_pre = propagate.then(|| {
                    let name = ctx.member_name(fc.function);
                    ctx.alloc.fn_pre_token(fc.function, &name)
                });
                // Record the callee under the body temp this inst will occupy,
                // to spot the exit `assert f#ensures(..)`.
                let body_temp = state.vals.len();
                let rb = ctx.recipe.as_mut().unwrap();
                rb.record_callee(body_temp, fc.function);
                let call = rb.emit(AxiomPure::App {
                    func,
                    type_args: fc.type_args.clone(),
                    args: args.clone(),
                });
                if let Some(g_pre) = g_pre {
                    rb.emit(AxiomPure::App {
                        func: g_pre,
                        type_args: Vec::new(),
                        args,
                    });
                }
                Some(call)
            } else {
                None
            };
            (id, recipe)
        }
        // A `forall` is a single e-node: the compiled body (its `RecipeId`, interned
        // program-wide) as payload, the captured terms as children. Nothing is
        // instantiated here — the one generic rule (`rewrite::forall_rule`) does that
        // at the next saturation, guarded on this node merging `true`. In a recipe
        // it is a `Forall` step: replayed at each call site, it rebuilds the
        // quantifier e-node with the caller's arguments as capture children.
        PureInst::Forall(q) => {
            let table = std::sync::Arc::clone(ctx.alloc.quant_table());
            let recipe_id = table
                .id_of(q)
                .expect("every syntactic forall is interned by FuncRegistry::new");
            let caps: Box<[egg::Id]> = q.captures.iter().map(|v| state.get_val(ctx, v)).collect();
            let id = ctx.add(Symbolic::Forall(recipe_id, caps));
            let recipe = if ctx.recipe.is_some() {
                let caps: Vec<Val> = q
                    .captures
                    .iter()
                    .map(|v| state.require_recipe(v, OPERAND_RECIPE))
                    .collect::<Result<_, _>>()?;
                let rb = ctx.recipe.as_mut().unwrap();
                Some(rb.emit_forall(recipe_id, caps))
            } else {
                None
            };
            (id, recipe)
        }
        // `Snap` needs the program + certificates; every inst walker intercepts
        // it and dispatches to `eval_snap` before reaching this function.
        PureInst::Snap { .. } => {
            unreachable!("Snap is handled by eval_snap in the inst walkers")
        }
        // perm(loc): permission amount held at `loc` in the given heap. Has no
        // pure recipe — a certificate walk rejects it.
        PureInst::Perm(hv, loc) => {
            if ctx.recipe.is_some() {
                return Err(VerifyError::Unimplemented(
                    "purify: perm in a function or resource body",
                ));
            }
            let heap = get_heap(state, hv);
            let addr = state.get_val(ctx, loc);
            let id = state
                .loc_kind(loc)
                .and_then(|k| {
                    ctx.chunk_under_pc(heap.chunks_of(&k), addr, pc_lits)
                        .map(|c| c.perm.clone())
                })
                .map(|p| p.to_id(ctx))
                .unwrap_or_else(|| zero_real(ctx));
            (id, None)
        }
        // Semantic ADT nodes. Each is a `FuncApp` over a verifier-minted **concept**
        // id (one per `(head, variant[, field])`, see `verify::mono`); the ground
        // `type_args` ride in the node's operator identity (the discriminant), so
        // distinct instantiations never merge and the cons/proj/tag reductions fire
        // per concept regardless of instantiation.
        PureInst::AdtCons {
            adt,
            type_args,
            variant,
            args,
        } => {
            let cons = ctx.alloc.cons(*adt, *variant);
            let arg_ids: Vec<egg::Id> = args.iter().map(|v| state.get_val(ctx, v)).collect();
            let id =
                ctx.add_func_app_id(cons, type_args.clone().into(), ty.clone(), arg_ids.into());
            let recipe = if ctx.recipe.is_some() {
                let args: Vec<Val> = args
                    .iter()
                    .map(|a| state.require_recipe(a, OPERAND_RECIPE))
                    .collect::<Result<_, _>>()?;
                let rb = ctx.recipe.as_mut().unwrap();
                Some(rb.emit(AxiomPure::App {
                    func: cons,
                    type_args: type_args.clone(),
                    args,
                }))
            } else {
                None
            };
            (id, recipe)
        }
        PureInst::AdtProj {
            adt,
            type_args,
            variant,
            field,
            base,
        } => {
            let proj = ctx.alloc.proj(*adt, *variant, *field);
            let base_id = state.get_val(ctx, base);
            let id = ctx.add_func_app_id(
                proj,
                type_args.clone().into(),
                ty.clone(),
                Box::new([base_id]),
            );
            let recipe = if ctx.recipe.is_some() {
                let base = state.require_recipe(base, OPERAND_RECIPE)?;
                let rb = ctx.recipe.as_mut().unwrap();
                Some(rb.emit(AxiomPure::App {
                    func: proj,
                    type_args: type_args.clone(),
                    args: vec![base],
                }))
            } else {
                None
            };
            (id, recipe)
        }
        PureInst::AdtTag {
            adt,
            type_args,
            base,
        } => {
            let tag = ctx.alloc.tag(*adt);
            let base_id = state.get_val(ctx, base);
            let id = ctx.add_func_app_id(
                tag,
                type_args.clone().into(),
                Type::Int,
                Box::new([base_id]),
            );
            let recipe = if ctx.recipe.is_some() {
                let base = state.require_recipe(base, OPERAND_RECIPE)?;
                let rb = ctx.recipe.as_mut().unwrap();
                Some(rb.emit(AxiomPure::App {
                    func: tag,
                    type_args: type_args.clone(),
                    args: vec![base],
                }))
            } else {
                None
            };
            (id, recipe)
        }
    })
}

fn heap_acc(ctx: &mut VerifyContext<'_>, loc: &Val, perm: egg::Id, state: &EvalState) -> Heap {
    let addr = state.get_val(ctx, loc);
    // The location kind (group + held value type + bound) comes straight from the
    // address operand's VMIR `Type::Addr` — no e-graph inference.
    let kind = state
        .loc_kind(loc)
        .expect("acc location must be Addr-typed");
    let value = ctx.fresh_symbolic_value(kind.value.clone());
    Heap::empty().with_chunk(&kind, Chunk::new(addr, perm, value))
}

/// Resolve a [`vmir::Perm`] to its e-class id, minting a fresh positive
/// [`Symbolic::Wildcard`] for each `Perm::Wildcard`. A concrete `Amount` is
/// exactly the value it wraps, so a non-wildcard program builds the same term as
/// before the `Perm` split.
fn eval_perm(ctx: &mut VerifyContext<'_>, state: &EvalState, perm: &vmir::Perm) -> egg::Id {
    match perm {
        vmir::Perm::Amount(v) => state.get_val(ctx, v),
        vmir::Perm::Wildcard => ctx.fresh_wildcard(),
        vmir::Perm::Ite(c, t, e) => {
            let c = state.get_val(ctx, c);
            let t = eval_perm(ctx, state, t);
            let e = eval_perm(ctx, state, e);
            ctx.add(Symbolic::Ite([c, t, e]))
        }
    }
}

/// The recipe-space term of a [`vmir::Perm`] footprint-slot permission (resource
/// certificate build). A `Wildcard` emits an [`AxiomPure::Wildcard`] step so
/// each graft mints a fresh share; `Amount`/`Ite` map to their operand recipes.
fn perm_recipe(
    rb: &mut crate::verify::cert::RecipeBuilder,
    state: &EvalState,
    perm: &vmir::Perm,
) -> Result<Val, VerifyError> {
    match perm {
        vmir::Perm::Amount(v) => state.require_recipe(v, OPERAND_RECIPE),
        vmir::Perm::Wildcard => Ok(rb.emit(crate::verify::rewrite::AxiomPure::Wildcard)),
        vmir::Perm::Ite(c, t, e) => {
            let c = state.require_recipe(c, OPERAND_RECIPE)?;
            let t = perm_recipe(rb, state, t)?;
            let e = perm_recipe(rb, state, e)?;
            Ok(rb.emit(crate::verify::rewrite::AxiomPure::Ternary(c, t, e)))
        }
    }
}

/// Merge two fractional chunks at the same address. Decouples the operational
/// value pick from the declarative agreement axiom: `perm = p0 + p1`,
/// `value = (p0 > 0) ? v0 : v1` (intentionally asymmetric), and an assumed
/// `(p0 > 0 && p1 > 0) ==> (v0 == v1)`.
///
/// The assume is emitted by unioning the (desugared) implication with `true`;
/// it is not an eager `union(v0, v1)`. When both fractions are positive,
/// saturation folds the antecedent, collapses the implication to `v0 == v1`,
/// and `eq-true-union` fuses the values — erasing the ternary's asymmetry by
/// congruence. When a fraction is zero, the antecedent is `false` and the
/// asymmetric pick selects the genuinely-held value. `BinOp` has no `>`/`&&`/
/// `==>`, so these desugar to `Lt(0, p)` and `Ite` forms.
fn merge_chunks(
    ctx: &mut VerifyContext<'_>,
    addr: egg::Id,
    p0: egg::Id,
    v0: egg::Id,
    p1: egg::Id,
    v1: egg::Id,
    pc_lits: &[(egg::Id, Polarity)],
) -> Chunk {
    let perm = ctx.add(Symbolic::Binary(BinOp::AddR, [p0, p1]));
    let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigRational::from(
        num::BigInt::from(0),
    ))));
    let p0_pos = ctx.add(Symbolic::Binary(BinOp::LtR, [zero, p0]));
    let p1_pos = ctx.add(Symbolic::Binary(BinOp::LtR, [zero, p1]));

    let value = ctx.add(Symbolic::Ite([p0_pos, v0, v1]));

    // `(PC ∧ p0 > 0 ∧ p1 > 0) ==> (v0 == v1)` as the golden-rule ITE chain.
    // Fold innermost-first: p1_pos, p0_pos, then PC literals in reverse.
    let true_ = ctx.true_();
    let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [v0, v1]));
    let antecedents = [(p1_pos, Polarity::Positive), (p0_pos, Polarity::Positive)]
        .into_iter()
        .chain(pc_lits.iter().rev().copied());
    let imp = ctx.implication(eq, antecedents);
    ctx.union(imp, true_);

    Chunk::new(addr, perm, value)
}

/// A location chunk extracted from a heap for the location axioms: its
/// permission, the location group tag, its argument e-classes, and its bound.
struct LocationChunk {
    /// Kept **structural** — a bounded location's axiom is assumed per leaf, and
    /// non-aliasing only fires for bare (`Leaf`) perms, so a join `Select` never
    /// materializes as an `ite` in the graph.
    perm: ChunkPerm,
    group: lasso::Spur,
    args: Vec<egg::Id>,
    bound: Bound,
}

/// A predicate's address type `&[name] Snap(id) @ *` — the group is the
/// predicate's interned tag (`Program.groups`), value its snapshot, unbounded.
fn pred_addr_type(program: &vmir::Program, pred_id: MemberId) -> Type {
    let group = program
        .groups
        .get(program.name(pred_id))
        .expect("predicate group tag not registered");
    Type::addr(group, Type::Snap(pred_id), Bound::Unbounded)
}

/// Extract the location chunks of `h`: for each chunk whose canonical address has
/// an `Addr{group,bound,..}` type (recovered by `infer_type`, so **computed**
/// addresses count too), record its perm, group, bound, and — for a direct
/// `@addr` application — its value-arg e-classes (used by the non-aliasing axiom).
fn location_chunks(ctx: &VerifyContext<'_>, h: &Heap) -> Vec<LocationChunk> {
    let mut out = Vec::new();
    for (kind, chunk) in h.entries() {
        // group/bound come straight from the chunk's location kind (VMIR-sourced) —
        // no inference. The value args for non-aliasing are read from the address
        // application node; absent for a computed address (no such node).
        let canon = ctx.egraph.find(chunk.addr);
        let args = ctx.egraph[canon]
            .nodes
            .iter()
            .find_map(|n| match n {
                Symbolic::FuncApp(f, _, args)
                    if matches!(ctx.func_ret_types.get(f), Some(Type::Addr { .. })) =>
                {
                    Some(args.to_vec())
                }
                _ => None,
            })
            .unwrap_or_default();
        out.push(LocationChunk {
            perm: chunk.perm.clone(),
            group: kind.group,
            bound: kind.bound.clone(),
            args,
        });
    }
    out
}

/// Emit the location axioms over `h` after a consolidation. Both are e-graph
/// facts the engine *resolves itself* (no Rust-side const-fold queries):
/// - **bound:** a `Bounded(b)` cell holds `perm ≤ b` — `union((b < perm) ?
///   false : true, true)`; a permission folding to `> b` unions `false == true`,
///   making the unit inconsistent so any goal is dischargeable.
/// - **non-aliasing:** two chunks of the *same* bounded location satisfy
///   `(permᵢ + permⱼ > b) ⟹ ¬(args equal)`, encoded as
///   `union(conj, (b < sum) ? false : conj)` where `conj = a0==b0 && a1==b1 …`.
///   When `b < sum` folds true the `ite` collapses `conj` to `false`. For arity
///   1 this is the single-`Eq` collapse (drives `a0 != a1`); for higher arity it
///   sets the whole conjunction false (the de-Morgan disjunction — the e-graph
///   won't pick a branch, SMT does later).
///
/// Unbounded locations (predicates) never participate.
fn assume_location_axioms(ctx: &mut VerifyContext<'_>, h: &Heap) {
    let chunks = location_chunks(ctx, h);
    if chunks.is_empty() {
        return;
    }
    let false_ = ctx.false_();
    let true_ = ctx.true_();

    // Bound: perm ≤ b at each bounded location — assumed **per leaf** of the
    // (possibly branch-structured) perm, so a join `Select` never materializes.
    // A literal leaf (`1/1`, `0`) folds the axiom to a tautology (no node kept).
    for c in &chunks {
        let Bound::Bounded(b) = &c.bound else {
            continue;
        };
        let b = ctx.add(Symbolic::Lit(Literal::Real(b.clone())));
        let mut leaves = Vec::new();
        c.perm.for_each_leaf(&mut |l| leaves.push(l));
        for leaf in leaves {
            let gt = ctx.add(Symbolic::Binary(BinOp::LtR, [b, leaf]));
            let le = ctx.add(Symbolic::Ite([gt, false_, true_]));
            ctx.union(le, true_);
        }
    }

    // Non-aliasing: same bounded location, perms sum > bound ⇒ args differ. Only
    // fires for bare (`Leaf`) perms — a branch-structured perm would need the
    // sum materialized; skipping is sound (it can only lose a disequality, never
    // add one) and the merged heap holds one leaf-perm chunk per location anyway.
    for i in 0..chunks.len() {
        for j in (i + 1)..chunks.len() {
            if chunks[i].group != chunks[j].group {
                continue;
            }
            let Bound::Bounded(b) = &chunks[i].bound else {
                continue;
            };
            let (Some(pi), Some(pj)) = (chunks[i].perm.as_leaf(), chunks[j].perm.as_leaf()) else {
                continue;
            };
            let b = ctx.add(Symbolic::Lit(Literal::Real(b.clone())));
            let sum = ctx.add(Symbolic::Binary(BinOp::AddR, [pi, pj]));
            let gt = ctx.add(Symbolic::Binary(BinOp::LtR, [b, sum]));
            // Both arg orders (the `!=` goal's `Eq` order is source-dependent).
            for (xs, ys) in [
                (&chunks[i].args, &chunks[j].args),
                (&chunks[j].args, &chunks[i].args),
            ] {
                let conj = conj_args_eq(ctx, xs, ys, true_, false_);
                let imp = ctx.add(Symbolic::Ite([gt, false_, conj]));
                ctx.union(conj, imp);
            }
        }
    }
    ctx.egraph.rebuild();
}

/// Build `xs0==ys0 && xs1==ys1 && …` as a right-nested `ite(eq, rest, false)`
/// chain (seeded `true`). For a single argument this is `ite(a==b, true, false)`,
/// which `ite-ident` collapses to `a==b`.
fn conj_args_eq(
    ctx: &mut VerifyContext<'_>,
    xs: &[egg::Id],
    ys: &[egg::Id],
    true_: egg::Id,
    false_: egg::Id,
) -> egg::Id {
    let mut acc = true_;
    for k in (0..xs.len()).rev() {
        let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [xs[k], ys[k]]));
        acc = ctx.add(Symbolic::Ite([eq, acc, false_]));
    }
    acc
}

/// The consolidating chunk lookup shared by [`heap_union`] and
/// [`heap_subtract`]: find the chunk at `addr` (canonical-address match) in
/// `kind`'s group, first re-merging any stored chunks whose addresses have
/// *become* one e-class since insertion (a union learned later — e.g. an
/// aliasing fact — splits the held permission invisibly across chunks; the
/// permission checks only ever see one chunk, so the split loses permission).
/// On a lookup miss, normalize once (`reduce`) and retry: a recipe-rebuilt
/// snapshot address spine may only meet the held chunk's class after the
/// terminating reductions collapse the snapshot towers, and the rebuild-time
/// reduce is conditional on new e-nodes (see the dead-branch note below).
///
/// Returns the (possibly consolidated) heap and the chunk found at `addr`.
///
/// `retry_on_miss` gates the normalize-and-retry: a subtract miss is an error
/// about to be reported (rare — always worth one `reduce`), while a union miss
/// is the ordinary "first chunk at this location" case, where a per-inhale
/// `reduce` is pure overhead.
fn find_chunk_consolidated(
    ctx: &mut VerifyContext<'_>,
    h: &Heap,
    kind: &LocationKind,
    addr: egg::Id,
    pc_lits: &[(egg::Id, Polarity)],
    retry_on_miss: bool,
) -> (Heap, Option<Chunk>) {
    // Address matching is ground e-class equality. Chunk canons are snapshotted up
    // front because the retry below mutates the graph, and canons from before and
    // after a `reduce` are not comparable.
    let chunks_vec: Vec<Chunk> = h.chunks_of(kind).to_vec();
    let canon = ctx.egraph.find(addr);
    let chunk_canons: Vec<egg::Id> =
        chunks_vec.iter().map(|c| ctx.egraph.find(c.addr)).collect();
    let collect_found = |canon: egg::Id, chunk_canons: &[egg::Id]| -> Vec<Chunk> {
        chunks_vec
            .iter()
            .zip(chunk_canons)
            .filter(|(_, cc)| **cc == canon)
            .map(|(c, _)| c.clone())
            .collect()
    };
    let mut found = collect_found(canon, &chunk_canons);
    // Retry-on-miss: the subtracted address may be a recipe-rebuilt snapshot spine
    // (`@addr(cons.0(f(.., Some(unwrap(proj_0(s))))))`) that only meets the held
    // chunk's address after the terminating reductions collapse the snapshot towers.
    if found.is_empty() && retry_on_miss {
        ctx.reduce();
        let canon = ctx.egraph.find(addr);
        let chunk_canons: Vec<egg::Id> =
            chunks_vec.iter().map(|c| ctx.egraph.find(c.addr)).collect();
        found = collect_found(canon, &chunk_canons);
    }
    let Some(first) = found.first().cloned() else {
        return (h.clone(), None);
    };
    if found.len() == 1 {
        return (h.clone(), Some(first));
    }
    // Several stored chunks collapsed into one address class: fold them into
    // one chunk (sound — they genuinely alias, so their fractions add and the
    // golden-rule value agreement applies) and rewrite the group.
    let mut out = h.clone();
    let mut acc = first;
    for next in &found[1..] {
        out = out.without_chunk(kind, next.addr);
        let acc_perm = acc.perm.to_id(ctx);
        let next_perm = next.perm.to_id(ctx);
        acc = merge_chunks(
            ctx, acc.addr, acc_perm, acc.value, next_perm, next.value, pc_lits,
        );
    }
    out = out.with_chunk(kind, acc.clone());
    (out, Some(acc))
}

/// Heap addition for a single location chunk of kind `kind`.
fn heap_union(
    ctx: &mut VerifyContext<'_>,
    h1: &Heap,
    kind: &LocationKind,
    chunk2: Chunk,
    pc_lits: &[(egg::Id, Polarity)],
) -> Heap {
    let (mut out, existing) = find_chunk_consolidated(ctx, h1, kind, chunk2.addr, pc_lits, false);
    if let Some(existing) = existing {
        // Replace the existing chunk in place (keep its stored address key).
        let existing_perm = existing.perm.to_id(ctx);
        let chunk2_perm = chunk2.perm.to_id(ctx);
        let merged = merge_chunks(
            ctx,
            existing.addr,
            existing_perm,
            existing.value,
            chunk2_perm,
            chunk2.value,
            pc_lits,
        );
        out = out.with_chunk(kind, merged);
    } else {
        out = out.with_chunk(kind, chunk2);
    }
    assume_location_axioms(ctx, &out);
    out
}

/// Prove a per-leaf permission predicate over a (possibly branch-structured)
/// [`ChunkPerm`] **WITHOUT materializing the `Select` into the ground graph**.
/// A `Select` pushes its condition into the pc and requires the predicate on
/// both arms; a `Leaf` discharges it under the accumulated pc. This is the CFG
/// case split done through the pc — no `ite` node, no `lt-ite`, no tier-4, and
/// (crucially) no perm-tower bloat in the live graph. The predicate is built
/// from a leaf amount id by `mk`.
fn prove_perm_leaves(
    ctx: &mut VerifyContext<'_>,
    perm: &ChunkPerm,
    pc_lits: &[(egg::Id, Polarity)],
    mk: &dyn Fn(&mut VerifyContext<'_>, egg::Id, &[(egg::Id, Polarity)]) -> bool,
) -> bool {
    match perm {
        ChunkPerm::Leaf(h) => mk(ctx, *h, pc_lits),
        ChunkPerm::Select { cond, then, els } => {
            let mut pc_t = pc_lits.to_vec();
            pc_t.push((*cond, Polarity::Positive));
            if !prove_perm_leaves(ctx, then, &pc_t, mk) {
                return false;
            }
            let mut pc_e = pc_lits.to_vec();
            pc_e.push((*cond, Polarity::Negative));
            prove_perm_leaves(ctx, els, &pc_e, mk)
        }
    }
}

/// The folded rational value of an e-class, if known — used by the per-leaf
/// fast paths to decide a comparison against a literal WITHOUT a prove_under_pc.
fn known_real(ctx: &VerifyContext<'_>, id: egg::Id) -> Option<num::BigRational> {
    match ctx.egraph[ctx.egraph.find(id)].data.known() {
        Some(Literal::Real(r)) => Some(r.clone()),
        _ => None,
    }
}

/// `held ≥ needed` over a structured `held`, per leaf (no `Select` in the graph).
fn prove_sufficient(
    ctx: &mut VerifyContext<'_>,
    held: &ChunkPerm,
    needed: egg::Id,
    pc_lits: &[(egg::Id, Polarity)],
) -> bool {
    prove_perm_leaves(ctx, held, pc_lits, &move |ctx, h, pc| {
        // Fast path: two known literals that already satisfy `h ≥ needed` need
        // no prove (the give-back `1/1 ≥ 1/1` case — the vast majority of leaves).
        // A literal that FAILS may still be a dead branch (`0 ≥ 1` on an
        // infeasible arm), so it falls through to the pc-aware prove.
        if let (Some(hr), Some(nr)) = (known_real(ctx, h), known_real(ctx, needed)) {
            if hr >= nr {
                return true;
            }
        }
        let false_ = ctx.false_();
        let true_ = ctx.true_();
        let lt = ctx.add(Symbolic::Binary(BinOp::LtR, [h, needed]));
        let goal = ctx.add(Symbolic::Ite([lt, false_, true_]));
        ctx.prove_under_pc(goal, pc)
    })
}

/// `0 < held` over a structured `held`, per leaf.
fn prove_perm_positive(
    ctx: &mut VerifyContext<'_>,
    held: &ChunkPerm,
    pc_lits: &[(egg::Id, Polarity)],
) -> bool {
    prove_perm_leaves(ctx, held, pc_lits, &|ctx, h, pc| {
        if let Some(hr) = known_real(ctx, h) {
            if hr > num::BigRational::from(num::BigInt::from(0)) {
                return true;
            }
        }
        let zero = zero_real(ctx);
        let goal = ctx.add(Symbolic::Binary(BinOp::LtR, [zero, h]));
        ctx.prove_under_pc(goal, pc)
    })
}

/// `¬(held < 1)` (full/write permission) over a structured `held`, per leaf.
fn prove_perm_write(
    ctx: &mut VerifyContext<'_>,
    held: &ChunkPerm,
    pc_lits: &[(egg::Id, Polarity)],
) -> bool {
    prove_perm_leaves(ctx, held, pc_lits, &|ctx, h, pc| {
        if let Some(hr) = known_real(ctx, h) {
            if hr >= num::BigRational::from(num::BigInt::from(1)) {
                return true;
            }
        }
        let write = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let lt = ctx.add(Symbolic::Binary(BinOp::LtR, [h, write]));
        let false_ = ctx.false_();
        let true_ = ctx.true_();
        let goal = ctx.add(Symbolic::Ite([lt, false_, true_]));
        ctx.prove_under_pc(goal, pc)
    })
}

/// `held − needed`, kept structural (leaves get `SubR`, the tree stays a
/// `Select` via the smart constructor so it never materializes as an `ite`).
fn perm_sub(ctx: &mut VerifyContext<'_>, held: &ChunkPerm, needed: egg::Id) -> ChunkPerm {
    match held {
        ChunkPerm::Leaf(h) => {
            ChunkPerm::Leaf(ctx.add(Symbolic::Binary(BinOp::SubR, [*h, needed])))
        }
        ChunkPerm::Select { cond, then, els } => {
            let t = perm_sub(ctx, then, needed);
            let e = perm_sub(ctx, els, needed);
            ChunkPerm::select(ctx, *cond, t, e)
        }
    }
}

/// Whether every leaf of `perm` const-folds to `0` (the chunk is emptied on
/// every branch, so it can be dropped). Const-fold only, no `Select` in the graph.
fn perm_all_zero(ctx: &VerifyContext<'_>, perm: &ChunkPerm) -> bool {
    match perm {
        ChunkPerm::Leaf(h) => matches!(
            ctx.egraph[ctx.egraph.find(*h)].data.known(),
            Some(Literal::Real(r)) if *r == num::BigRational::from(num::BigInt::from(0))
        ),
        ChunkPerm::Select { then, els, .. } => {
            perm_all_zero(ctx, then) && perm_all_zero(ctx, els)
        }
    }
}


/// Whether a permission term is — or, through `ite` gating or `*`/`+`/`-`
/// scaling, contains — a [`Symbolic::Wildcard`]. Selects the wildcard exhale
/// rule (require `held > 0`, assume `needed < held`) over the concrete one
/// (prove `held ≥ needed`). Bounded by a visited set; a non-wildcard perm term
/// (a literal / small gating `ite`) is walked in O(size).
pub(crate) fn contains_wildcard(ctx: &VerifyContext<'_>, id: egg::Id) -> bool {
    fn go(
        ctx: &VerifyContext<'_>,
        id: egg::Id,
        seen: &mut std::collections::HashSet<egg::Id>,
    ) -> bool {
        let id = ctx.egraph.find(id);
        if !seen.insert(id) {
            return false;
        }
        for n in &ctx.egraph[id].nodes {
            match n {
                Symbolic::Wildcard(_) => return true,
                Symbolic::Ite(ch) => {
                    if ch.iter().any(|c| go(ctx, *c, seen)) {
                        return true;
                    }
                }
                Symbolic::Binary(BinOp::MulR | BinOp::AddR | BinOp::SubR, ch) => {
                    if ch.iter().any(|c| go(ctx, *c, seen)) {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }
    go(ctx, id, &mut std::collections::HashSet::new())
}

/// Heap subtraction for a single location chunk of kind `kind`.
fn heap_subtract(
    ctx: &mut VerifyContext<'_>,
    h1: &Heap,
    kind: &LocationKind,
    chunk2: Chunk,
    pc_lits: &[(egg::Id, Polarity)],
) -> Result<Heap, VerifyError> {
    let (mut out, existing) = find_chunk_consolidated(ctx, h1, kind, chunk2.addr, pc_lits, true);
    // Guarded-merge path: a stored chunk keeps a FLAT presence guard and a
    // guard-free amount. Reconstruct the exact legacy `guard ? perm : 0`
    // obligation transiently here — once, per consume — so sufficiency/remainder
    // are proven against the gated perm (present only where the guard holds),
    // preserving legacy semantics while merges stay flat.
    let existing = existing.map(|c| {
        if !c.guard().is_empty() {
            let gated = gate_perm_by_guard(ctx, &c.perm, c.guard());
            Chunk::new_perm(c.addr, gated, c.value).with_recipe(c.recipe.clone())
        } else {
            c
        }
    });
    let chunk2_perm = chunk2.perm.to_id(ctx);
    let Some(existing) = existing else {
        // No chunk at `addr`. Subtracting a provably-zero permission (e.g. a
        // conditional footprint slot whose guard is false — a nested predicate
        // `b ==> P(..)` with `b` false) is a no-op, so it need not be held. A
        // wildcard is provably positive, so this (correctly) fails — a wildcard
        // cannot be exhaled from an empty location.
        let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        let pos = ctx.add(Symbolic::Binary(BinOp::LtR, [zero, chunk2_perm]));
        let false_ = ctx.false_();
        let true_ = ctx.true_();
        let nonpos = ctx.add(Symbolic::Ite([pos, false_, true_]));
        if ctx.prove_under_pc(nonpos, pc_lits) {
            return Ok(out);
        }
        return Err(VerifyError::InsufficientPermission);
    };

    // Wildcard exhale: instead of proving `held ≥ needed` (a wildcard has no
    // fixed value), require the location hold *some* permission (`held > 0`) and
    // **assume** the taken share is strictly smaller (`needed < held`) under the
    // pc — Silicon's constrainable-ARP rule. The `held − needed` remainder stays
    // positive, so the chunk is never emptied.
    if ctx.has_wildcard && contains_wildcard(ctx, chunk2_perm) {
        // Wildcard held/needed perms are always leaves (never a join `Select`),
        // so materializing here is a no-op id.
        let existing_perm = existing.perm.to_id(ctx);
        let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        let held_pos = ctx.add(Symbolic::Binary(BinOp::LtR, [zero, existing_perm]));
        if !ctx.prove_under_pc(held_pos, pc_lits) {
            return Err(VerifyError::InsufficientPermission);
        }
        let lt = ctx.add(Symbolic::Binary(BinOp::LtR, [chunk2_perm, existing_perm]));
        ctx.union(existing.value, chunk2.value);
        let remainder = ctx.add(Symbolic::Binary(BinOp::SubR, [existing_perm, chunk2_perm]));
        // Assume `needed < held` and, because the e-graph has no real-order
        // arithmetic to derive `held − needed > 0` from it, the remainder's
        // positivity explicitly — otherwise a later `perm > 0` framing check on
        // the leftover share (a field read after a wildcard exhale, or a nested
        // consume of the same predicate) could not discharge. Batched into one
        // rebuild.
        let rem_pos = ctx.perm_positive(remainder);
        ctx.assume_all_guarded([lt, rem_pos], pc_lits);
        out = out.with_chunk(
            kind,
            Chunk::new(existing.addr, remainder, existing.value)
                .with_recipe(existing.recipe.clone()),
        );
        return Ok(out);
    }

    // Sufficiency `held ≥ needed`, proven per-leaf over the (possibly
    // branch-structured) held perm — the `Select` never enters the graph.
    let proven = prove_sufficient(ctx, &existing.perm, chunk2_perm, pc_lits);
    if !proven {
        // Invariant 7 — consume under **pc-implied aliasing**. `acc(x.f,1/2)` and
        // `acc(y.f,1/2)` are distinct chunks on ground, but under an in-branch
        // `x == y` they are one location holding `1/1`. Sum the demanded chunk with
        // its pc-alias partners and re-prove; the debit stays guarded (below), so
        // ground never consolidates two chunks that are only conditionally equal.
        //
        // Tried only after the plain proof fails: no unaliased consume pays the probe.
        let partners = ctx.pc_alias_partners(h1.chunks_of(kind), chunk2.addr, pc_lits);
        if !partners.is_empty() {
            return heap_subtract_pc_aliased(
                ctx, h1, out, kind, &existing, chunk2, chunk2_perm, &partners, pc_lits,
            );
        }
        if crate::verify::viz::dump_perm_enabled() {
            let existing_perm = existing.perm.to_id(ctx);
            eprintln!(
                "[perm-dump] insufficient at subtract in group {:?}\n\
                 held.perm:\n{}needed.perm:\n{}",
                kind.group,
                crate::verify::viz::dump_term(ctx, existing_perm, 64),
                crate::verify::viz::dump_term(ctx, chunk2_perm, 64),
            );
        }
        return Err(VerifyError::InsufficientPermission);
    }

    ctx.union(existing.value, chunk2.value);

    // Remainder stays structural (leaves get `SubR`); never an `ite` in the graph.
    let remainder = perm_sub(ctx, &existing.perm, chunk2_perm);
    // Whether to drop the emptied chunk is a statement about the *heap*, so it has
    // to hold at the heap's scope — **unconditionally**, not under this
    // instruction's `pc`.
    //
    // The two differ because VMIR is linearized: the heap this subtract produces
    // flows on into the sibling branch, where `pc` does not hold. A guarded consume
    // (`h13 := <c> h12 - acc a (c ? 1/1 : 0/1)`, how the frontend lowers a move
    // inside an `if`) has remainder `1/1 - (c ? 1/1 : 0/1)` — zero under `c`, but a
    // full `1/1` under `!c`, where the permission was never given up. Proving
    // `remainder == 0` under `pc = <c>` and dropping the chunk loses the permission
    // for the `!c` path, which is what made the `else` arm of
    // `fn rect_new(a, b) { if a.x <= b.x { Rect{a,b} } else { Rect{b,a} } }` unable
    // to reclaim `a`.
    //
    // Const-fold, not `prove_under_pc`: this is heap hygiene, not an obligation, so
    // it must stay O(1). Asking the prover instead makes every subtract fall
    // through to the tier-3 clone and the tier-4 case split — the check is run once
    // per chunk per consume, and it dominated everything (93s vs 4s). Keeping a
    // chunk we merely *failed to prove* empty is always sound: the remainder term
    // evaluates to 0 on-path and to the retained permission off-path, and a
    // zero-permission chunk is inert (`perm > 0` gates every use). An ordinary
    // unguarded consume still folds to `1/1 - 1/1 = 0` and drops, as before.
    let empty = perm_all_zero(ctx, &remainder);
    if empty {
        out = out.without_chunk(kind, existing.addr);
    } else {
        // The value (and so its recipe provenance) is unchanged by a subtract.
        out = out.with_chunk(
            kind,
            Chunk::new_perm(existing.addr, remainder, existing.value)
                .with_recipe(existing.recipe.clone()),
        );
    }
    Ok(out)
}

/// Consume `chunk2` when sufficiency only holds because the pc makes other chunks
/// alias `chunk2.addr` (invariant 7 of the two-egraph block model).
///
/// - **Sufficiency** is proven against the *sum* over the demanded chunk and its
///   pc-alias `partners`: at any state where the pc holds they are one location, so
///   their fractions add (`1/2 + 1/2 ≥ 1/1`).
/// - **The debit is guarded and _distributed_** across the alias set, greedily:
///   each chunk gives up `min(it holds, still needed)`, gated by `pc ? take : 0`. No
///   chunk is merged — off-path the locations are genuinely distinct and nothing there
///   was given up.
///
///   Distribution (rather than parking the whole debit on the demanded chunk as a
///   guarded negative) is what makes every *later* operation correct without another
///   alias probe. Parking it leaves the partner reading `1/2` when the location
///   actually holds nothing, so `assert y.f == y.f` and even `exhale acc(y.f,1/2)`
///   would both wrongly succeed — the latter never reaching this function at all,
///   since the partner's own half satisfies the plain proof. Distributing drives every
///   member of the set to its true remainder, so the unsummed per-address view stays
///   sound and the per-chunk `≥ 0` obligation is preserved by construction.
/// - **Value agreement** is likewise assumed only under the pc: unioning the two
///   values outright would claim `x.f == y.f` on the path where `x != y`.
#[allow(clippy::too_many_arguments)]
fn heap_subtract_pc_aliased(
    ctx: &mut VerifyContext<'_>,
    h1: &Heap,
    out: Heap,
    kind: &LocationKind,
    existing: &Chunk,
    chunk2: Chunk,
    chunk2_perm: egg::Id,
    partners: &[egg::Id],
    pc_lits: &[(egg::Id, Polarity)],
) -> Result<Heap, VerifyError> {
    let mut total = existing.perm.to_id(ctx);
    for addr in partners {
        let Some(p) = h1
            .chunks_of(kind)
            .iter()
            .find(|c| ctx.egraph.find(c.addr) == ctx.egraph.find(*addr))
            .map(|c| c.perm.clone())
        else {
            continue;
        };
        let p = p.to_id(ctx);
        total = ctx.add(Symbolic::Binary(BinOp::AddR, [total, p]));
    }
    // `needed ≤ total`, i.e. `!(total < needed)`, under the pc.
    let lt = ctx.add(Symbolic::Binary(BinOp::LtR, [total, chunk2_perm]));
    let false_ = ctx.false_();
    let true_ = ctx.true_();
    let sufficient = ctx.add(Symbolic::Ite([lt, false_, true_]));
    if !ctx.prove_under_pc(sufficient, pc_lits) {
        return Err(VerifyError::InsufficientPermission);
    }
    // Golden rule, but only where the locations coincide.
    let agree = ctx.add(Symbolic::Binary(BinOp::Eq, [existing.value, chunk2.value]));
    ctx.assume_guarded(agree, pc_lits.iter().rev().copied());

    // Greedy distribution over the alias set, demanded chunk first.
    let mut out = out;
    let mut remaining = chunk2_perm;
    let set: Vec<Chunk> = std::iter::once(existing.clone())
        .chain(partners.iter().filter_map(|a| {
            h1.chunks_of(kind)
                .iter()
                .find(|c| ctx.egraph.find(c.addr) == ctx.egraph.find(*a))
                .cloned()
        }))
        .collect();
    for chunk in set {
        let hold = chunk.perm.to_id(ctx);
        // `min(hold, remaining)` — a symbolic hold needs the `ite`; concrete
        // fractions fold it away.
        let lt = ctx.add(Symbolic::Binary(BinOp::LtR, [hold, remaining]));
        let take = ctx.add(Symbolic::Ite([lt, hold, remaining]));
        let gated = ctx.gate_amount_by_pc(take, pc_lits);
        let rest = perm_sub(ctx, &chunk.perm, gated);
        remaining = ctx.add(Symbolic::Binary(BinOp::SubR, [remaining, take]));
        // Same hygiene as the plain path: drop a chunk only when the remainder is
        // *unconditionally* zero (off-path the permission was never given up).
        if perm_all_zero(ctx, &rest) {
            out = out.without_chunk(kind, chunk.addr);
        } else {
            out = out.with_chunk(
                kind,
                Chunk::new_perm(chunk.addr, rest, chunk.value)
                    .with_recipe(chunk.recipe.clone()),
            );
        }
    }
    Ok(out)
}

/// Invariant 6 of the two-egraph block model (`design/block-vmir/82-*.md`):
/// statement-level heap instructions operate at the **block-PC level only** — their
/// `inst.pc` is exactly the block cube, never a cube plus a suffix — because they
/// cannot appear as sub-expressions. Expression-embedded obligations (a function
/// precondition, a division check) are the only things allowed an extra suffix.
///
/// Checked rather than assumed, because the lowering is where it could silently
/// break, and a violation would mean a heap effect landing under a condition the
/// block model does not know about. Gated on `SILVER_OXIDE_ASSERT_BLOCK_PC` so it can
/// be run over the corpus and feature matrix in release builds (a `debug_assert`
/// would compile out of exactly the runs that exercise interesting programs).
///
/// Known violating shape: `unfolding p in e` is a Viper *expression* but is lowered to
/// a statement-level `HeapInst::Unfold`, so it can sit under an extra ternary guard.
/// Plan 82 proposes rejecting it until it becomes a scoped node.
fn assert_statement_pc_is_block_cube(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    inst: &Inst,
) {
    if !ctx.in_block() || std::env::var_os("SILVER_OXIDE_ASSERT_BLOCK_PC").is_none() {
        return;
    }
    let statement_level = matches!(
        inst.kind,
        InstKind::Heap(
            HeapInst::Inhale { .. }
                | HeapInst::Exhale { .. }
                | HeapInst::Fold { .. }
                | HeapInst::Unfold { .. }
                | HeapInst::Assign(..)
        )
    );
    if !statement_level {
        return;
    }
    let pc = collect_pc_lits(ctx, state, &inst.pc);
    assert!(
        cube_eq(ctx, &pc, ctx.current_cube()),
        "invariant 6: statement-level inst carries a pc other than the block cube \
         ({} literals vs {} in the cube) — kind {:?}",
        pc.len(),
        ctx.current_cube().len(),
        std::mem::discriminant(&inst.kind),
    );
}

/// Set-equality of two guard cubes under canonical e-classes (order-insensitive;
/// guards are small).
fn cube_eq(ctx: &VerifyContext<'_>, a: &[(egg::Id, Polarity)], b: &[(egg::Id, Polarity)]) -> bool {
    a.len() == b.len()
        && a.iter().all(|(ia, pa)| {
            let ca = ctx.egraph.find(*ia);
            b.iter()
                .any(|(ib, pb)| pa == pb && ctx.egraph.find(*ib) == ca)
        })
}

/// Append `lit` to a guard cube (idempotent under canonical e-classes).
fn cube_push(
    ctx: &VerifyContext<'_>,
    base: &[(egg::Id, Polarity)],
    lit: (egg::Id, Polarity),
) -> crate::verify::heap::HeapPc {
    let c = ctx.egraph.find(lit.0);
    if base
        .iter()
        .any(|(i, p)| *p == lit.1 && ctx.egraph.find(*i) == c)
    {
        return std::rc::Rc::from(base.to_vec());
    }
    let mut v = base.to_vec();
    v.push(lit);
    std::rc::Rc::from(v)
}

/// Structural control-flow merge of two predecessor exit heaps at a binary join
/// (`HeapInst::Merge`). The reachability edge is carried as a **flat per-chunk
/// guard cube** relative to the join heap's `pc`, never a `?:0` `Select` tower —
/// so the amount stays a guard-free `Leaf` and no `0` leaf is ever built (absence
/// is `¬guard`). Per location kind, per canonical address:
/// - **present on one arm only** ⇒ carry the chunk, flat-append the branch
///   literal to its guard (`cond+` for then, `cond−` for els). No `Select`, no
///   `0` leaf, depth stays 0. (`p_Case_j` ends as `guard=[¬c0,¬c1,cⱼ], 1/1`.)
/// - **both arms, equal guard, congruent amount** ⇒ carry with that guard; the
///   branch literal drops (give-back / shared-prefix uplift). Value phi only if
///   the values differ.
/// - **both arms, equal guard, divergent amount** ⇒ a single-level `Select` on
///   `cond` in the amount (genuine perm divergence, per-leaf prove). Guard shared.
/// - **both arms, guards differ** ⇒ genuine `(cond∧g_t)∨(¬cond∧g_e)` disjunction,
///   not a flat cube: fall back to the gated `guard?perm:0` amount encoding
///   (sound, rare — counted via `MergeTrace` to see if it ever fires).
///
/// The presence guard is reconstructed into the exact `guard?perm:0` obligation
/// **transiently at each consume site** (`gate_perm_by_guard`), so merges stay
/// flat while sufficiency/remainder keep the pre-hoist semantics. Runs only when
/// both arms are live (a dead arm is dropped at the `Merge` inst before this is
/// called), so an absent side is a genuine conditional footprint.
fn merge_heaps(ctx: &mut VerifyContext<'_>, cond: egg::Id, h_then: &Heap, h_els: &Heap) -> Heap {
    let mut out = Heap::empty();
    let mut kinds: Vec<LocationKind> = h_then.kinds().cloned().collect();
    for k in h_els.kinds() {
        if !kinds.contains(k) {
            kinds.push(k.clone());
        }
    }
    for kind in &kinds {
        let mut addrs: Vec<egg::Id> = Vec::new();
        for c in h_then.chunks_of(kind).iter().chain(h_els.chunks_of(kind)) {
            let canon = ctx.egraph.find(c.addr);
            if !addrs.iter().any(|a| ctx.egraph.find(*a) == canon) {
                addrs.push(canon);
            }
        }
        for addr in addrs {
            let ct = h_then.chunk_canon(ctx, kind, addr).cloned();
            let ce = h_els.chunk_canon(ctx, kind, addr).cloned();
            let chunk = match (ct, ce) {
                (Some(a), Some(b)) => {
                    let value = if ctx.egraph.find(a.value) == ctx.egraph.find(b.value) {
                        a.value
                    } else {
                        ctx.add(Symbolic::Ite([cond, a.value, b.value]))
                    };
                    if cube_eq(ctx, a.guard(), b.guard()) {
                        // Same presence on both arms → carry with shared guard.
                        // Amount: congruent ⇒ bare; divergent ⇒ single Select.
                        let perm = if ChunkPerm::same(ctx, &a.perm, &b.perm) {
                            a.perm.clone()
                        } else {
                            ChunkPerm::select(ctx, cond, a.perm.clone(), b.perm.clone())
                        };
                        Some(
                            Chunk::new_perm(a.addr, perm, value)
                                .with_guard(a.guard.clone())
                                .with_recipe(a.recipe.clone()),
                        )
                    } else {
                        // Guards differ: genuine disjunction. Fall back to the
                        // legacy gated encoding — `guard? p : 0` on each side under
                        // `cond` — with an empty residual guard (conditionality
                        // lives in the amount here).
                        crate::verify::heap::MergeTrace::bump_zero();
                        let pa = gate_perm_by_guard(ctx, &a.perm, a.guard());
                        let pb = gate_perm_by_guard(ctx, &b.perm, b.guard());
                        let perm = ChunkPerm::select(ctx, cond, pa, pb);
                        Some(Chunk::new_perm(a.addr, perm, value).with_recipe(a.recipe.clone()))
                    }
                }
                (Some(a), None) => {
                    let guard = cube_push(ctx, a.guard(), (cond, Polarity::Positive));
                    Some(a.with_guard(guard))
                }
                (None, Some(b)) => {
                    let guard = cube_push(ctx, b.guard(), (cond, Polarity::Negative));
                    Some(b.with_guard(guard))
                }
                (None, None) => None,
            };
            if let Some(chunk) = chunk {
                out = out.with_chunk(kind, chunk);
            }
        }
    }
    assume_location_axioms(ctx, &out);
    out
}

/// Materialize `guard ? perm : 0` for the rare guards-differ fallback. With an
/// empty guard this is `perm` unchanged (no node).
fn gate_perm_by_guard(
    ctx: &mut VerifyContext<'_>,
    perm: &ChunkPerm,
    guard: &[(egg::Id, Polarity)],
) -> ChunkPerm {
    let mut acc = perm.clone();
    for (id, pol) in guard {
        let zero = ChunkPerm::Leaf(zero_real(ctx));
        acc = match pol {
            Polarity::Positive => ChunkPerm::select(ctx, *id, acc, zero),
            Polarity::Negative => ChunkPerm::select(ctx, *id, zero, acc),
        };
    }
    acc
}

/// Evaluate a heap inst. `Sub` may fail with `InsufficientPermission`.
fn eval_heap_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    inst: &HeapInst,
    pc: &PathConds,
) -> Result<Heap, VerifyError> {
    match inst {
        // Block-IR heap join: structural per-chunk SELECT of the two predecessor
        // exit heaps. Emitted at every CFG join by the block lowering.
        HeapInst::Merge {
            cond,
            then_h,
            els_h,
        } => {
            // An unreachable predecessor arm (its cube refuted, e.g. the enum
            // `bb_unreach` after `inhale false`) is dropped outright — selecting
            // a `0`-leaf against it would need a tier-4 exhaustiveness split.
            match (heapval_dead(state, then_h), heapval_dead(state, els_h)) {
                (false, true) => return Ok(get_heap(state, then_h)),
                (true, false) => return Ok(get_heap(state, els_h)),
                _ => {}
            }
            let cond_id = state.get_val(ctx, cond);
            let h_then = get_heap(state, then_h);
            let h_els = get_heap(state, els_h);
            Ok(merge_heaps(ctx, cond_id, &h_then, &h_els))
        }
        // `base ± acc loc perm`: build the single chunk, then union (Add) or
        // subtract (Sub) it.
        HeapInst::Combine {
            base,
            sign,
            loc,
            perm,
        } => {
            let base_h = get_heap(state, base);
            let perm_id = eval_perm(ctx, state, perm);
            let chunk = heap_acc(ctx, loc, perm_id, state);
            let pc_lits: Vec<(egg::Id, Polarity)> = pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            let (kind, ch) = chunk.entries().next().unwrap();
            let (kind, mut ch) = (kind.clone(), ch.clone());
            match sign {
                Sign::Add => {
                    // A resource body's `acc` records a footprint slot in the
                    // certificate under construction: its value is the seed
                    // placeholder `SlotValue(i)` (supplied at graft time), its
                    // address/permission recipes are sliced at the end of the
                    // walk. The seed doubles as the chunk's recipe provenance,
                    // so a later `Deref` purifies to the slot value.
                    if ctx.recipe.is_some() {
                        let addr_r = state.require_recipe(loc, OPERAND_RECIPE)?;
                        let rb = ctx.recipe.as_mut().unwrap();
                        let perm_r = perm_recipe(rb, state, perm)?;
                        let elem = kind.value.clone();
                        let rb = ctx.recipe.as_mut().unwrap();
                        let i = rb.pending_slots.len();
                        let seed = rb.emit_seed(crate::verify::cert::SeedRef::SlotValue(i));
                        rb.pending_slots.push((kind.clone(), elem, addr_r, perm_r));
                        ch = ch.with_recipe(Some(seed));
                    }
                    Ok(heap_union(ctx, &base_h, &kind, ch, &pc_lits))
                }
                Sign::Sub => {
                    if ctx.recipe.is_some() {
                        return Err(VerifyError::Unimplemented(
                            "purify: unsupported heap inst in a resource body",
                        ));
                    }
                    heap_subtract(ctx, &base_h, &kind, ch, &pc_lits)
                }
            }
        }
        // Resource inhale/exhale need the program + certificates; method-only.
        HeapInst::Inhale { .. } | HeapInst::Exhale { .. } => Err(VerifyError::Unimplemented(
            "resource inhale/exhale outside method body",
        )),
        // Fold/Unfold need the program + certificates; handled in
        // `eval_method_inst`.
        HeapInst::Fold { .. } | HeapInst::Unfold { .. } => Err(VerifyError::Unimplemented(
            "fold/unfold outside method body",
        )),
        // Snapshot → heap reconstruction needs the program + certificates;
        // handled in `eval_method_inst` (function bodies are walked there).
        HeapInst::FromSnap { .. } => Err(VerifyError::Unimplemented(
            "FromSnap outside a function/method body",
        )),
        // Field assignment `loc := val`: requires write permission at `loc`,
        // then updates the chunk's value (permission unchanged).
        HeapInst::Assign(heap, Assign { loc, val }) => {
            let h = get_heap(state, heap);
            let addr = state.get_val(ctx, loc);
            let new_val = state.get_val(ctx, val);
            let kind = state
                .loc_kind(loc)
                .expect("assign location must be Addr-typed");
            let held = h.chunk(&kind, addr).cloned();
            let perm = held
                .as_ref()
                .map(|c| c.perm.clone())
                .unwrap_or_else(|| ChunkPerm::Leaf(zero_real(ctx)));
            let guard = held
                .as_ref()
                .map(|c| c.guard.clone())
                .unwrap_or_else(|| std::rc::Rc::from(Vec::new()));
            // SIDECOND: prove `not(perm < 1)` (full/write permission) under pc —
            // per leaf, so a branch-structured held perm never materializes. Under
            // the guarded-merge path the write obligation is proven against the
            // guard-gated perm (write required only where the chunk is present).
            let pc_lits: Vec<(egg::Id, Polarity)> = pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            let proof_perm = if !guard.is_empty() {
                gate_perm_by_guard(ctx, &perm, &guard)
            } else {
                perm.clone()
            };
            if !prove_perm_write(ctx, &proof_perm, &pc_lits) {
                return Err(VerifyError::InsufficientPermission);
            }
            // Permission (and its presence guard) unchanged by the write; keep it
            // structural.
            Ok(h.with_chunk(
                &kind,
                Chunk::new_perm(addr, perm, new_val).with_guard(guard),
            ))
        }
    }
}

/// Evaluate one instruction of a resource body (well-formedness pass). Resource
/// bodies emit `Pure`/`Heap`; `unfold` is the one heap op handled specially
/// (shared with method bodies), the rest go through `eval_heap_inst`. The
/// effectful variants (`Assume`/`Assert`/`Refute`) are not produced here.
fn eval_resource_body_inst(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceDefinition>,
) -> Result<(), VerifyError> {
    match &inst.kind {
        // A heap-dependent function call inside a resource body narrows the
        // body's footprint heap with `Snap` — shared with method bodies.
        InstKind::Pure(ty, PureInst::Snap { .. }) => {
            let (id, recipe) = eval_snap(ctx, program, state, inst, certs)?;
            state.push_val(id, ty.clone(), recipe);
        }
        InstKind::Pure(ty, pi) => {
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
            let (id, recipe) = eval_pure_inst(ctx, state, ty, pi, &pc_lits)?;
            state.push_val(id, ty.clone(), recipe);
        }
        // `unfold` inside a resource body verifies identically to a method
        // body (shared `eval_unfold`); only `Unfold` is emitted here.
        InstKind::Heap(HeapInst::Unfold { .. }) => eval_unfold(ctx, program, state, inst, certs)?,
        // The entry `heap_of req(args), s` of a two-state resource body:
        // reconstruct the pre-state heap from the snapshot parameter (implicitly
        // assuming the precondition resource's boolean).
        InstKind::Heap(HeapInst::FromSnap { .. }) => {
            let heap = eval_from_snap(ctx, program, state, inst, certs)?;
            state.push_heap(heap);
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, &inst.pc)?;
            state.push_heap(heap);
        }
        InstKind::Assume(_) | InstKind::Assert(_) | InstKind::Refute(_) => {
            return Err(VerifyError::Unimplemented(
                "effectful inst in resource body",
            ));
        }
    }
    Ok(())
}

fn eval_method_inst(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceDefinition>,
) -> Result<(), VerifyError> {
    match &inst.kind {
        // `Snap` needs the program + certificates (footprint graft), so it is
        // handled here rather than in `eval_pure_inst`.
        InstKind::Pure(ty, PureInst::Snap { .. }) => {
            let (id, recipe) = eval_snap(ctx, program, state, inst, certs)?;
            state.push_val(id, ty.clone(), recipe);
        }
        InstKind::Pure(ty, pi) => {
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
            let (id, recipe) = eval_pure_inst(ctx, state, ty, pi, &pc_lits)?;
            state.push_val(id, ty.clone(), recipe);
        }
        // `base inhale <resource>(args) perm`: produce the resource's footprint
        // (fresh values), scaled by `perm`, into `base` and **assume** its
        // boolean; `base exhale ...` consumes the footprint from `base` and
        // **asserts** it. A self-framed callee additionally yields the snapshot
        // of its footprint as a pure `Val` (the pre-state handle a two-state call
        // receives). Both route through `walk_footprint`.
        InstKind::Heap(
            hi @ (HeapInst::Inhale { base, call, perm } | HeapInst::Exhale { base, call, perm }),
        ) => {
            let is_inhale = matches!(hi, HeapInst::Inhale { .. });
            let base_h = get_heap(state, base);
            let args: Vec<egg::Id> = call.args.iter().map(|v| state.get_val(ctx, v)).collect();
            let scale = eval_perm(ctx, state, perm);
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
            // Inhale: produce fresh chunks, assume the bool guarded by `0 < scale`
            // (it carries no path condition — the branch lives in the perm scale).
            // Exhale: consume the held chunks, assert the bool under `pc`.
            let (source, direction, bool_guard) = if is_inhale {
                let pos = ctx.perm_positive(scale);
                let mut guard = vec![(pos, Polarity::Positive)];
                // Fork model: arms run unguarded (the branch no longer rides in
                // the perm scale), so the block cube must guard the inhaled bool
                // — otherwise a conditional `inhale` on one arm leaks its fact
                // past the branch.
                guard.extend_from_slice(&pc_lits);
                (ValueSource::Fresh, Direction::Produce, guard)
            } else {
                (
                    ValueSource::ReadHeap(base_h.clone()),
                    Direction::Consume,
                    pc_lits.clone(),
                )
            };
            let FootprintResult {
                heap: out, members, ..
            } = walk_footprint(
                ctx,
                program,
                certs,
                call.resource,
                &args,
                base_h,
                source,
                direction,
                Some(scale),
                &pc_lits,
                &bool_guard,
                false,
            )?;
            state.push_heap(out);
            if let Some(res_id) = hi.snap_yield(&program.decls) {
                let s = build_snapshot(ctx, res_id, members);
                // Inhale/exhale are method-only, so no recipe is in flight.
                state.push_val(s, Type::Snap(res_id), None);
            }
        }
        // `fold`: consume the predicate footprint (scaled by `perm`), assert the
        // body's pure facts, and produce a predicate chunk holding the snapshot
        // (`cons`) of the consumed field values.
        InstKind::Heap(HeapInst::Fold { base, call, perm }) => {
            // A function body may `fold` (via `folding … in …`); its recipe
            // shape is not implemented yet, so a certificate walk rejects it.
            if ctx.recipe.is_some() {
                return Err(VerifyError::Unimplemented(
                    "purify: fold in a function body",
                ));
            }
            let base_h = get_heap(state, base);
            let args: Vec<egg::Id> = call.args.iter().map(|v| state.get_val(ctx, v)).collect();
            let perm_id = eval_perm(ctx, state, perm);
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);

            // Consume the footprint from the current heap (reading its values),
            // asserting the predicate body; then place the predicate chunk holding
            // the snapshot of the consumed values.
            let FootprintResult {
                heap: out, members, ..
            } = walk_footprint(
                ctx,
                program,
                certs,
                call.resource,
                &args,
                base_h.clone(),
                ValueSource::ReadHeap(base_h),
                Direction::Consume,
                Some(perm_id),
                &pc_lits,
                &pc_lits,
                false,
            )?;
            let snap = build_snapshot(ctx, call.resource, members);
            let (pred_kind, pred_addr) = predicate_address(ctx, program, call.resource, &args);
            let out = heap_union(
                ctx,
                &out,
                &pred_kind,
                Chunk::new(pred_addr, perm_id, snap),
                &pc_lits,
            );
            state.push_heap(out);
            ctx.reduce();
        }
        // `unfold`: inverse of fold — consume the predicate chunk, reproduce the
        // footprint (fields recovered by projecting the snapshot), assume the
        // body's pure facts.
        InstKind::Heap(HeapInst::Unfold { .. }) => eval_unfold(ctx, program, state, inst, certs)?,
        // `heap_of R(args), s`: reconstruct a heap from a snapshot (the entry of
        // a heap-dependent function body), assuming the resource bool.
        InstKind::Heap(HeapInst::FromSnap { .. }) => {
            let heap = eval_from_snap(ctx, program, state, inst, certs)?;
            state.push_heap(heap);
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, &inst.pc)?;
            state.push_heap(heap);
        }
        InstKind::Assume(val) => {
            let id = state.get_val(ctx, val);
            // Guard by the path condition: an `assume` inside a branch holds only
            // on that branch (rev to match `implication`'s innermost-first fold).
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
            ctx.assume_guarded(id, pc_lits.iter().rev().copied());
        }
        InstKind::Assert(val) => {
            // TODO(heap-consolidation): `inst.heap` carries the heap this obligation
            // is checked in — once wired, consolidate it (materialise aliasing/
            // perm-sum facts into the e-graph) before `prove_under_pc`. Unused today.
            let id = state.get_val(ctx, val);
            let pc_lits: Vec<(egg::Id, Polarity)> = inst
                .pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            // For an opaque heap-free `#requires` token this proves the callee-cert
            // formula and releases the token (mirrors `eval_snap`); otherwise a
            // plain `prove_under_pc`.
            if !ctx.prove_under_pc(id, &pc_lits) {
                return Err(VerifyError::AssertionFailed);
            }
            // A certificate walk re-exports the assert as a guarded fact —
            // it was *proven* under `pre ∧ pc`, so replaying it guarded at
            // every occurrence of the function is unconditionally sound
            // (Silicon's `bodyProp`; the exit post assert is its `post` axiom).
            if ctx.recipe.is_some() {
                let pc_r = state.recipe_pc(&inst.pc)?;
                if ctx.recipe.as_ref().unwrap().is_post_assert(val) {
                    let pm_args = ctx
                        .recipe
                        .as_ref()
                        .unwrap()
                        .post_meta
                        .as_ref()
                        .unwrap()
                        .args
                        .clone();
                    let args: Vec<Option<Val>> = pm_args
                        .iter()
                        .map(|a| match a {
                            vmir::ContractArg::Val(v) => {
                                state.require_recipe(v, OPERAND_RECIPE).map(Some)
                            }
                            vmir::ContractArg::Result => Ok(None),
                        })
                        .collect::<Result<_, _>>()?;
                    ctx.recipe.as_mut().unwrap().export_post_fact(pc_r, args);
                } else {
                    let cond = state.require_recipe(val, OPERAND_RECIPE)?;
                    ctx.recipe.as_mut().unwrap().export_fact(pc_r, cond, false);
                }
            }
        }
        InstKind::Refute(val) => {
            // `refute A` succeeds iff `A` is NOT provable in this state.
            let id = state.get_val(ctx, val);
            let pc_lits: Vec<(egg::Id, Polarity)> = inst
                .pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            if ctx.prove_under_pc(id, &pc_lits) {
                return Err(VerifyError::RefuteFailed);
            }
        }
    }
    Ok(())
}

/// Where a footprint slot's value comes from (see [`walk_footprint`]).
enum ValueSource {
    /// Read the chunk value at the slot's address from this heap (fresh if
    /// absent). Used by `fold`/`snap`/`exhale`, which read a heap they hold.
    /// A certificate walk propagates the hit chunk's recipe provenance.
    ReadHeap(Heap),
    /// Recover it from the snapshot `s` as `unwrap(proj_i(s))`. Used by
    /// `unfold`/`from_snap`, which reconstruct the footprint from a snapshot.
    /// The second field is `s`'s recipe term (certificate walks only) — each
    /// slot's recipe mirrors the projection: `unwrap(proj_i(s_recipe))`.
    ProjectSnap(egg::Id, Option<Val>),
    /// A fresh unconstrained value per slot. Used by `inhale`, which produces a
    /// resource's footprint with unknown location values.
    Fresh,
}

/// The direction of a footprint walk: consume a held footprint and **assert** the
/// resource's boolean (`fold`/`snap`), or produce one and **assume** it
/// (`unfold`/`from_snap`).
enum Direction {
    Consume,
    Produce,
}

/// The result of a footprint walk: the accumulator heap after all slot effects,
/// the snapshot members `present ? Some(v) : None` per slot (for a `Consume`
/// walk; empty for `Produce`), and — during a certificate walk — each slot
/// value's recipe term.
struct FootprintResult {
    heap: Heap,
    members: Vec<egg::Id>,
    /// Recipe provenance of each slot value, in slot order (certificate walks
    /// only; all `None` otherwise).
    slot_recipes: Vec<Option<Val>>,
}

/// The single per-slot footprint loop behind `fold`, `unfold`, `snap` and
/// `from_snap`. For each footprint slot of `resource(args)`: graft the slot's
/// `(addr, perm)`, obtain the slot value from `source`, apply the slot's heap
/// effect to the `base` accumulator (subtract for `Consume`, union for
/// `Produce`; permission scaled by `scale` when `Some`), and thread the actual
/// value through `subst` so a value-dependent inner address (e.g. `P(this.next)`)
/// resolves. Finally graft the body boolean and discharge it per `direction`
/// (`Consume` asserts under `pc_lits`, `Produce` assumes it guarded by them).
///
/// The caller owns everything *around* the slots: the predicate-chunk add/remove
/// (bracketing differs — `fold` adds after, `unfold` removes before) and what to
/// do with `heap` (`snap` discards it — functions frame, they don't consume).
/// Whether a permission recipe mentions a `wildcard` (bare or gated) — the shape
/// of a function-precondition footprint slot. At a `Snap` such a slot needs no
/// permission *amount*: presence is the gating guard (`true` when bare) and
/// sufficiency is just "the caller holds a positive share where the slot is
/// required". Building the wildcard would leave un-collapsible `ite` residue in
/// the persistent graph that `ite-reduce` then churns on.
fn recipe_has_wildcard(perm: &crate::verify::cert::BodyRecipe) -> bool {
    use crate::verify::rewrite::{AxiomInst, AxiomPure};
    perm.steps
        .iter()
        .any(|s| matches!(s, AxiomInst::Val(AxiomPure::Wildcard)))
}

/// A footprint slot's permission as built for the current walk: either the real
/// `Amount` (drives the heap effect), or, for a wildcard slot at a `Snap`, a
/// `Presence` indicator `ite(guard, 1, 0)` standing in for the wildcard (drives
/// only the snapshot member + a "holds a positive share" sufficiency prove).
enum SlotPerm {
    Amount(egg::Id),
    Presence(egg::Id),
}

impl SlotPerm {
    fn map_id(self, f: impl FnOnce(egg::Id) -> egg::Id) -> SlotPerm {
        match self {
            SlotPerm::Amount(i) => SlotPerm::Amount(f(i)),
            SlotPerm::Presence(i) => SlotPerm::Presence(f(i)),
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_footprint(
    ctx: &mut VerifyContext<'_>,
    _program: &vmir::Program,
    certs: &HashMap<MemberId, ResourceDefinition>,
    resource: MemberId,
    args: &[egg::Id],
    base: Heap,
    source: ValueSource,
    direction: Direction,
    scale: Option<egg::Id>,
    pc_lits: &[(egg::Id, Polarity)],
    // The guard under which the body boolean is discharged (asserted for
    // `Consume`, assumed for `Produce`). Usually `pc_lits`; an `inhale` passes
    // `[0 < scale]` since it carries no path condition.
    bool_guard: &[(egg::Id, Polarity)],
    // A `Snap` (non-consuming precondition check): a bare-wildcard footprint slot
    // skips building the wildcard perm and subtracting — sufficiency becomes a
    // "holds a positive share" prove, presence is unconditional. Keeps the
    // wildcard `ite` residue (which `ite-reduce` churns on) out of the persistent
    // e-graph. `false` for the consuming/producing walks (fold/unfold/in/exhale).
    is_snap: bool,
) -> Result<FootprintResult, VerifyError> {
    use crate::verify::cert::SeedRef;
    let def = certs.get(&resource).ok_or(VerifyError::DependencyFailed)?;

    let mut heap = base;
    let mut values: Vec<egg::Id> = Vec::with_capacity(def.footprint.len());
    let mut recipes: Vec<Option<Val>> = Vec::with_capacity(def.footprint.len());
    let mut members = Vec::with_capacity(def.footprint.len());
    let mut changed = Vec::new();
    for (i, slot) in def.footprint.iter().enumerate() {
        // Rebuild the slot's address and permission from their recipes, resolving
        // params to `args` and any earlier-slot value refs to `values` (so a
        // value-dependent inner address like `list(this.next)` resolves).
        let resolve = |r: &SeedRef| -> egg::Id {
            match r {
                SeedRef::Param(k) => args[*k],
                SeedRef::SlotValue(j) => values[*j],
            }
        };
        // Heap framing is a *syntactic* e-class match (`heap_subtract`,
        // `ValueSource::ReadHeap`), so a slot address has to be in normal form
        // before we look it up. A slot address that reaches through a snapshot —
        // `Pt(f(r, cons(Some(unwrap(proj_0(s))))))`, the shape a Rust `&mut`
        // reparented under `old(..)` produces — is only e-class-equal to the held
        // chunk's address once the `proj∘cons` / `unwrap∘Some` reductions have
        // fired.
        //
        // Reduce only when the rebuild actually introduced something to reduce.
        // The recipe is add-only, so if `build` added no e-node then every term it
        // named was already present — and therefore already normalized by the
        // reduce that first introduced it. Guarding on the node count keeps repeat
        // call sites (the common case: one resource, many uses) free; reducing
        // unconditionally per slot re-runs the ADT rule set over the whole e-graph
        // every time and costs ~3.5x end to end.
        // A wildcard slot at a `Snap` (bare or gated): don't build the wildcard
        // perm (its amount is irrelevant to the snapshot and would pollute the
        // graph). Build its **presence** indicator instead — the same recipe with
        // the wildcard leaf replaced by full permission `1`, so `ite(guard, 1, 0)`
        // whose `0 < …` folds to the gating guard (`true` when unconditional).
        let wc_slot = is_snap && recipe_has_wildcard(&slot.perm);
        let before = ctx.egraph.total_number_of_nodes();
        let addr = slot.addr.build(&mut ctx.egraph, resolve, &mut changed);
        let bperm = if wc_slot {
            let one = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
            let pp = slot
                .perm
                .build_wildcard_as(&mut ctx.egraph, resolve, &mut changed, one);
            SlotPerm::Presence(pp)
        } else {
            SlotPerm::Amount(slot.perm.build(&mut ctx.egraph, resolve, &mut changed))
        };
        if ctx.egraph.total_number_of_nodes() != before {
            ctx.reduce();
        }
        let addr = ctx.egraph.find(addr);
        let bperm = bperm.map_id(|b| ctx.egraph.find(b));
        let elem = slot.elem.clone();
        let (value, recipe) = match &source {
            // Values are read from the *original* heap (aliased slots agree);
            // the hit chunk's recipe provenance rides along.
            ValueSource::ReadHeap(h) => h
                .entries()
                .find_map(|(_, c)| {
                    (ctx.egraph.find(c.addr) == ctx.egraph.find(addr))
                        .then(|| (c.value, c.recipe.clone()))
                })
                .unwrap_or_else(|| (ctx.fresh_symbolic_value(elem.clone()), None)),
            // `proj_i(s)` recovers the optional member (collapsing to the `cons`
            // argument when `s` is concrete); `unwrap` peels to the field value.
            // A certificate walk mirrors the projection into the recipe.
            ValueSource::ProjectSnap(s, s_recipe) => {
                let proj_id = ctx.alloc.proj(resource, 0, i);
                let opt_ty = ctx.alloc.option_type(elem.clone());
                let opt = ctx.add_func_app_id(proj_id, Box::new([]), opt_ty, Box::new([*s]));
                let value = ctx.option_unwrap(elem.clone(), opt);
                let recipe = match (ctx.recipe.is_some(), s_recipe) {
                    (true, Some(sr)) => {
                        use crate::verify::rewrite::AxiomPure;
                        let unwrap_id = ctx.alloc.option_value();
                        let rb = ctx.recipe.as_mut().unwrap();
                        let opt = rb.emit(AxiomPure::App {
                            func: proj_id,
                            type_args: Vec::new(),
                            args: vec![sr.clone()],
                        });
                        Some(rb.emit(AxiomPure::App {
                            func: unwrap_id,
                            type_args: vec![elem.clone()],
                            args: vec![opt],
                        }))
                    }
                    _ => None,
                };
                (value, recipe)
            }
            // Inhale: an unconstrained fresh value per slot.
            ValueSource::Fresh => (ctx.fresh_symbolic_value(elem.clone()), None),
        };
        // Snapshot member `present ? Some(v) : None`, plus the slot's heap effect.
        let present = match bperm {
            // Normal path: apply the (optionally scaled) permission to the heap
            // (subtract/union), presence is `0 < perm`.
            SlotPerm::Amount(bperm) => {
                let p = match scale {
                    Some(pm) => ctx.add(Symbolic::Binary(BinOp::MulR, [pm, bperm])),
                    None => bperm,
                };
                let chunk = Chunk::new(addr, p, value).with_recipe(recipe.clone());
                heap = match direction {
                    Direction::Consume => heap_subtract(ctx, &heap, &slot.kind, chunk, pc_lits)?,
                    Direction::Produce => heap_union(ctx, &heap, &slot.kind, chunk, pc_lits),
                };
                ctx.perm_positive(bperm)
            }
            // Wildcard `Snap` slot: no heap effect (Snap frames). Presence is the
            // gating guard `0 < ite(guard, 1, 0)` (folds to `guard`, `true` when
            // unconditional). Sufficiency: where the slot is required, the caller
            // must hold a positive share — prove `guard ⇒ 0 < held` against the
            // caller's (concrete) held permission; no wildcard is ever built.
            SlotPerm::Presence(pp) => {
                let guard = ctx.perm_positive(pp);
                let (_, existing) =
                    find_chunk_consolidated(ctx, &heap, &slot.kind, addr, pc_lits, true);
                let suff = match existing {
                    Some(c) => {
                        // `guard ⇒ 0 < held`, proven per leaf (never materialize
                        // the held `Select`): assume `guard` in the pc, prove
                        // `0 < leaf` on each branch. Guard-gate the held perm under
                        // the guarded-merge path so presence is respected.
                        let held = if !c.guard().is_empty() {
                            gate_perm_by_guard(ctx, &c.perm, c.guard())
                        } else {
                            c.perm.clone()
                        };
                        let mut pc = pc_lits.to_vec();
                        pc.push((guard, Polarity::Positive));
                        prove_perm_positive(ctx, &held, &pc)
                    }
                    // No chunk held here: sound only if the slot is not required
                    // on this path (`guard` is false).
                    None => {
                        let f = ctx.false_();
                        let t = ctx.true_();
                        let not_guard = ctx.add(Symbolic::Ite([guard, f, t]));
                        ctx.prove_under_pc(not_guard, pc_lits)
                    }
                };
                if !suff {
                    return Err(VerifyError::InsufficientPermission);
                }
                guard
            }
        };
        members.push(ctx.option_member(elem, present, value));
        values.push(value);
        recipes.push(recipe);
    }
    // The body boolean over params ++ all slot values.
    let resolve = |r: &SeedRef| -> egg::Id {
        match r {
            SeedRef::Param(k) => args[*k],
            SeedRef::SlotValue(j) => values[*j],
        }
    };
    let bool_id = def.bool.build(&mut ctx.egraph, resolve, &mut changed);
    match direction {
        // The precondition/predicate body must hold over the consumed values.
        Direction::Consume => {
            if !ctx.prove_under_pc(bool_id, bool_guard) {
                return Err(VerifyError::AssertionFailed);
            }
        }
        // The reconstructed body facts hold only where this walk is reached.
        Direction::Produce => {
            ctx.assume_guarded(bool_id, bool_guard.iter().rev().copied());
        }
    }
    Ok(FootprintResult {
        heap,
        members,
        slot_recipes: recipes,
    })
}

/// The `cons` of a resource's snapshot from its per-slot `members`
/// (`present ? Some(v) : None`). Predicate snapshots are single-variant,
/// non-generic ADTs headed by the resource id.
fn build_snapshot(
    ctx: &mut VerifyContext<'_>,
    resource: MemberId,
    members: Vec<egg::Id>,
) -> egg::Id {
    let cons = ctx.alloc.cons(resource, 0);
    ctx.add_func_app_id(cons, Box::new([]), Type::Snap(resource), members.into())
}

/// A predicate's location kind and address e-class for `args`: the address is an
/// ordinary `FuncApp` to the predicate's own id (its `@addr` function), typed by
/// its recorded `Addr{..}` return type. Shared by `fold` and `unfold`.
fn predicate_address(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    pred: MemberId,
    args: &[egg::Id],
) -> (LocationKind, egg::Id) {
    let addr_ty = pred_addr_type(program, pred);
    let kind = LocationKind::from_addr_type(&addr_ty).expect("predicate address type");
    let addr = ctx.add_func_app_id(
        crate::verify::func_registry::func_id_for_member(pred),
        Box::new([]),
        addr_ty,
        args.into(),
    );
    (kind, addr)
}

/// Evaluate an `unfold`: consume the predicate chunk, reproduce the footprint
/// (fields recovered by projecting the snapshot), assume the body's pure facts.
/// Shared by method bodies and resource bodies; grafts the unfolded predicate's
/// pre-verified certificate (so the predicate must be verified first — a
/// self/mutual `unfolding` cycle is rejected upstream by `analyze`).
fn eval_unfold(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceDefinition>,
) -> Result<(), VerifyError> {
    let InstKind::Heap(HeapInst::Unfold { base, call, perm }) = &inst.kind else {
        unreachable!("eval_unfold called on a non-Unfold instruction");
    };
    let base_h = get_heap(state, base);
    let args: Vec<egg::Id> = call.args.iter().map(|v| state.get_val(ctx, v)).collect();
    let perm_id = eval_perm(ctx, state, perm);
    let pc_lits = collect_pc_lits(ctx, state, &inst.pc);

    // Consume the predicate chunk, recovering the snapshot `s` it holds (and,
    // in a certificate walk, its recipe — the term the new slots project from).
    let (pred_kind, pred_addr) = predicate_address(ctx, program, call.resource, &args);
    let a = ctx.egraph.find(pred_addr);
    let (s, s_recipe) = base_h
        .entries()
        .find_map(|(_, c)| (ctx.egraph.find(c.addr) == a).then(|| (c.value, c.recipe.clone())))
        .ok_or(VerifyError::InsufficientPermission)?;
    if ctx.recipe.is_some() && s_recipe.is_none() {
        return Err(VerifyError::Unimplemented(
            "purify: unfold of an unheld predicate",
        ));
    }
    let out = heap_subtract(
        ctx,
        &base_h,
        &pred_kind,
        Chunk::new(pred_addr, perm_id, s),
        &pc_lits,
    )?;

    // Reproduce the footprint from `s` (`unwrap(proj_i(s))` per slot), assuming
    // the predicate body. `reduce()` afterward collapses any snapshot tower a
    // repeated fold/unfold round-trip created.
    let FootprintResult { heap: out, .. } = walk_footprint(
        ctx,
        program,
        certs,
        call.resource,
        &args,
        out,
        ValueSource::ProjectSnap(s, s_recipe),
        Direction::Produce,
        Some(perm_id),
        &pc_lits,
        &pc_lits,
        false,
    )?;
    state.push_heap(out);
    ctx.reduce();
    Ok(())
}

/// Evaluate a `Snap`: narrow `heap` to the snapshot of the self-framed
/// resource `resource(args)` — the implicit precondition check of a
/// heap-dependent function call. Exhale-shaped but **non-consuming**: footprint
/// sufficiency is proven on a scratch subtraction chain (so aliased slots
/// require their sum) whose result is discarded — functions frame, they don't
/// consume. The resource's boolean is **asserted** over the values read from
/// `heap`, and the snapshot is the `cons` of those values
/// (`present ? Some(v) : None` per slot, as in `fold`). Returns the snapshot
/// e-class; the caller pushes it as the inst's `Val`.
fn eval_snap(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceDefinition>,
) -> Result<(egg::Id, Option<Val>), VerifyError> {
    use crate::verify::rewrite::AxiomPure;
    let InstKind::Pure(
        _,
        PureInst::Snap {
            resource,
            args,
            heap,
        },
    ) = &inst.kind
    else {
        unreachable!("eval_snap called on a non-Snap instruction");
    };
    let h = get_heap(state, heap);
    let arg_ids: Vec<egg::Id> = args.iter().map(|v| state.get_val(ctx, v)).collect();
    let pc_lits = collect_pc_lits(ctx, state, &inst.pc);

    // Non-consuming: the sufficiency subtraction runs on a scratch clone of `h`
    // (so aliased slots require their sum) whose resulting heap is discarded —
    // functions frame, they don't consume. Values are read from `h`; the body
    // boolean is asserted. The snapshot is the `cons` of the per-slot members.
    let FootprintResult {
        members,
        slot_recipes,
        ..
    } = walk_footprint(
        ctx,
        program,
        certs,
        *resource,
        &arg_ids,
        h.clone(),
        ValueSource::ReadHeap(h),
        Direction::Consume,
        None,
        &pc_lits,
        &pc_lits,
        true,
    )?;
    let s = build_snapshot(ctx, *resource, members);

    // A certificate walk mirrors the snapshot as `cons(Some(v_i))` over the
    // read values' recipes (a self-framed footprint is fully held, so each
    // slot is `Some`), and exports the nested callee's pre-token as a fact:
    // the precondition was *checked here* by this `Snap`'s implicit exhale,
    // but that check lives in the inst, not in an `Assert`, so deriving facts
    // from asserts would miss it. A caller who rebuilds this recipe (and
    // thereby materializes the nested `g(args, s)`) can then discharge the
    // guard on `g`'s own post fact without re-running the check — Silicon's
    // `bodyPreconditionPropagationAxiom` (`FunctionData.scala:302`).
    let recipe = if ctx.recipe.is_some() {
        let def = certs.get(resource).ok_or(VerifyError::DependencyFailed)?;
        let elems: Vec<Type> = def.footprint.iter().map(|sl| sl.elem.clone()).collect();
        let args_r: Vec<Val> = args
            .iter()
            .map(|a| state.require_recipe(a, OPERAND_RECIPE))
            .collect::<Result<_, _>>()?;
        let pc_r = state.recipe_pc(&inst.pc)?;
        let some_id = ctx.alloc.option_some();
        let cons_id = ctx.alloc.cons(*resource, 0);
        let name = program.name(*resource).to_string();
        let tok_id = ctx.alloc.pre_token(*resource, &name);
        let rb = ctx.recipe.as_mut().unwrap();
        let mut members_r = Vec::with_capacity(slot_recipes.len());
        for (i, r) in slot_recipes.iter().enumerate() {
            let v = r.clone().ok_or(VerifyError::Unimplemented(
                "purify: snap value outside footprint",
            ))?;
            members_r.push(rb.emit(AxiomPure::App {
                func: some_id,
                type_args: vec![elems[i].clone()],
                args: vec![v],
            }));
        }
        let s_r = rb.emit(AxiomPure::App {
            func: cons_id,
            type_args: Vec::new(),
            args: members_r,
        });
        let mut tok_args = args_r;
        tok_args.push(s_r.clone());
        let cond = rb.emit(AxiomPure::App {
            func: tok_id,
            type_args: Vec::new(),
            args: tok_args,
        });
        rb.export_fact(pc_r, cond, false);
        Some(s_r)
    } else {
        None
    };

    // The precondition held here — `walk_footprint` proved footprint
    // sufficiency and the resource's bool. **Release the pre-token**: assume
    // `R#pre(args, s)`, the uninterpreted stamp guarding every fact the callee
    // exported (`pre_token`). Silicon does exactly this after consuming a
    // function's precondition at a call site (`Evaluator.scala:652`). The token
    // is never defined, so it can only ever become true here — which is what
    // makes the guarded facts sound.
    let name = program.name(*resource).to_string();
    let tok = ctx.alloc.pre_token(*resource, &name);
    let mut tok_args = arg_ids;
    tok_args.push(s);
    let tok = ctx.add_func_app_id(tok, Box::new([]), Type::Bool, tok_args.into());
    ctx.assume_guarded(tok, pc_lits.iter().rev().copied());

    ctx.reduce();
    Ok((s, recipe))
}

/// Evaluate a `FromSnap`: widen a snapshot value back into a heap — the entry
/// of a heap-dependent function body reconstructing its precondition heap from
/// the snapshot parameter. Inverse of [`eval_snap`], inhale-shaped: one chunk
/// per footprint slot at the grafted address with the footprint permission and
/// value `unwrap(proj_i(s))` (as in `unfold`), and the resource's boolean is
/// **assumed** over the projected values. Returns the reconstructed heap.
fn eval_from_snap(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceDefinition>,
) -> Result<Heap, VerifyError> {
    let InstKind::Heap(HeapInst::FromSnap {
        resource,
        args,
        snap,
    }) = &inst.kind
    else {
        unreachable!("eval_from_snap called on a non-FromSnap instruction");
    };
    let arg_ids: Vec<egg::Id> = args.iter().map(|v| state.get_val(ctx, v)).collect();
    let s = state.get_val(ctx, snap);
    // The snapshot parameter's recipe — each reconstructed slot's provenance
    // becomes `unwrap(proj_i(s))` over it (certificate walks only).
    let s_recipe = if ctx.recipe.is_some() {
        Some(state.require_recipe(snap, OPERAND_RECIPE)?)
    } else {
        None
    };
    let pc_lits = collect_pc_lits(ctx, state, &inst.pc);

    // Reconstruct the precondition heap: produce one chunk per footprint slot
    // valued `unwrap(proj_i(s))` into the empty heap, assuming the resource body
    // (guarded by the path condition — a `FromSnap` may sit under a branch).
    let FootprintResult { heap: out, .. } = walk_footprint(
        ctx,
        program,
        certs,
        *resource,
        &arg_ids,
        Heap::empty(),
        ValueSource::ProjectSnap(s, s_recipe),
        Direction::Produce,
        None,
        &pc_lits,
        &pc_lits,
        false,
    )?;
    ctx.reduce();
    Ok(out)
}

/// Axiomatize the state: make every domain axiom's fact available to the unit
/// about to be verified. An axiom body is evaluated into the e-graph and its
/// boolean merged with `true` up front — domains are monomorphic, so there is no
/// type-σ instantiation; quantification over *values* is a `forall` in the body,
/// which becomes its own lazy-instantiation rule below. Axiom bodies are trusted
/// — no obligations (div-by-zero, deref permission) are checked on them.
///
/// Invariant: the eager ground-axiom evaluation below only ever sees **nullary**
/// quantifier occurrences — axioms are closed and `let` is rejected in pure
/// lowering, so an axiom's top-level `forall`s capture nothing. Occurrences
/// *with* capture arguments enter the e-graph when an outer quantifier
/// instance's body is built (`rewrite::build_instance`), or as ordinary
/// `FuncApp` evaluation of a hosting method/resource body (v3: `forall`s in
/// method statements and contracts capture enclosing params/locals; those
/// bodies are evaluated per unit, never eagerly here).
fn assume_axioms(ctx: &mut VerifyContext<'_>, program: &vmir::Program) -> Result<(), VerifyError> {
    // One rule instantiates every `forall` in the program: quantifiers are
    // e-nodes (data), not rules, so one generic rule suffices — and a `forall`
    // materialized *during* saturation (by an outer instantiation, or by a
    // certificate graft) is picked up on the next iteration, which per-quantifier
    // rules structurally could not do (egg forbids mid-run rule injection).
    if !ctx.alloc.quant_table().is_empty() {
        let table = std::sync::Arc::clone(ctx.alloc.quant_table());
        ctx.axiom_rules
            .push(crate::verify::rewrite::forall_rule(table));
    }
    for decl in program.decls.iter() {
        let vmir::Declaration::Axiom(ax) = decl else {
            continue;
        };
        let mut state = EvalState::new();
        for inst in &ax.body.insts {
            match &inst.kind {
                InstKind::Pure(ty, pi) => {
                    // Axiom bodies are heap-free and trusted — no `Deref`, so the
                    // path condition is irrelevant here.
                    let (id, _) = eval_pure_inst(ctx, &state, ty, pi, &[])?;
                    state.push_val(id, ty.clone(), None);
                }
                InstKind::Assume(val) => {
                    let id = state.get_val(ctx, val);
                    let true_ = ctx.true_();
                    ctx.union(id, true_);
                    ctx.egraph.rebuild();
                }
                // An axiom body is never verified — a stray obligation
                // (there are none today: callees are precondition-free)
                // would be skipped, and heap insts cannot occur.
                InstKind::Assert(_) => {}
                _ => return Err(VerifyError::Unimplemented("non-pure inst in axiom body")),
            }
        }
        let res = state.get_val(ctx, &ax.body.res);
        let true_ = ctx.true_();
        ctx.union(res, true_);
        ctx.egraph.rebuild();
    }
    // One lazy unfold rule per already-verified function certificate: `analyze`
    // guarantees a function only ever calls functions verified earlier (it
    // rejects (mutual) recursion as a dependency cycle), so every function this
    // unit could reference already has a cert in `fn_certs` by the time its
    // ctx is set up here — same guarantee the driver's topological order
    // (`mod.rs`) already relies on. Each rule rebuilds the recipe's body lazily
    // (add-only) the moment a `FuncApp(f, ..)` occurrence is seen during
    // saturation (see `rewrite::function_rule`), instead of eagerly grafting it
    // once at translation-walk time.
    if let Some(fn_certs) = ctx.fn_certs {
        let contracts = contract_members(program);
        for (&id, def) in fn_certs.iter() {
            let name = ctx.member_name(id);
            let func = crate::verify::func_registry::func_id_for_member(id);
            // The uniform `f%pre` presence trigger gates the body-unfold of a
            // **genuine** function: the rule only fires where a `FuncApp(f%pre,
            // args)` node was minted (a value-position call, or a propagation step
            // in an unfolded value body). A **contract** function (`#requires` /
            // `#ensures`) is left ungated (`None`) — it must inline its formula
            // freely, as before, or a `f#ensures` occurrence stays opaque and its
            // post never reaches `f(args)`.
            let pre_token = (!contracts.contains(&id)).then(|| ctx.alloc.fn_pre_token(id, &name));
            ctx.axiom_rules.push(crate::verify::rewrite::function_rule(
                &name,
                func,
                std::sync::Arc::clone(def),
                pre_token,
            ));
            // A recursive function's post fact also triggers on its limited
            // twin `f'` — that is what delivers the postcondition at a
            // recursive unroll (the twin has no unfold rule by design).
            if def.limited.is_some() && def.facts.iter().any(|f| f.post) {
                ctx.axiom_rules
                    .push(crate::verify::rewrite::function_post_rule(
                        &name,
                        std::sync::Arc::clone(def),
                    ));
            }
        }
    }
    Ok(())
}

/// Resolve a trigger pattern term's heads to verifier `FuncId`s — the same
/// mapping [`prepare_body`] applies to the corresponding `PureInst`, so a
/// pattern matches exactly the nodes a body would build.
pub(crate) fn prepare_trig_term(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    term: &vmir::TrigTerm,
) -> crate::verify::rewrite::PreparedTerm {
    use crate::verify::rewrite::PreparedTerm;
    match term {
        vmir::TrigTerm::Bound(i) => PreparedTerm::Bound(*i),
        vmir::TrigTerm::Capture(c) => PreparedTerm::Capture(*c),
        vmir::TrigTerm::Lit(lit) => PreparedTerm::Lit(lit.clone()),
        vmir::TrigTerm::App {
            head,
            type_args,
            args,
        } => {
            let func = match head {
                vmir::TrigHead::Func(id) => crate::verify::func_registry::func_id_for_member(*id),
                vmir::TrigHead::AdtCons { adt, variant } => alloc.cons(*adt, *variant),
                vmir::TrigHead::AdtProj {
                    adt,
                    variant,
                    field,
                } => alloc.proj(*adt, *variant, *field),
                vmir::TrigHead::AdtTag { adt } => alloc.tag(*adt),
            };
            PreparedTerm::App {
                func,
                type_args: type_args.iter().cloned().collect(),
                args: args.iter().map(|a| prepare_trig_term(alloc, a)).collect(),
            }
        }
    }
}

/// Lower an axiom/quantifier body's inst stream into registry-resolved pure
/// steps (every callee down to its verifier `FuncId`), ready for the applier —
/// which has no registry access at rule-application time.
pub(crate) fn prepare_body(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    quants: &crate::verify::quant::RecipeTable,
    insts: &[vmir::Inst],
) -> Result<Vec<crate::verify::rewrite::AxiomInst>, VerifyError> {
    use crate::verify::rewrite::{AxiomInst, AxiomPure};
    let mut out = Vec::with_capacity(insts.len());
    for inst in insts {
        // A nested `forall` is a step like any other: it materializes the inner
        // e-node with the enclosing instance's values as capture children.
        if let InstKind::Pure(_, PureInst::Forall(q)) = &inst.kind {
            out.push(AxiomInst::Forall {
                recipe: quants.id_of(q)?,
                caps: q.captures.clone(),
            });
            continue;
        }
        let prepared = match &inst.kind {
            InstKind::Pure(_, pi) => AxiomInst::Val(match pi {
                PureInst::Binary(op, l, r) => AxiomPure::Binary(*op, l.clone(), r.clone()),
                PureInst::Ternary(c, t, e) => AxiomPure::Ternary(c.clone(), t.clone(), e.clone()),
                PureInst::RealCast(v) => AxiomPure::RealCast(v.clone()),
                PureInst::FunctionCall(fc) => AxiomPure::App {
                    func: crate::verify::func_registry::func_id_for_member(fc.function),
                    type_args: fc.type_args.clone(),
                    args: fc.args.iter().cloned().collect(),
                },
                PureInst::AdtCons {
                    adt,
                    type_args,
                    variant,
                    args,
                } => AxiomPure::App {
                    func: alloc.cons(*adt, *variant),
                    type_args: type_args.clone(),
                    args: args.clone(),
                },
                PureInst::AdtProj {
                    adt,
                    type_args,
                    variant,
                    field,
                    base,
                } => AxiomPure::App {
                    func: alloc.proj(*adt, *variant, *field),
                    type_args: type_args.clone(),
                    args: vec![base.clone()],
                },
                PureInst::AdtTag {
                    adt,
                    type_args,
                    base,
                } => AxiomPure::App {
                    func: alloc.tag(*adt),
                    type_args: type_args.clone(),
                    args: vec![base.clone()],
                },
                PureInst::Fresh
                | PureInst::Deref(..)
                | PureInst::Perm(..)
                | PureInst::Snap { .. }
                | PureInst::Forall(_) => {
                    return Err(VerifyError::Unimplemented("impure inst in axiom body"));
                }
            }),
            InstKind::Assume(v) => AxiomInst::Assume(v.clone()),
            // Never verified; nothing to record.
            InstKind::Assert(_) => continue,
            _ => return Err(VerifyError::Unimplemented("non-pure inst in axiom body")),
        };
        out.push(prepared);
    }
    Ok(out)
}

/// Check the well-definedness of a `forall` **at the point it is encountered**,
/// in a throwaway clone of the live e-graph.
///
/// Cloning (rather than seeding a blank graph) makes every ambient fact — the
/// host's path condition, the assumed axioms, grafted certificates — available
/// for free, with no seeding policy and no pollution of the real graph: whatever
/// the binders' fresh values touch dies with the scratch graph.
///
/// The binders become fresh values and the captures keep their real e-classes, so
/// the body's side conditions are discharged *for an arbitrary binding*. Those
/// conditions are exactly a pure expression's: `Div`/`Mod` divisors, and the
/// `assert f#requires(..)` stitched at a call to a contract-bearing function.
/// Body-local path conditions come along (short-circuit lowering emits them), so
/// a guard proves its own consequent's WD: `forall x :: {f(x)} x != 0 ==> f(10 / x)`
/// discharges the division under `<x != 0>`.
///
/// A nested `forall` is checked recursively here — with its encloser's binders
/// already fresh — so no WD obligation ever survives into a recipe. That is what
/// keeps instantiation (which runs inside a rewrite rule, where nothing can be
/// proven) obligation-free.
fn check_forall_wd(
    ctx: &mut VerifyContext<'_>,
    q: &vmir::Forall,
    caps: &[egg::Id],
    host_pc: &[(egg::Id, Polarity)],
) -> Result<(), VerifyError> {
    // `ctx.egraph` is a scratch clone for the duration; the live graph, its
    // fixpoint cache and the memo scope are handled by `with_scratch_graph`.
    // The certificate recipe (if one is being built) is paused: the WD walk's
    // scratch evaluation must not mirror steps into the host's recipe.
    let recipe = ctx.recipe.take();
    let res = ctx.with_scratch_graph(|ctx| check_forall_wd_in_scratch(ctx, q, caps, host_pc));
    ctx.recipe = recipe;
    res
}

fn check_forall_wd_in_scratch(
    ctx: &mut VerifyContext<'_>,
    q: &vmir::Forall,
    caps: &[egg::Id],
    host_pc: &[(egg::Id, Polarity)],
) -> Result<(), VerifyError> {
    let mut state = EvalState::new();
    for (id, ty) in caps.iter().zip(q.cap_types.iter()) {
        state.push_val(*id, ty.clone(), None);
    }
    for ty in q.bound.iter() {
        let fresh = ctx.fresh_symbolic_value(ty.clone());
        state.push_val(fresh, ty.clone(), None);
    }

    for inst in &q.body.insts {
        // The body's own guards sit *under* the host's: a side condition must hold
        // wherever the quantifier is stated, and wherever the body reaches it.
        let mut pc_lits = host_pc.to_vec();
        pc_lits.extend(collect_pc_lits(ctx, &state, &inst.pc));

        for (goal, err) in inst_obligations(ctx, &state, &inst.kind, &pc_lits) {
            if !ctx.prove_under_pc(goal, &pc_lits) {
                return Err(err);
            }
        }
        match &inst.kind {
            // A nested quantifier: check it under this level's fresh binders, then
            // build its node like any other step.
            InstKind::Pure(ty, pi @ PureInst::Forall(inner)) => {
                let inner_caps: Vec<egg::Id> = inner
                    .captures
                    .iter()
                    .map(|v| state.get_val(ctx, v))
                    .collect();
                check_forall_wd(ctx, inner, &inner_caps, &pc_lits)?;
                let (id, _) = eval_pure_inst(ctx, &state, ty, pi, &pc_lits)?;
                state.push_val(id, ty.clone(), None);
            }
            InstKind::Pure(ty, pi) => {
                let (id, _) = eval_pure_inst(ctx, &state, ty, pi, &pc_lits)?;
                state.push_val(id, ty.clone(), None);
            }
            // A callee's postcondition, stitched at the call: assume it under the
            // guards it was emitted with.
            InstKind::Assume(val) => {
                let id = state.get_val(ctx, val);
                ctx.assume_guarded(id, pc_lits.iter().rev().copied());
            }
            // A callee's precondition, stitched at the call site: the other half of
            // a quantifier body's well-definedness, and the reason a WD check needs
            // the *ambient* facts (the guard establishing it may be the body's own
            // implication, or a fact the host already knows).
            InstKind::Assert(val) => {
                let id = state.get_val(ctx, val);
                if !ctx.prove_under_pc(id, &pc_lits) {
                    return Err(VerifyError::AssertionFailed);
                }
            }
            InstKind::Refute(_) | InstKind::Heap(_) => {
                return Err(VerifyError::Unimplemented("impure inst in a forall body"));
            }
        }
    }
    Ok(())
}

/// Per-instruction evaluator: the shared signature of [`eval_method_inst`] and
/// [`eval_resource_body_inst`], so [`walk_body`] can be parameterized by which
/// one the body kind uses.
type EvalFn = fn(
    &mut VerifyContext<'_>,
    &vmir::Program,
    &mut EvalState,
    &Inst,
    &HashMap<MemberId, ResourceDefinition>,
) -> Result<(), VerifyError>;

/// The single body-walk shared by all three drivers: for each instruction,
/// discharge its side-condition [`inst_obligations`] under the path condition,
/// then evaluate it, snapshotting for the visualizer throughout. Keeping this in
/// one place is what makes an obligation added to `inst_obligations` impossible
/// to skip in one driver (the `5aad7bc` division-check bug: the check existed but
/// was wired into only one of three near-identical copies of this loop).
///
/// `eval` selects the per-inst semantics (method/function vs resource body).
/// `footprint_ops`, when `Some`, collects each `acc`'s `(loc, perm)` operand in
/// body order — the resource driver's one extra responsibility (drives the
/// fold/unfold snapshot layout); `None` for method and function bodies.
#[allow(clippy::too_many_arguments)]
fn walk_body(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    snap: &mut Snapshotter,
    insts: &[Inst],
    certs: &HashMap<MemberId, ResourceDefinition>,
    eval: EvalFn,
    mut footprint_ops: Option<&mut Vec<(Val, vmir::Perm)>>,
) -> Result<(), VerifyError> {
    for (inst_idx, inst) in insts.iter().enumerate() {
        assert_statement_pc_is_block_cube(ctx, state, inst);
        if let (Some(ops), InstKind::Heap(HeapInst::Combine { loc, perm, .. })) =
            (&mut footprint_ops, &inst.kind)
        {
            ops.push((loc.clone(), perm.clone()));
        }
        let vals_before = state.vals.len();
        let heaps_before = state.heaps.len();
        // Rendering the instruction (and cloning heaps for the viz snapshot) is
        // pure diagnostics — deferred to the failure paths and the (env-gated)
        // snapshotter so the hot path pays nothing for it.
        let inst_text = |program: &vmir::Program| {
            format_inst(
                inst,
                &program.decls,
                &program.interner,
                &program.groups,
                vals_before,
                heaps_before,
            )
        };
        let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
        for (goal, err) in inst_obligations(ctx, state, &inst.kind, &pc_lits) {
            if !ctx.prove_under_pc(goal, &pc_lits) {
                if crate::verify::viz::dump_perm_enabled() {
                    eprintln!(
                        "[perm-dump] failed obligation goal:\n{}",
                        crate::verify::viz::dump_term(ctx, goal, 64),
                    );
                }
                let inst_text = inst_text(program);
                if snap.enabled() {
                    let heaps = display_heaps(state, &inst.kind, heaps_before);
                    snap.snapshot(ctx, &heaps, &format!("FAIL: {}", inst_text), Some(goal));
                }
                return Err(err.with_inst(inst_text, inst_idx, insts.len()));
            }
        }
        // A quantifier's own side conditions, discharged once per syntactic
        // occurrence against fresh binders in a scratch clone (see
        // [`check_forall_wd`]). It happens here, not in the evaluator, because it
        // needs the path condition — and here it cannot be forgotten by one of the
        // three drivers. Axiom bodies never reach this walk: they stay trusted.
        if let InstKind::Pure(_, PureInst::Forall(q)) = &inst.kind {
            let caps: Vec<egg::Id> = q.captures.iter().map(|v| state.get_val(ctx, v)).collect();
            if let Err(err) = check_forall_wd(ctx, q, &caps, &pc_lits) {
                let inst_text = inst_text(program);
                if snap.enabled() {
                    let heaps = display_heaps(state, &inst.kind, heaps_before);
                    snap.snapshot(ctx, &heaps, &format!("FAIL: {}", inst_text), None);
                }
                return Err(err.with_inst(inst_text, inst_idx, insts.len()));
            }
        }
        if let Err(err) = eval(ctx, program, state, inst, certs) {
            let inst_text = inst_text(program);
            if snap.enabled() {
                let heaps = display_heaps(state, &inst.kind, heaps_before);
                snap.snapshot(ctx, &heaps, &format!("FAIL: {}", inst_text), None);
            }
            return Err(err.with_inst(inst_text, inst_idx, insts.len()));
        }
        ctx.alloc.stats.insts_processed += 1;
        if snap.enabled() {
            let highlight =
                (state.vals.len() > vals_before).then(|| state.vals[state.vals.len() - 1]);
            let heaps = display_heaps(state, &inst.kind, heaps_before);
            snap.snapshot(ctx, &heaps, &inst_text(program), highlight);
        }
    }
    Ok(())
}

pub(crate) fn verify_method(
    program: &vmir::Program,
    method_name: &str,
    method: &Method,
    certs: &HashMap<MemberId, ResourceDefinition>,
    fn_certs: &HashMap<MemberId, std::sync::Arc<FunctionDefinition>>,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> Result<(), VerifyError> {
    let mut ctx = VerifyContext::new(&program.interner, &program.decls, &program.groups, alloc);
    ctx.fn_certs = Some(fn_certs);
    assume_axioms(&mut ctx, program)?;
    let mut state = EvalState::new();
    let mut snap = Snapshotter::from_env(method_name);
    snap.snapshot(&ctx, &[], "init", None);

    // Block walker (Stage 3): evaluate blocks in stored order — which is
    // topological *and* the original emission order, so positional `EvalState`
    // temps (`vals[n]` == `Temp(n)`) stay valid — running each block's `join`
    // phase then its `body` phase through the same per-inst engine (`walk_body`)
    // the flat verifier used. The heap threads linearly via each inst's explicit
    // `base: HeapVal`; the per-predecessor structural merge is a later stage.
    for (bid, block) in method.blocks.iter_enumerated() {
        // Stored order is topological: a block's predecessors have smaller ids.
        // (A future lowering bug that broke this would corrupt positional eval.)
        debug_assert!(
            match &block.preds {
                vmir::Preds::Entry => true,
                vmir::Preds::From(p) => p.0 < bid.0,
                vmir::Preds::Join { then_, els, .. } => then_.0 < bid.0 && els.0 < bid.0,
            },
            "blocks must be stored in topological order (preds precede)"
        );
        // ── Stage-4 heap hook ──────────────────────────────────────────────
        // Stage 4 will derive this block's `h_in` from `block.preds` here (a
        // `HeapInst::Merge` for a `Join`). Stage 3 threads the heap linearly via
        // the insts' explicit `base: HeapVal` refs, so there is nothing to do.
        // ───────────────────────────────────────────────────────────────────
        // No scratch during the join phase: the cube's reach boolean is
        // materialized *by* the join, so it isn't resolvable until join runs.
        ctx.end_block();
        walk_body(
            &mut ctx,
            program,
            &mut state,
            &mut snap,
            &block.join,
            certs,
            eval_method_inst,
            None,
        )?;
        // Record this block's cube for the (experimental) per-block scratch. All
        // body insts share it (vmir::Block::cube), so the scratch assumes it once.
        let cube = collect_pc_lits(&mut ctx, &state, &block.cube);
        ctx.begin_block(cube);
        walk_body(
            &mut ctx,
            program,
            &mut state,
            &mut snap,
            &block.body,
            certs,
            eval_method_inst,
            None,
        )?;
        // Dead-arm tagging: if the block's cube is now refuted in the ground
        // graph (an unreachable arm — e.g. after `inhale false` unioned a reach
        // flag with `false`), tag its exit heap so a downstream join merge drops
        // it instead of forming a `0`-leaf that would need a case split. Cheap:
        // just consults folded literals, no clone.
        if let vmir::HeapVal::Temp(n) = block.h_out {
            let lits = collect_pc_lits(&mut ctx, &state, &block.cube);
            let refuted = lits.iter().any(|(id, pol)| {
                matches!(
                    ctx.egraph[ctx.egraph.find(*id)].data.known(),
                    Some(Literal::Bool(b)) if *b != matches!(pol, Polarity::Positive)
                )
            });
            if refuted {
                state.dead_heaps.insert(n);
            }
        }
    }
    ctx.end_block();
    if let Some(t) = crate::verify::heap::MergeTrace::take() {
        eprintln!(
            "[merge-trace] {method_name}: selects_built={} zero_leaves={} max_depth={}",
            t.selects_built, t.zero_leaves, t.max_depth
        );
    }
    Ok(())
}

/// Verify a resource self-contained: run its body in a fresh egraph with fresh
/// symbolic params (a two-state resource's pre-state snapshot is an ordinary
/// trailing param), discharging each instruction's side-condition obligations
/// under its path condition. Abstract resources have nothing to check. This
/// establishes well-formedness **once**; method call sites reuse it without
/// re-checking (see [`eval_resource_call`]).
pub(crate) fn verify_resource(
    program: &vmir::Program,
    resource_name: &str,
    resource: &Resource,
    certs: &HashMap<MemberId, ResourceDefinition>,
    fn_certs: &HashMap<MemberId, std::sync::Arc<FunctionDefinition>>,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> Result<Option<ResourceDefinition>, VerifyError> {
    let Some(body) = resource.body.as_ref() else {
        // Abstract resource: nothing to prove, no definition.
        return Ok(None);
    };

    let mut ctx = VerifyContext::new(&program.interner, &program.decls, &program.groups, alloc);
    ctx.fn_certs = Some(fn_certs);
    assume_axioms(&mut ctx, program)?;
    // The certificate recipe is built by the walk itself: each `acc` records a
    // footprint slot, `Deref`s resolve through chunk provenance. Installed
    // after `assume_axioms` so axiom bodies don't mirror into the recipe.
    ctx.recipe = Some(crate::verify::cert::RecipeBuilder::new(
        resource.params.len(),
        None,
        None,
        None,
    ));
    let params: Vec<egg::Id> = resource
        .params
        .iter()
        .map(|ty| ctx.fresh_symbolic_value(ty.clone()))
        .collect();
    // A two-state (`Ctx`) resource needs no special seeding: its pre-state
    // arrives as the trailing snapshot parameter (a fresh symbolic like any
    // other param) and its body's entry `FromSnap` reconstructs the pre-state
    // heap, implicitly assuming the precondition resource's boolean.
    let mut state = EvalState::with_args(params, resource.params.clone());

    let mut snap = Snapshotter::from_env(resource_name);
    snap.snapshot(&ctx, &[], "init", None);

    walk_body(
        &mut ctx,
        program,
        &mut state,
        &mut snap,
        &body.insts,
        certs,
        eval_resource_body_inst,
        None,
    )?;

    // Capture the body as a pure recipe (add-only; imports no e-classes). Each
    // call site rebuilds the footprint addresses/permissions and the body boolean
    // from the recipe and re-derives any merge it needs itself (Finding C).
    // Slot address/permission recipes and the body boolean are sliced out of
    // the shared step stream the walk built.
    use crate::verify::cert::SlotRecipe;
    let rb = ctx.recipe.take().expect("resource walk builds a recipe");
    let footprint = rb
        .pending_slots
        .iter()
        .map(|(kind, elem, addr, perm)| {
            Ok(SlotRecipe {
                kind: kind.clone(),
                elem: elem.clone(),
                addr: rb.slice(addr)?,
                perm: rb.slice(perm)?,
            })
        })
        .collect::<Result<Vec<_>, VerifyError>>()?;
    let bool_r = state
        .recipe_of(&body.res.1)
        .ok_or(VerifyError::Unimplemented(
            "purify: resource bool without a recipe",
        ))?;
    Ok(Some(ResourceDefinition {
        footprint,
        bool: rb.slice(&bool_r)?,
    }))
}

/// Verify a non-recursive function and capture its body as a **pure term
/// recipe** ([`FunctionDefinition`]) for other units to unfold lazily at call
/// sites (`rewrite::function_rule`). Abstract functions (no body) have nothing
/// to verify.
///
/// The walk runs the ordinary live eval (obligations, `FromSnap`/`Unfold` heap
/// reconstruction, `Deref` values), logging each heap-reconstruction event into
/// `ctx.heap_events`. Then [`purify_function`] re-walks the body once, turning it
/// into an add-only recipe over the params (and the snapshot param, for
/// heap-dependent functions): every `Deref` becomes the pure term the snapshot
/// projects to (`unwrap(proj_i(snap))`, possibly nested through `unfolding`), and
/// the entry `assume f#requires` is **dropped**. That drop is the whole point —
/// the old design cloned the verified e-graph, so a precondition-derived merge
/// (e.g. `g(x) ≡ 5` from `requires g(x)==5` once a body obligation saturated)
/// rode into every call site via `transplant`; a recipe imports no e-classes, so
/// it cannot leak (Finding B).
///
/// Callees — including the function's own `f#requires`/`f#ensures` contract
/// functions — are ordinary `Function` decls verified earlier in dependency
/// order, so their recipes are already in `fn_certs`, and `assume_axioms`
/// (called at the top of this function's own `ctx` setup) has already installed
/// their unfold rules — saturation (triggered via `prove_under_pc`) discharges
/// the contract obligations lazily as needed.
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_function(
    program: &vmir::Program,
    function_name: &str,
    self_id: MemberId,
    function: &Function,
    certs: &HashMap<MemberId, ResourceDefinition>,
    fn_certs: &HashMap<MemberId, std::sync::Arc<FunctionDefinition>>,
    // The members of `self_id`'s SCC iff it is a genuine recursion cycle (else
    // `None`). In-SCC callees are retargeted to their limited twin in the recipe,
    // and this function's own limited twin is recorded so its unfold rule frames
    // `f(x) == f'(x)`.
    recursive_scc: Option<&std::collections::HashSet<MemberId>>,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> Result<Option<std::sync::Arc<FunctionDefinition>>, VerifyError> {
    let Some(body) = function.body.as_ref() else {
        // Abstract/uninterpreted function: no body to verify. Its contract
        // decls are verified as ordinary Functions (spec WF); synthesize the
        // guarded post axiom from the contract links, if any.
        return Ok(contract_post_definition(
            alloc,
            program,
            self_id,
            function,
            recursive_scc.is_some(),
        ));
    };

    let mut ctx = VerifyContext::new(&program.interner, &program.decls, &program.groups, alloc);
    ctx.fn_certs = Some(fn_certs);
    assume_axioms(&mut ctx, program)?;
    // The certificate recipe is built by the walk itself (single pass): the
    // pre-token guard, the limited-twin substitution set, and the exit-post
    // shape are fixed up front.
    let guard_app = pre_token(ctx.alloc, program, function);
    let post_meta = function.ensures.as_ref().map(|en| {
        let self_func = if recursive_scc.is_some() {
            let name = ctx.member_name(self_id);
            ctx.alloc.limited(self_id, &name)
        } else {
            crate::verify::func_registry::func_id_for_member(self_id)
        };
        crate::verify::cert::PostMeta {
            ensures_member: en.member,
            ensures_func: crate::verify::func_registry::func_id_for_member(en.member),
            self_func,
            args: en.args.clone(),
        }
    });
    let mut recipe = crate::verify::cert::RecipeBuilder::new(
        function.params.len(),
        guard_app,
        recursive_scc.cloned(),
        post_meta,
    );
    // A **contract** function (some other function's `#requires`/`#ensures`, i.e. a
    // lowered pre/postcondition) is a spec body: its nested calls emit no
    // precondition-propagation token, so unfolding it at a client leaves the
    // callees dormant (discharged by congruence, not by unfolding) — the pcguard
    // validator-ladder win. A regular function body stays a value position.
    if contract_members(program).contains(&self_id) {
        recipe.mark_spec();
    }
    ctx.recipe = Some(recipe);
    // Recursive batch: every SCC member's spec-derived post axiom is available
    // while this body is checked (Silicon emits `post` in phase 1, before the
    // phase-2 body check) — this is what lets the exit assert use a recursive
    // call's postcondition (induction; termination is not checked, same as
    // Silicon without `decreases`).
    if let Some(scc) = recursive_scc {
        for &m in scc {
            let vmir::Declaration::Function(mf) = &program.decls[m] else {
                continue;
            };
            if let Some(post) = contract_post_definition(ctx.alloc, program, m, mf, false) {
                let name = ctx.member_name(m);
                let func = crate::verify::func_registry::func_id_for_member(m);
                ctx.axiom_rules
                    .push(crate::verify::rewrite::facts_rule(&name, func, post));
            }
        }
    }
    // Params seed the initial `Val::Temp(0..n_params)` slots (heap-free: no ctx heap).
    let params: Vec<egg::Id> = function
        .params
        .iter()
        .map(|ty| ctx.fresh_symbolic_value(ty.clone()))
        .collect();
    let param_types: Vec<Type> = function.params.iter().cloned().collect();
    let mut state = EvalState::with_args(params.clone(), param_types);

    let mut snap = Snapshotter::from_env(function_name);
    snap.snapshot(&ctx, &[], "init", None);
    // The method-body eval path handles every inst a function body can contain
    // (pure ops, the entry `assume`, `Snap`/`FromSnap`/`Unfold` for heap-dependent
    // functions).
    walk_body(
        &mut ctx,
        program,
        &mut state,
        &mut snap,
        &body.insts,
        certs,
        eval_method_inst,
        None,
    )?;

    // The walk mirrored the body into a pure, add-only recipe (params → args
    // at call sites via `build_instance`); `Deref` values became the pure
    // terms their chunks carry as provenance (`unwrap(proj_i(snap))`), and the
    // entry `assume f#requires` was dropped (Finding B — `Assume` emits no
    // recipe step, so the precondition cannot leak into callers).
    let rb = ctx.recipe.take().expect("function walk builds a recipe");
    let (steps, facts) = rb.into_function_parts()?;
    let res = state
        .recipe_of(&body.res)
        .ok_or(VerifyError::Unimplemented(
            "purify: function result without a recipe",
        ))?;
    // A recursive function records its limited twin so the unfold rule frames
    // `f(x) == f'(x)`. Minted here (not in the recipe) so the id exists even if
    // the body has no reachable recursive call under some path.
    let limited = recursive_scc.map(|_| {
        let name = ctx.member_name(self_id);
        ctx.alloc.limited(self_id, &name)
    });
    Ok(Some(std::sync::Arc::new(FunctionDefinition {
        n_params: function.params.len(),
        steps,
        res: Some(res),
        limited,
        facts,
    })))
}

/// The **pre-token** guarding every fact a function's body exports: the
/// application `(func, args)` that must hold for the facts to fire, over the
/// function's own param space (`Val::Temp(0..n_params)` — so recipe space too,
/// where the params are the identity).
///
/// The two function flavours supply it differently, but the guard *shape* is the
/// same single boolean application either way:
/// - **heap-free**: `f#requires(params)`, a **defined** boolean function. A call
///   site's `Assert f#requires(args)` passing is what makes it true there.
/// - **heap-dependent**: `R#pre(args, s)`, an **uninterpreted** token over the
///   `#requires` Resource (see [`FuncRegistry::pre_token`]). The precondition is
///   not definable from `(args, s)` — it also demands the footprint — so the
///   token is stamped by [`eval_snap`] where the check passed.
///
/// `None` for a function without a precondition (its facts are unguarded).
/// The set of **contract** functions — every function's lowered
/// `#requires`/`#ensures` (booleans carrying a pre/postcondition), collected from
/// the contract links. Contract-function bodies are spec positions: they are left
/// ungated (must inline freely) and suppress precondition propagation.
fn contract_members(program: &vmir::Program) -> std::collections::HashSet<MemberId> {
    let mut set = std::collections::HashSet::new();
    for decl in program.decls.iter() {
        let vmir::Declaration::Function(f) = decl else {
            continue;
        };
        if let Some(r) = f.requires.as_ref() {
            set.insert(r.member());
        }
        if let Some(e) = f.ensures.as_ref() {
            set.insert(e.member);
        }
    }
    set
}

fn pre_token(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    program: &vmir::Program,
    function: &Function,
) -> Option<(crate::verify::lang::FuncId, Vec<Val>)> {
    match function.requires.as_ref()? {
        vmir::Requires::Pure(rq) => Some((
            crate::verify::func_registry::func_id_for_member(rq.member),
            rq.args.clone(),
        )),
        vmir::Requires::Framed {
            resource,
            args,
            snap,
        } => {
            let name = program.name(*resource).to_string();
            let mut args = args.clone();
            args.push(snap.clone());
            Some((alloc.pre_token(*resource, &name), args))
        }
    }
}

/// Synthesize an **abstract** function's definition: no body, nothing to
/// verify — just the guarded post axiom `pre-token ⟹ f#ensures(params,
/// f(params))` built from the contract links. (Silicon's phase 1 emits
/// `post`/`postProp` for abstract functions once the spec is well-defined; our
/// contract decls get that WF check as ordinary `Function` verification,
/// scheduled first by the link edges in `analyze`.) `None` when there is nothing
/// to export: no ensures, or a generic function.
fn contract_post_definition(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    program: &vmir::Program,
    self_id: MemberId,
    function: &Function,
    // Set when this is the function's *own* definition and it sits in a
    // recursion cycle: the fact then expresses the result as the limited twin
    // `f'(params)` and the definition records `f'`, so the unfold rule frames
    // `f(x) == f'(x)`. Without the frame an abstract SCC member would be
    // unreachable from a sibling's recipe, which lowers it to `f'`. Cleared for
    // the in-batch pre-seed (rules keyed on the full ids, no frames installed
    // yet).
    recursive: bool,
) -> Option<std::sync::Arc<FunctionDefinition>> {
    use crate::verify::cert::Fact;
    use crate::verify::func_registry::func_id_for_member;
    use crate::verify::rewrite::{AxiomInst, AxiomPure};

    let en = function.ensures.as_ref()?;
    let limited = recursive.then(|| alloc.limited(self_id, program.name(self_id)));
    let n_params = function.params.len();
    let mut steps: Vec<AxiomInst> = Vec::new();
    let emit = |steps: &mut Vec<AxiomInst>, pure: AxiomPure| -> Val {
        let v = Val::Temp(n_params + steps.len());
        steps.push(AxiomInst::Val(pure));
        v
    };
    // Link args are over the params (`Temp(0..n_params)`) — identity in recipe
    // space, so they can be used verbatim.
    let mut guards = Vec::new();
    if let Some((func, args)) = pre_token(alloc, program, function) {
        let tok = emit(
            &mut steps,
            AxiomPure::App {
                func,
                type_args: Vec::new(),
                args,
            },
        );
        guards.push((tok, vmir::Polarity::Positive));
    }
    let self_app = emit(
        &mut steps,
        AxiomPure::App {
            func: limited.unwrap_or_else(|| func_id_for_member(self_id)),
            type_args: Vec::new(),
            args: (0..n_params).map(Val::Temp).collect(),
        },
    );
    let args: Vec<Val> = en
        .args
        .iter()
        .map(|a| match a {
            vmir::ContractArg::Val(v) => v.clone(),
            vmir::ContractArg::Result => self_app.clone(),
        })
        .collect();
    let cond = emit(
        &mut steps,
        AxiomPure::App {
            func: func_id_for_member(en.member),
            type_args: Vec::new(),
            args,
        },
    );
    Some(std::sync::Arc::new(FunctionDefinition {
        n_params,
        steps,
        res: None,
        limited,
        facts: vec![Fact {
            guards,
            cond,
            post: true,
        }],
    }))
}

/// Proof obligations implied by an instruction's kind, as `(goal, error)` pairs
/// that must each be proven `true` under the instruction's path condition. A
/// `Deref` requires a positive permission for the location it reads; `acc`
/// requires a non-negative permission; division requires a non-zero divisor.
///
/// This is the **single** source of per-instruction obligations: every body
/// driver (`verify_method`, `verify_resource`, `verify_function`) discharges
/// exactly this list, so an obligation added here is checked everywhere.
fn inst_obligations(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    kind: &InstKind,
    pc_lits: &[(egg::Id, Polarity)],
) -> Vec<(egg::Id, VerifyError)> {
    match kind {
        // `0 < perm(heap, loc)` — the location must be framed by the heap being
        // read. In a function body that heap is the one the entry `FromSnap`
        // reconstructs from the snapshot parameter, so this failing means a read
        // outside the declared precondition. `chunk_under_pc` lets an address
        // that only aliases a held chunk under this instruction's branch (e.g.
        // `y.f` where `x == y` holds here) still frame.
        InstKind::Pure(_, PureInst::Deref(heap, loc)) => {
            let addr = state.get_val(ctx, loc);
            let held = get_heap(state, heap);
            let perm = state.loc_kind(loc).and_then(|k| {
                let c = ctx
                    .chunk_under_pc(held.chunks_of(&k), addr, pc_lits)?
                    .clone();
                // Guarded-merge path: frame against the guard-gated perm (a
                // conditionally-held location frames only where its guard holds).
                let p = if !c.guard().is_empty() {
                    gate_perm_by_guard(ctx, &c.perm, c.guard())
                } else {
                    c.perm.clone()
                };
                Some(p)
            });
            match perm {
                // A bare (or absent) perm: the goal `0 < leaf` is discharged by
                // the caller exactly as before (flag-OFF byte-identical).
                None => {
                    let zero = zero_real(ctx);
                    let goal = ctx.add(Symbolic::Binary(BinOp::LtR, [zero, zero]));
                    vec![(goal, VerifyError::InsufficientPermission)]
                }
                Some(p @ ChunkPerm::Leaf(_)) => {
                    let leaf = p.as_leaf().unwrap();
                    let zero = zero_real(ctx);
                    let goal = ctx.add(Symbolic::Binary(BinOp::LtR, [zero, leaf]));
                    vec![(goal, VerifyError::InsufficientPermission)]
                }
                // A branch-structured held perm: prove `0 < perm` per leaf (never
                // materialize the `Select`). On success emit no goal; on failure a
                // trivially-false goal carries the error to the caller.
                Some(p) => {
                    if prove_perm_positive(ctx, &p, pc_lits) {
                        vec![]
                    } else {
                        let false_ = ctx.false_();
                        vec![(false_, VerifyError::InsufficientPermission)]
                    }
                }
            }
        }
        // `not(perm < 0)` desugared to an `Ite`. Applies to a location combine,
        // a resource inhale/exhale, and fold/unfold (their permission scale must
        // be ≥ 0 — a consuming op with a negative scale would flip
        // `heap_subtract` into permission fabrication).
        // A wildcard is positive by construction (assumed `0 < w` at creation),
        // and the e-graph has no real-order reasoning to *prove* `¬(w < 0)`.
        // Silicon likewise skips the non-negativity assertion for a constrainable
        // ARP (`PermissionSupporter.assertNotNegative`), so a wildcard-bearing
        // permission carries no `perm ≥ 0` obligation.
        InstKind::Heap(
            HeapInst::Combine { perm, .. }
            | HeapInst::Inhale { perm, .. }
            | HeapInst::Exhale { perm, .. }
            | HeapInst::Fold { perm, .. }
            | HeapInst::Unfold { perm, .. },
        ) if perm.has_wildcard() => vec![],
        InstKind::Heap(
            HeapInst::Combine { perm, .. }
            | HeapInst::Inhale { perm, .. }
            | HeapInst::Exhale { perm, .. }
            | HeapInst::Fold { perm, .. }
            | HeapInst::Unfold { perm, .. },
        ) => {
            let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
            let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
            let perm = eval_perm(ctx, state, perm);
            let zero = zero_real(ctx);
            let lt = ctx.add(Symbolic::Binary(BinOp::LtR, [perm, zero]));
            let goal = ctx.add(Symbolic::Ite([lt, false_, true_]));
            vec![(
                goal,
                VerifyError::SideCondition("permission may be negative"),
            )]
        }
        // `not(divisor == 0)` desugared to an `Ite`. The divisor is homogeneous
        // with the result (casts), so the VMIR result type gives the zero's type.
        InstKind::Pure(ty, PureInst::Binary(op, _, r)) if op.is_div_or_mod() => {
            let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
            let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
            let rv = state.get_val(ctx, r);
            let zero = zero_of(ctx, ty);
            let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [rv, zero]));
            let goal = ctx.add(Symbolic::Ite([eq, false_, true_]));
            vec![(goal, VerifyError::SideCondition("divisor may be zero"))]
        }
        _ => vec![],
    }
}

/// Zero literal of the given numeric type (`Real` fallback for non-numeric).
fn zero_of(ctx: &mut VerifyContext<'_>, ty: &Type) -> egg::Id {
    match ty {
        Type::Int => ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(0)))),
        _ => zero_real(ctx),
    }
}

#[cfg(test)]
mod e2e;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::lang::Symbolic;

    fn fresh_ctx<'a>(interner: &'a lasso::Rodeo) -> VerifyContext<'a> {
        // Leak a `'static` empty allocator, names table, and group interner so the
        // returned context can borrow them.
        let alloc: &'static mut _ =
            Box::leak(Box::new(crate::verify::func_registry::FuncRegistry::empty()));
        let decls: &'static _ = Box::leak(Box::new(typed_index_collections::TiVec::<
            vmir::MemberId,
            vmir::Declaration,
        >::new()));
        let groups: &'static _ = Box::leak(Box::new(lasso::Rodeo::<lasso::Spur>::new()));
        VerifyContext::new(interner, decls, groups, alloc)
    }

    fn real(ctx: &mut VerifyContext<'_>, n: i64, d: i64) -> egg::Id {
        ctx.add(Symbolic::Lit(Literal::Real(num::BigRational::new(
            num::BigInt::from(n),
            num::BigInt::from(d),
        ))))
    }

    /// An **unbounded** test location kind — like a predicate, it triggers no
    /// bound/non-aliasing axioms, so the merge/subtract unit tests exercise the
    /// chunk accounting in isolation (as the old non-`Addr` test addresses did).
    fn test_kind() -> LocationKind {
        LocationKind {
            group: <lasso::Spur as lasso::Key>::try_from_usize(0).unwrap(),
            value: Type::Int,
            bound: Bound::Unbounded,
        }
    }

    // A multi-arg bounded location (not Viper-reachable; only via direct VMIR):
    // two chunks of the same location whose perms sum > bound, with all args
    // forced equal, must contradict (the conjunction of arg-equalities collapses
    // to false against the assumed-true equalities).
    #[test]
    fn multiarg_location_nonaliasing_all_args_equal_is_inconsistent() {
        let interner = lasso::Rodeo::new();
        let decls = typed_index_collections::TiVec::<vmir::MemberId, vmir::Declaration>::new();
        let mut groups = lasso::Rodeo::<lasso::Spur>::new();
        let g = groups.get_or_intern("g");
        let mut alloc = crate::verify::func_registry::FuncRegistry::empty();
        let mut ctx = VerifyContext::new(&interner, &decls, &groups, &mut alloc);

        // A 2-arg bounded address group `g` of held type `Int`, cap `1/1`. The
        // address is an ordinary `FuncApp` to the group's address function
        // (`FuncId(0)` here); its `Addr{..}` return type is recorded in
        // `func_ret_types` (recovered by `location_chunks`).
        let addr_ty = Type::addr(
            g,
            Type::Int,
            Bound::Bounded(num::BigRational::from(num::BigInt::from(1))),
        );
        let addr_fn = crate::verify::lang::FuncId(0);
        let (x0, y0) = (ctx.add(Symbolic::Fresh(0)), ctx.add(Symbolic::Fresh(1)));
        let (x1, y1) = (ctx.add(Symbolic::Fresh(2)), ctx.add(Symbolic::Fresh(3)));
        let a0 = ctx.add_func_app_id(addr_fn, Box::new([]), addr_ty.clone(), Box::new([x0, y0]));
        let a1 = ctx.add_func_app_id(addr_fn, Box::new([]), addr_ty.clone(), Box::new([x1, y1]));
        let k = LocationKind::from_addr_type(&addr_ty).unwrap();
        let (v0, v1) = (ctx.add(Symbolic::Fresh(4)), ctx.add(Symbolic::Fresh(5)));
        let (p0, p1) = (real(&mut ctx, 3, 4), real(&mut ctx, 1, 2)); // sum 5/4 > 1
        let heap = Heap::empty()
            .with_chunk(&k, Chunk::new(a0, p0, v0))
            .with_chunk(&k, Chunk::new(a1, p1, v1));

        // Assume both argument pairs are equal: x0==x1, y0==y1.
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        for (a, b) in [(x0, x1), (y0, y1)] {
            let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [a, b]));
            ctx.union(eq, true_);
        }
        ctx.egraph.rebuild();

        assume_location_axioms(&mut ctx, &heap);
        ctx.saturate();
        assert!(
            ctx.is_inconsistent(),
            "holding 5/4 across a 2-arg location with all args equal must contradict"
        );
    }

    #[test]
    fn heap_union_merges_egg_equivalent_addresses() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p1, v1));
        ctx.union(a, b);
        ctx.egraph.rebuild();

        let merged = heap_union(&mut ctx, &h1, &test_kind(), Chunk::new(b, p2, v2), &[]);

        let canon = ctx.egraph.find(a);
        let chunk = merged
            .chunk(&test_kind(), canon)
            .expect("merged chunk missing");

        let expected_perm = ctx.add(Symbolic::Binary(BinOp::AddR, [p1, p2]));
        ctx.saturate();
        assert_eq!(ctx.egraph.find(chunk.perm.repr_id()), ctx.egraph.find(expected_perm));
        // Both fractions positive (1, 2) → agreement axiom fuses the values.
        assert_eq!(ctx.egraph.find(v1), ctx.egraph.find(v2));
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v1));
        assert_eq!(merged.entries().count(), 1);
    }

    // Two chunks inserted at *distinct* addresses whose classes collapse
    // later (an aliasing union learned after insertion): the consolidating
    // lookup must re-merge them so a subtract sees the full held amount —
    // first-match lookup only ever saw one 1/2 fragment and failed.
    #[test]
    fn subtract_consolidates_post_hoc_aliased_chunks() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let half = real(&mut ctx, 1, 2);
        let (v0, v1) = (ctx.add(Symbolic::Fresh(2)), ctx.add(Symbolic::Fresh(3)));
        let h = Heap::empty()
            .with_chunk(&test_kind(), Chunk::new(a, half, v0))
            .with_chunk(&test_kind(), Chunk::new(b, half, v1));
        assert_eq!(h.entries().count(), 2);

        // The aliasing fact arrives after both chunks are in the heap.
        ctx.union(a, b);
        ctx.egraph.rebuild();

        let one = real(&mut ctx, 1, 1);
        let out = heap_subtract(&mut ctx, &h, &test_kind(), Chunk::new(a, one, v0), &[])
            .expect("full permission is held across the two aliased fragments");
        // 1/2 + 1/2 − 1/1 = 0 const-folds → the emptied chunk is dropped.
        assert_eq!(out.entries().count(), 0);
    }

    // The borrow / give-back cycle: a chunk whose permission was reduced to
    // `1 − p` gets `p` unioned back in. The merged permission `(1 − p) + p`
    // must land back in `1/1`'s class (the cancellation rewrite), so the next
    // full-permission check is O(1) — the "regain full perm after a match arm"
    // shape, with `p = ite(c, 1, 0)` a branch-scaled borrow.
    #[test]
    fn give_back_restores_full_permission() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let c = ctx.add(Symbolic::Fresh(1));
        let one = real(&mut ctx, 1, 1);
        let zero = real(&mut ctx, 0, 1);
        let p = ctx.add(Symbolic::Ite([c, one, zero]));
        let rest = ctx.add(Symbolic::Binary(BinOp::SubR, [one, p]));
        let (v0, v1) = (ctx.add(Symbolic::Fresh(2)), ctx.add(Symbolic::Fresh(3)));

        let h = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, rest, v0));
        let out = heap_union(&mut ctx, &h, &test_kind(), Chunk::new(a, p, v1), &[]);
        let chunk = out
            .chunk(&test_kind(), ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();
        assert_eq!(
            ctx.egraph.find(chunk.perm.repr_id()),
            ctx.egraph.find(one),
            "(1 - p) + p must collapse back to the full permission"
        );
    }

    #[test]
    fn merge_zero_fraction_picks_active_value() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p0, v0));
        let merged = heap_union(&mut ctx, &h1, &test_kind(), Chunk::new(a, p1, v1), &[]);
        let chunk = merged
            .chunk(&test_kind(), ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();

        // p0 = 0 → asymmetric ternary picks the active half v1; no fusion.
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v1));
        assert_ne!(ctx.egraph.find(v0), ctx.egraph.find(v1));
    }

    #[test]
    fn merge_both_active_fuses_values() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p0, v0));
        let merged = heap_union(&mut ctx, &h1, &test_kind(), Chunk::new(a, p1, v1), &[]);
        let chunk = merged
            .chunk(&test_kind(), ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();

        // Both fractions positive → agreement axiom fuses the symbolic values.
        assert_eq!(ctx.egraph.find(v0), ctx.egraph.find(v1));
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v0));
    }

    #[test]
    fn merge_under_false_pc_blocks_fusion() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let false_lit = ctx.add(Symbolic::Lit(Literal::Bool(false)));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p0, v0));
        let merged = heap_union(
            &mut ctx,
            &h1,
            &test_kind(),
            Chunk::new(a, p1, v1),
            &[(false_lit, Polarity::Positive)],
        );
        let chunk = merged
            .chunk(&test_kind(), ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();

        // PC literal is `false` → implication collapses to its `true` fallback;
        // values must NOT fuse even though both fractions are positive.
        assert_ne!(ctx.egraph.find(v0), ctx.egraph.find(v1));
        // Value pick is independent of the PC gate.
        assert_eq!(ctx.egraph.find(chunk.value), ctx.egraph.find(v0));
    }

    #[test]
    fn merge_under_true_pc_allows_fusion() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p0 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v0 = ctx.add(Symbolic::Fresh(1));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let true_lit = ctx.add(Symbolic::Lit(Literal::Bool(true)));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p0, v0));
        let merged = heap_union(
            &mut ctx,
            &h1,
            &test_kind(),
            Chunk::new(a, p1, v1),
            &[(true_lit, Polarity::Positive)],
        );
        let _chunk = merged
            .chunk(&test_kind(), ctx.egraph.find(a))
            .expect("merged chunk missing");
        ctx.saturate();

        // PC literal is `true` + both fractions positive → agreement fires.
        assert_eq!(ctx.egraph.find(v0), ctx.egraph.find(v1));
    }

    #[test]
    fn prove_under_empty_pc_proves_known_goal() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let g = ctx.add(Symbolic::Fresh(0));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        ctx.union(g, true_);
        ctx.egraph.rebuild();

        // Goal already in the `true` eclass → proven under the empty PC.
        assert!(ctx.prove_under_pc(g, &[]));
    }

    #[test]
    fn prove_unknown_goal_fails() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        // A free boolean never driven to `true` is not provable.
        let g = ctx.add(Symbolic::Fresh(0));
        assert!(!ctx.prove_under_pc(g, &[]));
    }

    #[test]
    fn prove_under_false_pc_is_vacuous() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        // Unprovable goal, but the path is unsatisfiable (`false`).
        let g = ctx.add(Symbolic::Fresh(0));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        let false_lit = ctx.add(Symbolic::Lit(Literal::Bool(false)));

        assert!(ctx.prove_under_pc(g, &[(false_lit, Polarity::Positive)]));
        // The vacuous proof must NOT fuse the goal into `true` unconditionally.
        ctx.saturate();
        assert_ne!(ctx.egraph.find(g), ctx.egraph.find(true_));
    }

    #[test]
    fn prove_commits_conditional_implication() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let c = ctx.add(Symbolic::Fresh(0));
        let x = ctx.add(Symbolic::Fresh(1));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        // goal = `c ? true : x` — true under hypothesis `c`, unknown otherwise.
        let goal = ctx.add(Symbolic::Ite([c, true_, x]));

        // Provable under PC `<c>`; commits `c ==> goal` into the live graph.
        assert!(ctx.prove_under_pc(goal, &[(c, Polarity::Positive)]));

        // Not leaked unconditionally: `c` still unknown ⇒ goal not yet true.
        ctx.saturate();
        assert_ne!(ctx.egraph.find(goal), ctx.egraph.find(true_));

        // Once `c` is established, the goal collapses to `true`.
        ctx.union(c, true_);
        ctx.saturate();
        assert_eq!(ctx.egraph.find(goal), ctx.egraph.find(true_));
    }

    #[test]
    fn subtract_symbolic_perm_fails_without_proof() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p_have = ctx.add(Symbolic::Fresh(1));
        let p_take = ctx.add(Symbolic::Fresh(2));
        let v1 = ctx.add(Symbolic::Fresh(3));
        let v2 = ctx.add(Symbolic::Fresh(4));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p_have, v1));
        // Symbolic perms → `have >= take` not provable by equality saturation.
        let err = heap_subtract(&mut ctx, &h1, &test_kind(), Chunk::new(a, p_take, v2), &[])
            .err()
            .expect("symbolic-perm exhale must fail without a proof");
        assert!(matches!(
            err.root_cause(),
            VerifyError::InsufficientPermission
        ));
    }

    #[test]
    fn heap_subtract_canonical_match() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p2, v1));
        ctx.union(a, b);
        ctx.egraph.rebuild();

        let result = heap_subtract(&mut ctx, &h1, &test_kind(), Chunk::new(b, p1, v2), &[])
            .expect("subtract should succeed");

        let canon = ctx.egraph.find(a);
        let chunk = result
            .chunk(&test_kind(), canon)
            .expect("result chunk missing");
        let expected_perm = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        ctx.egraph.rebuild();
        assert_eq!(ctx.egraph.find(chunk.perm.repr_id()), ctx.egraph.find(expected_perm));
        assert_eq!(ctx.egraph.find(v1), ctx.egraph.find(v2));
    }

    #[test]
    fn heap_subtract_exact_match_drops_chunk() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p1, v1));
        let result = heap_subtract(&mut ctx, &h1, &test_kind(), Chunk::new(a, p1, v2), &[])
            .expect("subtract should succeed");

        let canon = ctx.egraph.find(a);
        assert!(
            result.chunk(&test_kind(), canon).is_none(),
            "zero-perm chunk must be dropped"
        );
    }

    #[test]
    fn heap_subtract_over_consume_fails() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let p2 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));
        let v2 = ctx.add(Symbolic::Fresh(3));

        let h1 = Heap::empty().with_chunk(&test_kind(), Chunk::new(a, p1, v1));
        let err = heap_subtract(&mut ctx, &h1, &test_kind(), Chunk::new(a, p2, v2), &[])
            .err()
            .expect("over-consumption must fail");
        assert!(matches!(
            err.root_cause(),
            VerifyError::InsufficientPermission
        ));
    }

    #[test]
    fn heap_subtract_missing_addr_fails() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let p1 = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let v1 = ctx.add(Symbolic::Fresh(2));

        let h1 = Heap::empty();
        let err = heap_subtract(&mut ctx, &h1, &test_kind(), Chunk::new(a, p1, v1), &[])
            .err()
            .expect("subtract from empty must fail");
        assert!(matches!(
            err.root_cause(),
            VerifyError::InsufficientPermission
        ));
    }

    #[test]
    fn const_fold_folds_subtraction() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let one = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into())));
        let diff = ctx.add(Symbolic::Binary(BinOp::SubR, [one, one]));
        ctx.egraph.rebuild();

        let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        assert_eq!(ctx.egraph.find(diff), ctx.egraph.find(zero));
    }

    #[test]
    fn const_fold_folds_ternary() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let cond = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        let t = ctx.add(Symbolic::Fresh(0));
        let e = ctx.add(Symbolic::Fresh(1));
        let ite = ctx.add(Symbolic::Ite([cond, t, e]));
        ctx.saturate();

        // `true ? t : e` collapses to the symbolic `t`.
        assert_eq!(ctx.egraph.find(ite), ctx.egraph.find(t));
        assert_ne!(ctx.egraph.find(ite), ctx.egraph.find(e));
    }

    #[test]
    fn rewrite_ite_false_picks_else() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let cond = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let t = ctx.add(Symbolic::Fresh(0));
        let e = ctx.add(Symbolic::Fresh(1));
        let ite = ctx.add(Symbolic::Ite([cond, t, e]));
        ctx.saturate();

        assert_eq!(ctx.egraph.find(ite), ctx.egraph.find(e));
        assert_ne!(ctx.egraph.find(ite), ctx.egraph.find(t));
    }

    #[test]
    fn rewrite_add_zero_int() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let x = ctx.add(Symbolic::Fresh(0));
        let zero = ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(0))));
        let sum = ctx.add(Symbolic::Binary(BinOp::AddI, [x, zero]));
        ctx.saturate();

        assert_eq!(ctx.egraph.find(sum), ctx.egraph.find(x));
    }

    #[test]
    fn rewrite_add_zero_real_commuted() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let x = ctx.add(Symbolic::Fresh(0));
        let zero = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
        // `0 + x` (commuted) must also fold to `x`.
        let sum = ctx.add(Symbolic::Binary(BinOp::AddR, [zero, x]));
        ctx.saturate();

        assert_eq!(ctx.egraph.find(sum), ctx.egraph.find(x));
    }

    #[test]
    fn eq_true_unions_args() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [a, b]));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        // `assume a == b` is modelled as unioning the equality with `true`.
        ctx.union(eq, true_);
        ctx.saturate();

        assert_eq!(ctx.egraph.find(a), ctx.egraph.find(b));
    }

    #[test]
    fn eq_unknown_does_not_union() {
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        // Build the equality but never prove it true.
        let _eq = ctx.add(Symbolic::Binary(BinOp::Eq, [a, b]));
        ctx.saturate();

        assert_ne!(ctx.egraph.find(a), ctx.egraph.find(b));
    }

    #[test]
    fn eq_true_propagates_through_congruence() {
        let mut interner = lasso::Rodeo::new();
        let f = crate::verify::lang::FuncId(lasso::Key::into_usize(interner.get_or_intern("f")));
        let mut ctx = fresh_ctx(&interner);

        let a = ctx.add(Symbolic::Fresh(0));
        let b = ctx.add(Symbolic::Fresh(1));
        let fa = ctx.add(Symbolic::FuncApp(f, Box::from([]), Box::from([a])));
        let fb = ctx.add(Symbolic::FuncApp(f, Box::from([]), Box::from([b])));
        let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [a, b]));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        ctx.union(eq, true_);
        ctx.saturate();

        // Unioning the args lets congruence close `f(a) == f(b)`.
        assert_eq!(ctx.egraph.find(fa), ctx.egraph.find(fb));
    }

    /// Build `d != 0` as `not(d == 0)` = `ite(d == 0, false, true)`, returning
    /// the e-class id (test helper, pure VMIR / e-graph level).
    fn ne_zero(ctx: &mut VerifyContext<'_>, d: egg::Id) -> egg::Id {
        let zero = ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(0))));
        let eq = ctx.add(Symbolic::Binary(BinOp::Eq, [d, zero]));
        let false_ = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let true_ = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        ctx.add(Symbolic::Ite([eq, false_, true_]))
    }

    #[test]
    fn realcast_folds_int_to_real() {
        // real(2) const-folds to the Real literal 2.
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);
        let two = ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(2))));
        let cast = ctx.add(Symbolic::RealCast(two));
        let real_two = ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(2).into())));
        ctx.saturate();
        assert_eq!(ctx.egraph.find(cast), ctx.egraph.find(real_two));
    }

    #[test]
    fn rewrite_and_true_collapses() {
        // b && true  =  ite(b, true, false)  =>  b
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);
        let b = ctx.add(Symbolic::Fresh(0));
        let t = ctx.add(Symbolic::Lit(Literal::Bool(true)));
        let f = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let ite = ctx.add(Symbolic::Ite([b, t, f]));
        ctx.saturate();
        assert_eq!(ctx.egraph.find(ite), ctx.egraph.find(b));
    }

    #[test]
    fn rewrite_and_self_collapses() {
        // b && b  =  ite(b, b, false)  =>  b
        let interner = lasso::Rodeo::new();
        let mut ctx = fresh_ctx(&interner);
        let b = ctx.add(Symbolic::Fresh(0));
        let f = ctx.add(Symbolic::Lit(Literal::Bool(false)));
        let ite = ctx.add(Symbolic::Ite([b, b, f]));
        ctx.saturate();
        assert_eq!(ctx.egraph.find(ite), ctx.egraph.find(b));
    }
}
