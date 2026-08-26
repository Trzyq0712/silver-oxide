use std::collections::HashMap;

use crate::verify::cert::PermRecipe;
use crate::vmir::display::VmirDisplay;
use crate::{
    verify::{
        cert::{FunctionDefinition, ResourceDefinition},
        context::VerifyContext,
        error::VerifyError,
        heap::{
            Chunk, ChunkPerm, Heap, LocationKind, cube_eq, gate_perm_by_guard,
            algebra::{
                Demand, chunk_under_pc, find_chunk_consolidated, heap_subtract, heap_union,
                merge_heaps, perm_held_at,
                prove_perm_positive, prove_perm_write, summarize_perm_at, union_heaps,
            },
        },
        lang::Symbolic,
        stats,
        viz::Snapshotter,
    },
    vmir::{
        self, Assign, BinOp, Declaration, Function, HeapInst, HeapVal, Inst, InstKind,
        Bind, Literal, MemberId, Method, PathConds, Polarity, PureInst, Resource, Type, Val,
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
    /// Permission temps (`p`), evaluated at their defining instruction. A `p`
    /// temp denotes ONE permission: a `wildcard` under it is minted once here, so
    /// reading the temp twice reads the same share.
    perms: Vec<ChunkPerm>,
    /// The defining instruction of each `perms` entry, kept in lockstep. The
    /// certificate walk needs the permission's *shape* (not its e-classes) to
    /// slice a [`PermRecipe`], and a `ChunkPerm` has already lost which operands
    /// it came from.
    perm_defs: Vec<vmir::PermInst>,
    /// Heap temps produced on a **provably unreachable** path (a block whose
    /// cube is refuted in the ground graph — e.g. after `bb_unreach`'s `inhale
    /// false`). The Stage-4 join merge drops such an arm outright instead of
    /// selecting a `0`-leaf against it (which would need an exhaustiveness
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
            perms: Vec::new(),
            perm_defs: Vec::new(),
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
            perms: Vec::new(),
            perm_defs: Vec::new(),
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

    /// The evaluation state a quantifier body starts from. Capture is implicit —
    /// the body indexes *this* table directly (see [`vmir::Forall`]) — so the frame
    /// is this state cut to `binder_base`, which is the `forall` step's own temp:
    /// the first binder takes that slot, so the step's own boolean is unnameable
    /// from inside. Heaps are dropped; a quantifier body is heap-free by
    /// construction.
    fn frame_for(&self, q: &vmir::Forall) -> Self {
        let mut frame = Self {
            vals: self.vals.clone(),
            val_types: self.val_types.clone(),
            recipes: self.recipes.clone(),
            heaps: Vec::new(),
            // A quantifier body is permission-free, like it is heap-free.
            perms: Vec::new(),
            perm_defs: Vec::new(),
            dead_heaps: std::collections::HashSet::new(),
        };
        // The step itself is not evaluated yet, so the table ends exactly at its
        // temp; the truncation is a no-op guard, not a cut.
        debug_assert!(frame.vals.len() >= q.binder_base);
        frame.vals.truncate(q.binder_base);
        frame.val_types.truncate(q.binder_base);
        frame.recipes.truncate(q.binder_base);
        frame
    }

    fn push_val(&mut self, id: egg::Id, ty: Type, recipe: Option<Val>) {
        self.vals.push(id);
        self.val_types.push(ty);
        self.recipes.push(recipe);
    }
    fn push_heap(&mut self, heap: Heap) {
        self.heaps.push(heap);
    }
    fn push_perm(&mut self, perm: ChunkPerm, def: vmir::PermInst) {
        self.perms.push(perm);
        self.perm_defs.push(def);
    }

    /// Whether a permission operand is wildcard-derived, without evaluating it.
    /// A `Temp` answers from its already-evaluated `ChunkPerm`, whose `wild` flag
    /// carries the provenance the e-graph cannot.
    fn perm_is_wild(&self, pv: &vmir::PermVal) -> bool {
        match pv {
            vmir::PermVal::Amount(_) => false,
            vmir::PermVal::Wildcard => true,
            vmir::PermVal::Temp(i) => self.perms[*i].has_wild(),
        }
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
        (val_base, heap_base, 0usize, std::slice::from_ref(inst)),
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
            HeapInst::Add { base, .. }
            | HeapInst::Sub { base, .. }
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
/// is the path condition of the owning instruction. A `Deref` consults it to
/// resolve an address that only aliases a held chunk under the branch (e.g.
/// `y.f` where `x == y` holds on this path); a `FunctionCall` assumes the
/// callee's `f%pre` token under it (the token's truth is what releases the
/// callee's body equality and exported facts). Every other variant ignores it.
///
/// `recipe_pc` is the *same* path condition before lowering, needed only when a
/// recipe is being built: a propagated `g%pre` token records it in recipe space
/// (via [`EvalState::recipe_pc`]) so the token is released only under the
/// body-internal condition guarding its call. `None` where no recipe-space pc can
/// be recovered — a trusted axiom body, or a `forall` WD check whose pc is the
/// concatenation `host_pc ++ inst.pc` with the host half already lowered to ids.
/// `None` records empty guards, i.e. exactly the pre-guard behavior: it can only
/// release a token too eagerly, never too late, so it cannot mask a real failure.
fn eval_pure_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    ty: &Type,
    pi: &PureInst,
    pc_lits: &[(egg::Id, Polarity)],
    recipe_pc: Option<&PathConds>,
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
            let id = expr!(ctx, if {cond} then {then_} else {else_});
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
                chunk_under_pc(ctx, heap.chunks_of(&k), addr, pc_lits)
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
            // Just add the uninterpreted application, for abstract, heap-free and
            // heap-dependent callees alike. A verified callee's definitional
            // equality `f(args) == body` is installed lazily by its own
            // `rewrite::function_rule`, not eagerly here.
            let args: Vec<egg::Id> = fc.args.iter().map(|v| state.get_val(ctx, v)).collect();
            let func_id = crate::verify::func_registry::func_id_for_member(fc.function);
            let id = ctx.add_func_app_id(
                func_id,
                fc.type_args.clone().into(),
                ty.clone(),
                args.clone().into(),
            );
            // Silicon's `f%pre`, assumed only at call sites. Every genuine
            // value-position call mints the callee's `f%pre(args)` token node,
            // whose *presence* lets `rewrite::function_rule` materialize the
            // callee's body here, and whose *truth* is what releases the resulting
            // axioms (`tok ==> f == body`, `tok ==> each exported fact`). The one
            // non-value position is a **contract-function body** (a lowered
            // pre/post), handled below.
            //
            // The truth is assumed under this call's path condition, so a call
            // under a ternary/implication cannot release the callee's facts onto a
            // sibling intra-block path. This is the only place a pc enters the
            // function-unfold encoding; every axiom above inherits it transitively
            // through the token. `.rev()` because `pc_lits` is outermost-first and
            // `implication` folds innermost-first (cf. `InstKind::Assume`).
            {
                let name = ctx.member_name(fc.function);
                let tok = ctx.alloc.fn_pre_token(fc.function, &name);
                let tok_id = ctx.add(Symbolic::FuncApp(tok, Box::new([]), args.into()));
                ctx.assume_token_guarded(tok_id, pc_lits.iter().rev().copied());
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
                    let tok = rb.emit(AxiomPure::App {
                        func: g_pre,
                        type_args: Vec::new(),
                        args,
                    });
                    // The callee-internal pc of *this* call, in recipe space: the
                    // release becomes `f%pre(a) ==> (pc[x:=a] ==> g%pre(gargs))`, so
                    // a conditionally-called callee's axioms do not fire at args the
                    // body never calls it at.
                    let guards = match recipe_pc {
                        Some(pc) => state.recipe_pc(pc)?,
                        None => Vec::new(),
                    };
                    // The token's value is never consumed, so `RecipeBuilder::slice`
                    // would prune it as unreachable from the result. Register it as
                    // a slice root.
                    rb.record_token_step(tok, guards);
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
            // Compile the quantifier the first time the walk reaches it. Its
            // capture list is derived, not stored — see `Forall::free_temps`.
            // Name resolution rides on copies of the two shared refs, so it does
            // not borrow `ctx` across the `&mut ctx.alloc`.
            let (interner, decls) = (ctx.interner, ctx.decls);
            let names = move |m| crate::verify::context::member_name_in(interner, decls, m);
            let (recipe_id, free) =
                crate::verify::quant::intern_forall(ctx.alloc, &names, q)?;
            let free: Vec<Val> = free.iter().map(|&k| Val::Temp(k)).collect();
            let caps: Box<[egg::Id]> = free.iter().map(|v| state.get_val(ctx, v)).collect();
            let id = ctx.add(Symbolic::Forall(recipe_id, caps));
            let recipe = if ctx.recipe.is_some() {
                let caps: Vec<Val> = free
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
        // `unwrap(v)`: the `Some` payload of an `Option`. The result type IS the
        // element type, so it needs no type argument. A certificate walk mirrors
        // the projection, exactly as a footprint slot's `unwrap(proj_i(s))` does.
        PureInst::OptionUnwrap(v) => {
            let opt = state.get_val(ctx, v);
            let id = ctx.option_unwrap(ty.clone(), opt);
            let recipe = if ctx.recipe.is_some() {
                let vr = state.require_recipe(v, OPERAND_RECIPE)?;
                let unwrap_id = ctx.alloc.option_value();
                let rb = ctx.recipe.as_mut().unwrap();
                Some(rb.emit(crate::verify::rewrite::AxiomPure::App {
                    func: unwrap_id,
                    type_args: vec![ty.clone()],
                    args: vec![vr],
                }))
            } else {
                None
            };
            (id, recipe)
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
            let id = match state.loc_kind(loc) {
                Some(k) => {
                    let chunks = heap.chunks_of(&k).to_vec();
                    perm_held_at(ctx, &chunks, addr, pc_lits)
                }
                None => expr!(ctx, 0/1),
            };
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

fn heap_acc(ctx: &mut VerifyContext<'_>, loc: &Val, perm: ChunkPerm, state: &EvalState) -> Heap {
    let addr = state.get_val(ctx, loc);
    // The location kind (group + held value type + bound) comes straight from the
    // address operand's VMIR `Type::Addr` — no e-graph inference.
    let kind = state
        .loc_kind(loc)
        .expect("acc location must be Addr-typed");
    let value = ctx.fresh_symbolic_value(kind.value.clone());
    Heap::empty().with_chunk(&kind, Chunk::new_perm(addr, perm, value))
}

/// Resolve a [`vmir::PermVal`] to its e-class id, minting a fresh positive share
/// for a bare `wildcard`. A concrete `Amount` is exactly the value it wraps, so a
/// non-wildcard program builds the same term it always did.
///
/// A `Temp` was evaluated at its defining instruction, so it costs a lookup and
/// mints nothing: a `p` temp denotes one permission however many times it is read.
fn eval_perm(ctx: &mut VerifyContext<'_>, state: &EvalState, perm: &vmir::PermVal) -> egg::Id {
    eval_perm_structural(ctx, state, perm).to_id(ctx)
}

/// [`eval_perm`], but keeping the permission's **branch structure** as a
/// [`ChunkPerm`] instead of flattening it into one `Ite` term — the method-body
/// twin of [`build_perm`], which does the same for a footprint slot.
///
/// The term is identical either way (`ChunkPerm::to_id` rebuilds exactly the `Ite`
/// this used to add); what differs is that the structure is visible ABOVE the
/// e-graph, so a consume can align the demand's arms against the held permission's
/// (`prove_sufficient_aligned`, `perm_sub_aligned`) rather than proving against an
/// opaque `ite`. Without this, `exhale c ==> acc(x.f)` in a *method* stays opaque
/// even though the same assertion inside a predicate does not.
///
/// `ChunkPerm::select` is the smart constructor, so an ungated permission still
/// builds exactly the `Leaf` it did before.
fn eval_perm_structural(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    perm: &vmir::PermVal,
) -> ChunkPerm {
    match perm {
        vmir::PermVal::Amount(v) => ChunkPerm::leaf(state.get_val(ctx, v)),
        vmir::PermVal::Wildcard => ChunkPerm::wild_leaf(ctx.fresh_wildcard()),
        vmir::PermVal::Temp(i) => state.perms[*i].clone(),
    }
}

/// Evaluate a permission *instruction*, the definition of a `p` temp. The one
/// place a permission gains branch structure in a method body.
fn eval_perm_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    inst: &vmir::PermInst,
) -> ChunkPerm {
    match inst {
        vmir::PermInst::Ite(c, t, e) => {
            let c = state.get_val(ctx, c);
            let t = eval_perm_structural(ctx, state, t);
            let e = eval_perm_structural(ctx, state, e);
            ChunkPerm::select(ctx, c, t, e)
        }
    }
}

/// Which consume rule a permission demand selects. Read off the *evaluated*
/// permission's provenance, which `ChunkPerm::Leaf`'s `wild` flag carries
/// structurally -- not recognised in the e-graph after the fact, where congruence
/// can put a wildcard-bearing term into a literal's class. See [`Demand`].
fn demand_of(perm: &ChunkPerm) -> Demand {
    if perm.has_wild() {
        Demand::Wildcard
    } else {
        Demand::Concrete
    }
}

/// The recipe-space form of a footprint-slot permission (resource certificate
/// build): the `p` steps the slot's permission reaches, in dependency order, with
/// each operand replaced by its recipe temp.
///
/// Deliberately *not* flattened into pure steps — see [`PermRecipe`] for why the
/// `wildcard` must stay out of a rebuilt step stream.
///
/// The walk memoizes per body temp, so a permission read twice yields one step and
/// hence one wildcard at graft time, matching what the IR says: a `p` temp is one
/// permission.
fn perm_recipe(state: &EvalState, perm: &vmir::PermVal) -> Result<PermRecipe<Val>, VerifyError> {
    fn leaf(
        state: &EvalState,
        pv: &vmir::PermVal,
        steps: &mut Vec<vmir::PermInst<Val>>,
        memo: &mut HashMap<usize, usize>,
    ) -> Result<vmir::PermVal<Val>, VerifyError> {
        Ok(match pv {
            vmir::PermVal::Amount(v) => {
                vmir::PermVal::Amount(state.require_recipe(v, OPERAND_RECIPE)?)
            }
            vmir::PermVal::Wildcard => vmir::PermVal::Wildcard,
            vmir::PermVal::Temp(i) => {
                if let Some(j) = memo.get(i) {
                    return Ok(vmir::PermVal::Temp(*j));
                }
                let vmir::PermInst::Ite(c, t, e) = &state.perm_defs[*i];
                let t = leaf(state, t, steps, memo)?;
                let e = leaf(state, e, steps, memo)?;
                let c = state.require_recipe(c, OPERAND_RECIPE)?;
                steps.push(vmir::PermInst::Ite(c, t, e));
                let j = steps.len() - 1;
                memo.insert(*i, j);
                vmir::PermVal::Temp(j)
            }
        })
    }
    let mut steps = Vec::new();
    let mut memo = HashMap::new();
    let res = leaf(state, perm, &mut steps, &mut memo)?;
    Ok(PermRecipe { steps, res })
}

/// What a `wildcard` leaf becomes when a footprint slot's permission is grafted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WildcardAs {
    /// A freshly minted positive share (`0 < w` assumed) — the real permission.
    Fresh,
    /// Full permission `1`, so a gated wildcard builds the slot's **presence**
    /// indicator `ite(guard, 1, 0)` whose `0 < …` folds to `guard`. Used by a
    /// frame-only exhale, which needs presence but no amount: building the wildcard
    /// would leave un-collapsible `ite` residue in the persistent graph for
    /// `ite-reduce` to churn on.
    One,
}

/// Graft a footprint slot's permission: [`eval_perm_structural`]'s descent, over a
/// slot recipe instead of an [`EvalState`]. One wildcard is picked per `wildcard`
/// **leaf** reached, eagerly — a leaf under a false guard still mints, and the
/// enclosing `ite` discards it.
///
/// Keeps the **branch structure** as a [`ChunkPerm`] rather than flattening it into
/// one `Ite` term.
///
/// The structure is what lets a consume align the demand's arms against the held
/// permission's (see `heap_subtract`): `ChunkPerm::restrict` takes the matching arm
/// when both branch on the same condition and carries the whole term in otherwise, so
/// precision falls out of the shapes agreeing rather than out of any case analysis
/// here. Flattened into an `Ite`, that structure survives only inside the e-graph term
/// and the consume cannot see it.
///
/// `ChunkPerm::select` is the smart constructor: it flattens arms branching on the
/// same condition, collapses `then ≡ els`, and drops an arm whose condition
/// const-folds — so a wildcard-free program still builds exactly what it did before.
fn build_perm(
    ctx: &mut VerifyContext<'_>,
    perm: &PermRecipe,
    resolve: &impl Fn(&crate::verify::cert::SeedRef) -> egg::Id,
    changed: &mut Vec<egg::Id>,
    wildcard_as: WildcardAs,
) -> ChunkPerm {
    fn leaf(
        ctx: &mut VerifyContext<'_>,
        pv: &vmir::PermVal<crate::verify::cert::BodyRecipe>,
        built: &[ChunkPerm],
        resolve: &impl Fn(&crate::verify::cert::SeedRef) -> egg::Id,
        changed: &mut Vec<egg::Id>,
        wildcard_as: WildcardAs,
    ) -> ChunkPerm {
        match pv {
            vmir::PermVal::Amount(r) => {
                ChunkPerm::leaf(r.build(&mut ctx.egraph, resolve, changed))
            }
            // `WildcardAs::One` builds a **presence** indicator, not a share: it is
            // the literal `1`, with no wildcard left in it, so the leaf is concrete.
            vmir::PermVal::Wildcard => match wildcard_as {
                WildcardAs::Fresh => ChunkPerm::wild_leaf(ctx.fresh_wildcard()),
                WildcardAs::One => ChunkPerm::leaf(
                    ctx.add(Symbolic::Lit(Literal::Real(num::BigInt::from(1).into()))),
                ),
            },
            // A step only names earlier ones, so this is always already built.
            vmir::PermVal::Temp(i) => built[*i].clone(),
        }
    }
    let mut built: Vec<ChunkPerm> = Vec::with_capacity(perm.steps.len());
    for step in &perm.steps {
        let vmir::PermInst::Ite(c, t, e) = step;
        let c = c.build(&mut ctx.egraph, resolve, changed);
        let t = leaf(ctx, t, &built, resolve, changed, wildcard_as);
        let e = leaf(ctx, e, &built, resolve, changed, wildcard_as);
        built.push(ChunkPerm::select(ctx, c, t, e));
    }
    leaf(ctx, &perm.res, &built, resolve, changed, wildcard_as)
}

/// Scale every leaf of a permission by `pm`, preserving the branch structure.
///
/// Distributing rather than wrapping (`ite(c, pm*t, pm*e)` over `pm * ite(c, t, e)`)
/// is what keeps the `ChunkPerm` tree intact through an `unfolding`'s multiplier. The
/// two are equal but not identical; `mul-one-real-l` puts them in one class once the
/// slot's `ctx.reduce()` runs, which is why the common `1/1` scale costs nothing.
fn scale_perm(ctx: &mut VerifyContext<'_>, pm: egg::Id, pm_wild: bool, perm: ChunkPerm) -> ChunkPerm {
    match perm {
        // A wildcard *scale* (an `unfolding` inside a function body) makes every
        // scaled leaf wildcard-derived, whatever the slot's own amount was.
        ChunkPerm::Leaf { id, wild } => ChunkPerm::Leaf {
            id: ctx.add(Symbolic::Binary(BinOp::MulR, [pm, id])),
            wild: wild || pm_wild,
        },
        ChunkPerm::Select { cond, then, els } => {
            let t = scale_perm(ctx, pm, pm_wild, *then);
            let e = scale_perm(ctx, pm, pm_wild, *els);
            ChunkPerm::select(ctx, cond, t, e)
        }
    }
}
































/// Invariant 6 of the two-egraph block model (`design/block-vmir/82-*.md`):
/// statement-level heap instructions operate at the **block-PC level only** — their
/// `inst.pc` is exactly the block cube, never a cube plus a suffix — because they
/// cannot appear as sub-expressions. Expression-embedded obligations (a function
/// precondition, a division check) are the only things allowed an extra suffix.
///
/// A violation means a heap effect landing under a condition the block model does
/// not know about. Gated on `SILVER_OXIDE_ASSERT_BLOCK_PC` so it can be run over
/// the corpus in release builds, where a `debug_assert` would compile out.
///
/// Known violating shape: `unfolding p in e` is a Viper *expression* but lowers to
/// statement-level instructions, so it can sit under an extra ternary guard. Since the
/// fold/unfold desugaring it is the pair's *resource* half that carries the shape --
/// the slot halves are sub-statement and were never listed -- so it is still caught,
/// just through a different variant. Plan 82 proposes rejecting it until it becomes a
/// scoped node.
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
            HeapInst::Inhale { .. } | HeapInst::Exhale { .. } | HeapInst::Assign(..)
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






/// Evaluate a heap inst. `Sub` may fail with `InsufficientPermission`.
fn eval_heap_inst(
    ctx: &mut VerifyContext<'_>,
    state: &EvalState,
    inst: &HeapInst,
    pc: &PathConds,
) -> Result<Heap, VerifyError> {
    match inst {
        // Heap SUM: both heaps are held at once, so permissions at a shared
        // location add and values there must agree. Contrast `Merge`, which
        // selects between mutually exclusive predecessor states.
        HeapInst::Union { a, b } => {
            let ha = get_heap(state, a).clone();
            let hb = get_heap(state, b).clone();
            // The block cube is load-bearing here, not decorative: a loop exit's
            // union runs under `<!guard>`, and both the positivity decision and the
            // guarded value equality have to be relative to it.
            let pc_lits: Vec<(egg::Id, Polarity)> = pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            Ok(union_heaps(ctx, &ha, &hb, &pc_lits))
        }
        // Block-IR heap join: structural per-chunk SELECT of the two predecessor
        // exit heaps. Emitted at every CFG join by the block lowering.
        HeapInst::Merge {
            cond,
            then_h,
            els_h,
        } => {
            // An unreachable predecessor arm (its cube refuted, e.g. the enum
            // `bb_unreach` after `inhale false`) is dropped outright — selecting
            // a `0`-leaf against it would need an exhaustiveness case split.
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
        HeapInst::Add {
            base, loc, perm, ..
        }
        | HeapInst::Sub {
            base, loc, perm, ..
        } => {
            // `Add` carries a `Bind`; `Sub` is read-shaped and carries none.
            let bind = match inst {
                HeapInst::Add { bind, .. } => Some(bind),
                _ => None,
            };
            let base_h = get_heap(state, base);
            let cperm = eval_perm_structural(ctx, state, perm);
            let chunk = heap_acc(ctx, loc, cperm.clone(), state);
            let pc_lits: Vec<(egg::Id, Polarity)> = pc
                .conds
                .iter()
                .map(|(v, p)| (state.get_val(ctx, v), *p))
                .collect();
            let (kind, ch) = chunk.entries().next().unwrap();
            let (kind, mut ch) = (kind.clone(), ch.clone());
            if let Some(bind) = bind {
                {
                    // The bind selects the value source. `Fresh` and `SelfSlot`
                    // agree on the *value* today — `heap_acc` mints a fresh
                    // symbolic either way — and differ only in provenance: a
                    // resource body's slot records a `SlotValue(i)` seed that is
                    // resolved at graft time by whatever the caller passed. So
                    // this reads the bind rather than inferring the context, but
                    // is behavior-preserving.
                    match bind {
                        // A resource body's footprint slot. Recorded below.
                        Bind::SelfSlot => debug_assert!(
                            ctx.recipe.is_some(),
                            "`with self` outside a resource-body (certificate) walk"
                        ),
                        // A method-body produce: an unconstrained value, and no
                        // certificate is under construction to record it in.
                        Bind::Fresh => debug_assert!(
                            ctx.recipe.is_none(),
                            "`with fresh` inside a resource body — a body that \
                             mints an observable value is not deterministic"
                        ),
                        // The produce half of a desugared `fold`: the chunk
                        // holds the snapshot the paired `exhale` handed back,
                        // rather than a fresh value. That shared term IS the
                        // equation `snap(P(x)) = cons(body)` -- the binding the
                        // dedicated `Fold` instruction had to preserve is now
                        // emergent from naming the same `Val` twice.
                        Bind::Bound(v) => {
                            let bound = state.get_val(ctx, v);
                            ch = Chunk::new_perm(ch.addr, cperm.clone(), bound)
                                .with_recipe(state.recipe_of(v));
                        }
                    }
                    // A resource body's `acc` records a footprint slot in the
                    // certificate under construction: its value is the seed
                    // placeholder `SlotValue(i)` (supplied at graft time), its
                    // address/permission recipes are sliced at the end of the
                    // walk. The seed doubles as the chunk's recipe provenance,
                    // so a later `Deref` purifies to the slot value.
                    if ctx.recipe.is_some() {
                        let addr_r = state.require_recipe(loc, OPERAND_RECIPE)?;
                        let perm_r = perm_recipe(state, perm)?;
                        let elem = kind.value.clone();
                        let rb = ctx.recipe.as_mut().unwrap();
                        let i = rb.pending_slots.len();
                        let seed = rb.emit_seed(crate::verify::cert::SeedRef::SlotValue(i));
                        rb.pending_slots.push((kind.clone(), elem, addr_r, perm_r));
                        ch = ch.with_recipe(Some(seed));
                    }
                    Ok(heap_union(ctx, &base_h, &kind, ch, &pc_lits))
                }
            } else {
                if ctx.recipe.is_some() {
                    return Err(VerifyError::Unimplemented(
                        "purify: unsupported heap inst in a resource body",
                    ));
                }
                heap_subtract(ctx, &base_h, &kind, ch, &pc_lits, demand_of(&cperm))
            }
        }
        // Resource inhale/exhale need the program + certificates; method-only.
        HeapInst::Inhale { .. } | HeapInst::Exhale { .. } => Err(VerifyError::Unimplemented(
            "resource inhale/exhale outside method body",
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
                .map(|c| c.ungated_perm().clone())
                .unwrap_or_else(|| ChunkPerm::leaf(expr!(ctx, 0/1)));
            let guard = held
                .as_ref()
                .map(|c| c.guard_pc())
                .unwrap_or_else(|| std::rc::Rc::from(Vec::new()));
            // SIDECOND: prove `not(perm < cap)` (full/write permission, `cap` =
            // the location's own permission bound, `1/1` for a field) under pc —
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
            if !prove_perm_write(ctx, &proof_perm, &kind.bound, &pc_lits) {
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
        InstKind::Pure(ty, pi) => {
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
            let (id, recipe) = eval_pure_inst(ctx, state, ty, pi, &pc_lits, Some(&inst.pc))?;
            state.push_val(id, ty.clone(), recipe);
        }
        // The consume half of a desugared `unfold`: yields what it removed.
        InstKind::Heap(HeapInst::Sub {
            yields_value: true, ..
        }) => {
            eval_sub_yield(ctx, state, inst, &inst.pc)?;
        }
        // A heap-dependent function call's implicit precondition check, which
        // may appear in a contract body. Non-consuming, so it is legal here where
        // a consuming resource op is not.
        InstKind::Heap(HeapInst::Exhale {
            frame_only: true, ..
        }) => {
            eval_resource_op(ctx, program, state, inst, certs)?;
        }
        // The entry of a two-state resource body: reconstruct the pre-state
        // heap from the snapshot parameter (implicitly assuming the precondition
        // resource's boolean). A *bound* inhale, so it reconstructs rather than
        // havocs.
        InstKind::Heap(HeapInst::Inhale {
            bind: Bind::Bound(_),
            ..
        }) => {
            let heap = eval_from_snap(ctx, program, state, inst, certs)?;
            state.push_heap(heap);
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, &inst.pc)?;
            state.push_heap(heap);
        }
        InstKind::Perm(pi) => {
            let p = eval_perm_inst(ctx, state, pi);
            state.push_perm(p, pi.clone());
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
        InstKind::Pure(ty, pi) => {
            let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
            let (id, recipe) = eval_pure_inst(ctx, state, ty, pi, &pc_lits, Some(&inst.pc))?;
            state.push_val(id, ty.clone(), recipe);
        }
        // `base inhale <resource>(args) perm`: produce the resource's footprint
        // (fresh values), scaled by `perm`, into `base` and **assume** its
        // boolean; `base exhale ...` consumes the footprint from `base` and
        // **asserts** it. A self-framed callee additionally yields the snapshot
        // of its footprint as a pure `Val` (the pre-state handle a two-state call
        // receives). Both route through `walk_footprint`.
        // The consume half of a desugared `unfold`: yields what it removed.
        InstKind::Heap(HeapInst::Sub {
            yields_value: true, ..
        }) => {
            eval_sub_yield(ctx, state, inst, &inst.pc)?;
        }
        InstKind::Heap(HeapInst::Inhale { .. } | HeapInst::Exhale { .. }) => {
            eval_resource_op(ctx, program, state, inst, certs)?;
        }
        InstKind::Heap(hi) => {
            let heap = eval_heap_inst(ctx, state, hi, &inst.pc)?;
            state.push_heap(heap);
        }
        InstKind::Perm(pi) => {
            let p = eval_perm_inst(ctx, state, pi);
            state.push_perm(p, pi.clone());
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
                if std::env::var_os("SILVER_OXIDE_TRACE_ASSERT").is_some() {
                    eprintln!(
                        "[assert-fail] Assert inst, pc={} lits:\n{}",
                        pc_lits.len(),
                        crate::verify::viz::dump_term(ctx, id, 40),
                    );
                }
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
/// the snapshot members `present ? Some(v) : None` per slot, and — during a
/// certificate walk — each slot value's recipe term. Members are filled for
/// **both** directions: the `members.push` in the slot loop is unconditional, so
/// a `Produce` walk conses a snapshot exactly as a `Consume` walk does.
struct FootprintResult {
    heap: Heap,
    members: Vec<egg::Id>,
    /// Recipe provenance of each slot value, in slot order (certificate walks
    /// only; all `None` otherwise).
    slot_recipes: Vec<Option<Val>>,
}

/// A footprint slot's permission as built for the current walk: either the real
/// `Amount` (drives the heap effect), or, for a wildcard slot at a `Snap`, a
/// `Presence` indicator `ite(guard, 1, 0)` standing in for the wildcard (drives
/// only the snapshot member + a "holds a positive share" sufficiency prove).
enum SlotPerm {
    Amount(ChunkPerm),
    Presence(ChunkPerm),
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
    // `scale_wild`: whether `scale` itself came from a `wildcard` (an `unfolding`
    // in a function body), which makes every scaled leaf wildcard-derived.
    scale_wild: bool,
    pc_lits: &[(egg::Id, Polarity)],
    // The guard under which the body boolean is discharged (asserted for
    // `Consume`, assumed for `Produce`). Usually `pc_lits`; an `inhale` passes
    // `[0 < scale]` since it carries no path condition.
    bool_guard: &[(egg::Id, Polarity)],
    // A **frame-only** exhale (a heap-dependent function call's implicit
    // precondition check): a bare-wildcard footprint slot skips building the
    // wildcard perm and subtracting — sufficiency becomes a "holds a positive
    // share" prove, presence is unconditional. Keeps the wildcard `ite` residue
    // (which `ite-reduce` churns on) out of the persistent e-graph. `false` for
    // the consuming/producing walks.
    //
    // This was `is_snap` while `PureInst::Snap` existed. Stage 3b turned that
    // into a frame-only exhale and the flag became a second name for the same
    // bit — its one `true` caller passes `frame_only` — so it is now that bit.
    frame_only: bool,
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
        // before we look it up: an address reaching through a snapshot
        // (`Pt(f(r, cons(Some(unwrap(proj_0(s))))))`) only becomes e-class-equal to
        // the held chunk's address once `proj∘cons` / `unwrap∘Some` have fired.
        //
        // Reduce only when the rebuild actually introduced something to reduce: the
        // recipe is add-only, so if `build` added no e-node then every term it named
        // was already present, hence already normalized. Reducing unconditionally
        // per slot re-runs the ADT rule set over the whole graph and costs ~3.5x.
        // A wildcard slot at a frame-only exhale (bare or gated): build its
        // **presence** indicator rather than the wildcard perm — the same shape with
        // the wildcard leaf built as full permission `1`, so `ite(guard, 1, 0)`
        // whose `0 < …` folds to the gating guard.
        // The slot's permission shape is also the static source for the consume rule
        // its demand selects, at the `SlotPerm::Amount` consume below -- see
        // [`Demand`]. Shape-only, so it is the same predicate the IR side asks.
        let slot_wildcard = slot.perm.has_wildcard();
        let slot_demand = if slot_wildcard {
            Demand::Wildcard
        } else {
            Demand::Concrete
        };
        let wc_slot = frame_only && slot_wildcard;
        let before = ctx.egraph.total_number_of_nodes();
        let addr = slot.addr.build(&mut ctx.egraph, resolve, &mut changed);
        let wildcard_as = if wc_slot {
            WildcardAs::One
        } else {
            WildcardAs::Fresh
        };
        let bperm = {
            let p = build_perm(ctx, &slot.perm, &resolve, &mut changed, wildcard_as);
            if wc_slot {
                SlotPerm::Presence(p)
            } else {
                SlotPerm::Amount(p)
            }
        };
        if ctx.egraph.total_number_of_nodes() != before {
            ctx.reduce();
        }
        let addr = ctx.egraph.find(addr);
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
                    Some(pm) => scale_perm(ctx, pm, scale_wild, bperm.clone()),
                    None => bperm.clone(),
                };
                let chunk = Chunk::new_perm(addr, p, value).with_recipe(recipe.clone());
                heap = match direction {
                    Direction::Consume => {
                        heap_subtract(ctx, &heap, &slot.kind, chunk, pc_lits, slot_demand)?
                    }
                    Direction::Produce => heap_union(ctx, &heap, &slot.kind, chunk, pc_lits),
                };
                let bperm_id = bperm.to_id(ctx);
                expr!(ctx, (0/1) <r {bperm_id})
            }
            // Wildcard `Snap` slot: no heap effect (Snap frames). Presence is the
            // gating guard `0 < ite(guard, 1, 0)` (folds to `guard`, `true` when
            // unconditional). Sufficiency: where the slot is required, the caller
            // must hold a positive share — prove `guard ⇒ 0 < held` against the
            // caller's (concrete) held permission; no wildcard is ever built.
            SlotPerm::Presence(pp) => {
                let pp = pp.to_id(ctx);
                let guard = expr!(ctx, (0/1) <r {pp});
                let (_, existing) =
                    find_chunk_consolidated(ctx, &heap, &slot.kind, addr, pc_lits, true);
                let suff = match existing {
                    Some(c) => {
                        // `guard ⇒ 0 < held`, proven per leaf (never materialize
                        // the held `Select`): assume `guard` in the pc, prove
                        // `0 < leaf` on each branch. Gated, so presence is
                        // respected: a conditionally-held slot frames only where
                        // its guard holds.
                        let held = c.gated_perm(ctx);
                        let mut pc = pc_lits.to_vec();
                        pc.push((guard, Polarity::Positive));
                        prove_perm_positive(ctx, &held, &pc)
                    }
                    // No chunk held here: sound only if the slot is not required
                    // on this path (`guard` is false).
                    None => {
                        let not_guard = expr!(ctx, not {guard});
                        ctx.prove_under_pc(not_guard, pc_lits)
                    }
                };
                // Last resort, the framing twin of what `heap_subtract_inner` does
                // on a miss: no chunk matched this address on ground (or the one
                // that did could not be shown positive), but another chunk of the
                // group may sit here — under an equality the pc does not mention,
                // or under its own presence guard, which is the `&mut`-reborrow
                // shape. Summarize the group at `addr` and ask for positivity per
                // leaf. Reached only by a check that would otherwise fail, so no
                // framing check that succeeds outright pays for it.
                let suff = suff || {
                    let chunks = heap.chunks_of(&slot.kind).to_vec();
                    let (total, set) = summarize_perm_at(ctx, &chunks, addr, pc_lits);
                    let mut pc = pc_lits.to_vec();
                    pc.push((guard, Polarity::Positive));
                    !set.is_empty() && prove_perm_positive(ctx, &total, &pc)
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
                if std::env::var_os("SILVER_OXIDE_TRACE_ASSERT").is_some() {
                    eprintln!(
                        "[assert-fail] resource-bool consume, pc={} lits:\n{}",
                        bool_guard.len(),
                        crate::verify::viz::dump_term(ctx, bool_id, 40),
                    );
                }
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

/// Evaluate a **value-yielding** `Sub`: remove the chunk at `loc` and hand back
/// what was there, as `Option<T>` (`None` iff nothing was removed).
///
/// This is the consume half of a desugared `unfold`. Unlike the plain `Sub` in
/// [`eval_heap_inst`], which subtracts a freshly-minted chunk value, this reads
/// the **held** chunk's value -- that value *is* the predicate's snapshot, and
/// sharing it with the paired `inhale` is what makes the fold/unfold round-trip
/// hold. In a certificate walk the hit chunk's recipe rides along, so the
/// reconstructed slots purify to `unwrap(proj_i(s))` over it.
fn eval_sub_yield(
    ctx: &mut VerifyContext<'_>,
    state: &mut EvalState,
    inst: &Inst,
    pc: &PathConds,
) -> Result<(), VerifyError> {
    let InstKind::Heap(HeapInst::Sub {
        base, loc, perm, ..
    }) = &inst.kind
    else {
        unreachable!("eval_sub_yield called on a non-yielding-Sub instruction");
    };
    let base_h = get_heap(state, base);
    let addr = state.get_val(ctx, loc);
    let kind = state
        .loc_kind(loc)
        .expect("acc location must be Addr-typed");
    let cperm = eval_perm_structural(ctx, state, perm);
    let pc_lits: Vec<(egg::Id, Polarity)> = pc
        .conds
        .iter()
        .map(|(v, p)| (state.get_val(ctx, v), *p))
        .collect();

    // The held value, and (certificate walks) its provenance. A miss is an
    // outright failure, which is what makes the `Option` below concretely
    // `Some` on every path that continues: `None` is reachable only at a
    // provably-non-positive permission.
    let a = ctx.egraph.find(addr);
    let (held, held_recipe) = base_h
        .entries()
        .find_map(|(_, c)| (ctx.egraph.find(c.addr) == a).then(|| (c.value, c.recipe.clone())))
        .ok_or(VerifyError::InsufficientPermission)?;
    if ctx.recipe.is_some() && held_recipe.is_none() {
        return Err(VerifyError::Unimplemented(
            "purify: consume of an unheld location",
        ));
    }
    let out = heap_subtract(
        ctx,
        &base_h,
        &kind,
        Chunk::new_perm(addr, cperm.clone(), held),
        &pc_lits,
        demand_of(&cperm),
    )?;
    state.push_heap(out);

    // Presence is `0 < perm`, built from the permission the instruction names.
    // For a literal amount it const-folds to `true` and `option_member` collapses
    // to a bare `Some`, so the paired `inhale`'s unwrap peels with no proof goal.
    let perm_id = cperm.to_id(ctx);
    let present = expr!(ctx, (0/1) <r {perm_id});
    let elem = kind.value.clone();
    let opt = ctx.option_member(elem.clone(), present, held);
    // The recipe must purify the value that is *pushed*, which is the option --
    // not the held value inside it. Handing the held value's recipe straight
    // through would leave the paired `OptionUnwrap` emitting `unwrap(held)`, a
    // stray peel with no `Some` under it: sound in the e-graph, where the
    // instruction's own `option_member` reduces, but dangling in a certificate
    // replayed at a client, where it silently severs the fold/unfold identity.
    // Wrapping here keeps the pair `unwrap(Some(r))`, which reduces by the same
    // rule on both paths.
    let opt_recipe = match (ctx.recipe.is_some(), &held_recipe) {
        (true, Some(hr)) => {
            let some_id = ctx.alloc.option_some();
            let rb = ctx.recipe.as_mut().unwrap();
            Some(rb.emit(crate::verify::rewrite::AxiomPure::App {
                func: some_id,
                type_args: vec![elem.clone()],
                args: vec![hr.clone()],
            }))
        }
        _ => None,
    };
    state.push_val(opt, Type::Option(Box::new(elem)), opt_recipe);
    Ok(())
}

/// Evaluate a resource `inhale` / `exhale`. `base inhale R(args) p` produces the
/// resource's footprint into `base` and **assumes** its boolean; `base exhale ..`
/// consumes it and **asserts** it. A self-framed callee additionally yields the
/// snapshot of its footprint as a pure `Val`.
///
/// Shared by the method walk and the resource/function-body walks: a
/// **frame-only** exhale (a heap-dependent function call's implicit precondition
/// check) occurs inside contract and function bodies, where a *consuming*
/// resource op would rightly be rejected.
fn eval_resource_op(
    ctx: &mut VerifyContext<'_>,
    program: &vmir::Program,
    state: &mut EvalState,
    inst: &Inst,
    certs: &HashMap<MemberId, ResourceDefinition>,
) -> Result<(), VerifyError> {
    let InstKind::Heap(
        hi @ (HeapInst::Inhale {
            base, call, perm, ..
        }
        | HeapInst::Exhale {
            base, call, perm, ..
        }),
    ) = &inst.kind
    else {
        unreachable!("eval_resource_op called on a non-resource-op instruction");
    };

        let is_inhale = matches!(hi, HeapInst::Inhale { .. });
        // A frame-only exhale is the implicit precondition check of a
        // heap-dependent function call: sufficiency is proven on a scratch
        // subtraction chain (so aliased slots require their sum) whose result
        // is discarded, and a bare-wildcard slot takes the presence path
        // rather than materializing a wildcard permission.
        let frame_only = matches!(hi, HeapInst::Exhale { frame_only: true, .. });
        let base_h = get_heap(state, base);
        let args: Vec<egg::Id> = call.args.iter().map(|v| state.get_val(ctx, v)).collect();
        let scale = eval_perm(ctx, state, perm);
        let pc_lits = collect_pc_lits(ctx, state, &inst.pc);
        // Inhale: produce fresh chunks, assume the bool guarded by `0 < scale`
        // (it carries no path condition — the branch lives in the perm scale).
        // Exhale: consume the held chunks, assert the bool under `pc`.
        let (source, direction, bool_guard) = if is_inhale {
            // The bind is the value source: `Fresh` havocs each slot, while
            // `Bound(s)` recovers it as `unwrap(proj_i(s))` so this heap and
            // any other reconstruction from `s` name the *same* terms.
            let source = match hi {
                HeapInst::Inhale {
                    bind: Bind::Bound(v),
                    ..
                } => {
                    // Always a plain `Snap`: a desugared `unfold` names the
                    // `PureInst::OptionUnwrap` temp, not the `Option` itself, so
                    // the seam is explicit in the instruction stream.
                    let sv = state.get_val(ctx, v);
                    ValueSource::ProjectSnap(sv, state.recipe_of(v))
                }
                HeapInst::Inhale {
                    bind: Bind::SelfSlot,
                    ..
                } => {
                    return Err(VerifyError::Unimplemented(
                        "`with self` on a resource inhale",
                    ));
                }
                _ => ValueSource::Fresh,
            };
            let pos = expr!(ctx, (0/1) <r {scale});
            let mut guard = vec![(pos, Polarity::Positive)];
            // Fork model: arms run unguarded (the branch no longer rides in
            // the perm scale), so the block cube must guard the inhaled bool
            // — otherwise a conditional `inhale` on one arm leaks its fact
            // past the branch.
            guard.extend_from_slice(&pc_lits);
            (source, Direction::Produce, guard)
        } else {
            (
                ValueSource::ReadHeap(base_h.clone()),
                Direction::Consume,
                pc_lits.clone(),
            )
        };
        let FootprintResult {
            heap: out,
            members,
            slot_recipes,
        } = walk_footprint(
            ctx,
            program,
            certs,
            call.resource,
            &args,
            base_h,
            source,
            direction,
            // A frame check does not scale: it reads the footprint at the
            // callee's own slot permissions, exactly as the dedicated `Snap`
            // did. Scaling by the (unused) `1/1` operand would rebuild every
            // slot permission as `1 * p`, which is equal but not identical,
            // and identity is what the `old(f(x)) == f(x)` congruence needs.
            if frame_only { None } else { Some(scale) },
            state.perm_is_wild(perm),
            &pc_lits,
            &bool_guard,
            frame_only,
        )?;
        if hi.produces_heap() {
            state.push_heap(out);
        }
        if let Some(res_id) = hi.snap_yield(&program.decls) {
            let s = build_snapshot(ctx, res_id, members);
            // A certificate walk mirrors the snapshot as `cons(Some(v_i))`
            // over the read values' recipes -- a self-framed footprint is
            // fully held, so every slot is `Some`. Only a frame-only exhale
            // (a function's precondition check) is ever reached during a
            // recipe walk; a consuming inhale/exhale is method-only, where no
            // recipe is in flight and this yields `None` as before.
            let recipe = if ctx.recipe.is_some() {
                let def = certs.get(&res_id).ok_or(VerifyError::DependencyFailed)?;
                let elems: Vec<Type> =
                    def.footprint.iter().map(|sl| sl.elem.clone()).collect();
                let some_id = ctx.alloc.option_some();
                let cons_id = ctx.alloc.cons(res_id, 0);
                let rb = ctx.recipe.as_mut().unwrap();
                let mut members_r = Vec::with_capacity(slot_recipes.len());
                for (i, r) in slot_recipes.iter().enumerate() {
                    let v = r.clone().ok_or(VerifyError::Unimplemented(
                        "purify: snap value outside footprint",
                    ))?;
                    members_r.push(rb.emit(crate::verify::rewrite::AxiomPure::App {
                        func: some_id,
                        type_args: vec![elems[i].clone()],
                        args: vec![v],
                    }));
                }
                Some(rb.emit(crate::verify::rewrite::AxiomPure::App {
                    func: cons_id,
                    type_args: Vec::new(),
                    args: members_r,
                }))
            } else {
                None
            };
            state.push_val(s, Type::Snap(res_id), recipe);
        }
    Ok(())
}

/// Evaluate a a bound `inhale`: widen a snapshot value back into a heap — the entry
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
    let InstKind::Heap(HeapInst::Inhale {
        bind: Bind::Bound(snap),
        call,
        ..
    }) = &inst.kind
    else {
        unreachable!("eval_from_snap called on a non-bound-inhale instruction");
    };
    let (resource, args) = (&call.resource, &call.args);
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
    // (guarded by the path condition — a a bound `inhale` may sit under a branch).
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
        false,
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
/// lowering, so an axiom's top-level `forall`s capture nothing. Occurrences with
/// captures enter the e-graph when an outer instance's body is built
/// (`rewrite::build_instance`) or while evaluating a hosting method/resource body,
/// never eagerly here.
fn assume_axioms(ctx: &mut VerifyContext<'_>, program: &vmir::Program) -> Result<(), VerifyError> {
    // One rule instantiates every `forall` in the program: quantifiers are
    // e-nodes (data), not rules, so one generic rule suffices — and a `forall`
    // materialized *during* saturation (by an outer instantiation, or by a
    // certificate graft) is picked up on the next iteration, which per-quantifier
    // rules structurally could not do (egg forbids mid-run rule injection).
    // Registered unconditionally: the table is filled lazily, so "empty right now"
    // says nothing about whether this unit will state a quantifier. The rule costs
    // nothing until a `Forall` node exists — its searcher scans one
    // `classes_by_op` bucket.
    let table = std::sync::Arc::clone(ctx.alloc.quant_table());
    ctx.axiom_rules
        .push(crate::verify::rewrite::forall_rule(table));
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
                    let (id, _) = eval_pure_inst(ctx, &state, ty, pi, &[], None)?;
                    state.push_val(id, ty.clone(), None);
                }
                InstKind::Assume(val) => {
                    let id = state.get_val(ctx, val);
                    let true_ = expr!(ctx, true);
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
        let true_ = expr!(ctx, true);
        ctx.union(res, true_);
        ctx.egraph.rebuild();
    }
    // One lazy unfold rule per already-verified function certificate. `analyze`
    // guarantees a function only calls functions verified earlier, so every
    // function this unit could reference already has a cert in `fn_certs`. Each
    // rule rebuilds the recipe's body lazily (add-only) when a `FuncApp(f, ..)`
    // occurrence is seen during saturation (see `rewrite::function_rule`).
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
/// pattern matches exactly the nodes a body would build — and canonicalize its
/// variables into recipe space: at or above `binder_base` a variable is a binder
/// (`Bound`), below it a free enclosing value whose capture slot is `slot`.
pub(crate) fn prepare_trig_term(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    term: &vmir::TrigTerm,
    binder_base: usize,
    slot: &std::collections::HashMap<usize, usize>,
) -> crate::verify::rewrite::PreparedTerm {
    use crate::verify::rewrite::PreparedTerm;
    match term {
        vmir::TrigTerm::Var(k) if *k >= binder_base => PreparedTerm::Bound(k - binder_base),
        vmir::TrigTerm::Var(k) => PreparedTerm::Capture(slot[k]),
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
                args: args
                    .iter()
                    .map(|a| prepare_trig_term(alloc, a, binder_base, slot))
                    .collect(),
            }
        }
    }
}

/// Lower an axiom/quantifier body's inst stream into registry-resolved pure
/// steps (every callee down to its verifier `FuncId`), ready for the applier —
/// which has no registry access at rule-application time. `names` resolves a
/// member to its source name, needed for the display label of a minted `f%pre`
/// token (the registry holds no interner).
pub(crate) fn prepare_body(
    alloc: &mut crate::verify::func_registry::FuncRegistry,
    quants: &crate::verify::quant::RecipeTable,
    names: &dyn Fn(MemberId) -> String,
    insts: &[vmir::Inst],
) -> Result<Vec<crate::verify::rewrite::AxiomInst>, VerifyError> {
    use crate::verify::rewrite::{AxiomInst, AxiomPure};
    let mut out = Vec::with_capacity(insts.len());
    for inst in insts {
        // A nested `forall` is a step like any other: it materializes the inner
        // e-node with the enclosing instance's values as capture children. Its
        // capture list is derived (`Forall::free_temps`) and cached on the table by
        // the innermost-first intern that ran just before this one.
        if let InstKind::Pure(_, PureInst::Forall(q)) = &inst.kind {
            let (recipe, free) = quants.entry_of(q)?;
            out.push(AxiomInst::Forall {
                recipe: *recipe,
                caps: free.iter().map(|&k| Val::Temp(k)).collect(),
            });
            continue;
        }
        // A call is two steps, exactly as on the eval walk (`eval_pure_inst`'s
        // `FunctionCall` arm): the application, plus the callee's `f%pre(args)`
        // presence token that lets `rewrite::function_rule` unfold its body *here*.
        // Without the token an instance materializes `f(σ)` opaquely and the callee
        // never unfolds under the quantifier. The token step occupies no temp slot,
        // so the application keeps this inst's slot.
        if let InstKind::Pure(_, PureInst::FunctionCall(fc)) = &inst.kind {
            let args: Vec<Val> = fc.args.iter().cloned().collect();
            out.push(AxiomInst::Val(AxiomPure::App {
                func: crate::verify::func_registry::func_id_for_member(fc.function),
                type_args: fc.type_args.clone(),
                args: args.clone(),
            }));
            // The token's truth is released under this inst's own path condition —
            // a call under `i > 0 ==> ..` inside the body must not fire the
            // callee's axioms at a σ where `i > 0` fails. No `recipe_pc` needed:
            // a prepared body's `Val`s *are* the host body's temps, used
            // identity-wise, so `inst.pc`'s literals transfer directly.
            out.push(AxiomInst::Token {
                func: alloc.fn_pre_token(fc.function, &names(fc.function)),
                args,
                guards: inst.pc.conds.clone(),
            });
            continue;
        }
        let prepared = match &inst.kind {
            InstKind::Pure(_, pi) => AxiomInst::Val(match pi {
                PureInst::Binary(op, l, r) => AxiomPure::Binary(*op, l.clone(), r.clone()),
                PureInst::Ternary(c, t, e) => AxiomPure::Ternary(c.clone(), t.clone(), e.clone()),
                PureInst::RealCast(v) => AxiomPure::RealCast(v.clone()),
                PureInst::FunctionCall(_) => unreachable!("handled above"),
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
                | PureInst::OptionUnwrap(_)
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
/// The binders become fresh values while every enclosing value keeps its real
/// e-class, so the body's side conditions are discharged *for an arbitrary
/// binding*. Those conditions are exactly a pure expression's: `Div`/`Mod`
/// divisors, and the `assert f#requires(..)` stitched at a call to a
/// contract-bearing function. Body-local path conditions come along (short-circuit
/// lowering emits them), so a guard proves its own consequent's WD:
/// `forall x :: {f(x)} x != 0 ==> f(10 / x)` discharges the division under
/// `<x != 0>`.
///
/// A nested `forall` is checked recursively here, with its encloser's binders
/// already fresh, so no WD obligation survives into a recipe — instantiation runs
/// inside a rewrite rule, where nothing can be proven.
fn check_forall_wd(
    ctx: &mut VerifyContext<'_>,
    q: &vmir::Forall,
    host: &EvalState,
    host_pc: &[(egg::Id, Polarity)],
) -> Result<(), VerifyError> {
    // `ctx.egraph` is a scratch clone for the duration; the live graph, its
    // fixpoint cache and the memo scope are handled by `with_scratch_graph`.
    // The certificate recipe (if one is being built) is paused: the WD walk's
    // scratch evaluation must not mirror steps into the host's recipe.
    let recipe = ctx.recipe.take();
    let res = ctx.with_scratch_graph(|ctx| check_forall_wd_in_scratch(ctx, q, host, host_pc));
    ctx.recipe = recipe;
    res
}

fn check_forall_wd_in_scratch(
    ctx: &mut VerifyContext<'_>,
    q: &vmir::Forall,
    host: &EvalState,
    host_pc: &[(egg::Id, Polarity)],
) -> Result<(), VerifyError> {
    // Capture is implicit: the body indexes the *enclosing* value table directly,
    // so the body's state is that table cut to the quantifier's frame — which
    // starts at the `forall` step's own temp, shadowed by the first binder.
    let mut state = host.frame_for(q);
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
                check_forall_wd(ctx, inner, &state, &pc_lits)?;
                let (id, _) = eval_pure_inst(ctx, &state, ty, pi, &pc_lits, None)?;
                state.push_val(id, ty.clone(), None);
            }
            InstKind::Pure(ty, pi) => {
                let (id, _) = eval_pure_inst(ctx, &state, ty, pi, &pc_lits, None)?;
                state.push_val(id, ty.clone(), None);
            }
            // A callee's postcondition, stitched at the call: assume it under the
            // guards it was emitted with.
            InstKind::Assume(val) => {
                let id = state.get_val(ctx, val);
                ctx.assume_guarded(id, pc_lits.iter().rev().copied());
            }
            // A quantifier body is heap-free, hence permission-free.
            InstKind::Perm(_) => {
                return Err(VerifyError::Unimplemented(
                    "permission instruction in a quantifier body",
                ));
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
/// then evaluate it, snapshotting for the visualizer throughout. One place, so an
/// obligation added to `inst_obligations` cannot be skipped by one driver.
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
    mut footprint_ops: Option<&mut Vec<(Val, vmir::PermVal)>>,
) -> Result<(), VerifyError> {
    for (inst_idx, inst) in insts.iter().enumerate() {
        assert_statement_pc_is_block_cube(ctx, state, inst);
        if let (Some(ops), InstKind::Heap(HeapInst::Add { loc, perm, .. } | HeapInst::Sub { loc, perm, .. })) =
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
            if let Err(err) = check_forall_wd(ctx, q, state, &pc_lits) {
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
        stats::bump(|s| s.insts_processed += 1);
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
    ));
    let params: Vec<egg::Id> = resource
        .params
        .iter()
        .map(|ty| ctx.fresh_symbolic_value(ty.clone()))
        .collect();
    // A two-state (`Ctx`) resource needs no special seeding: its pre-state
    // arrives as the trailing snapshot parameter (a fresh symbolic like any
    // other param) and its body's entry bound `inhale` reconstructs the pre-state
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
                // One `slice` per operand, shape preserved. Permission step lists
                // are short (a `PermInst::Ite` only arises from a branch gate or a
                // read-only weakening — see `Sink::gate_perm`).
                perm: perm.try_map(&mut |v: &Val| rb.slice(v))?,
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
        bool: rb.slice_with_tokens(&bool_r)?,
    }))
}

/// Verify a non-recursive function and capture its body as a **pure term
/// recipe** ([`FunctionDefinition`]) for other units to unfold lazily at call
/// sites (`rewrite::function_rule`). Abstract functions (no body) have nothing
/// to verify.
///
/// The walk runs the ordinary live eval (obligations, a bound `inhale`/`Unfold` heap
/// reconstruction, `Deref` values), logging each heap-reconstruction event into
/// `ctx.heap_events`. Then [`purify_function`] re-walks the body once, turning it
/// into an add-only recipe over the params (and the snapshot param, for
/// heap-dependent functions): every `Deref` becomes the pure term the snapshot
/// projects to (`unwrap(proj_i(snap))`, possibly nested through `unfolding`), and
/// the entry `assume f#requires` is **dropped** so that no precondition-derived
/// merge can ride into a call site (a recipe imports no e-classes).
///
/// Callees — including the function's own `f#requires`/`f#ensures` contract
/// functions — are ordinary `Function` decls verified earlier in dependency
/// order, so their recipes are already in `fn_certs` and their unfold rules
/// installed; saturation discharges the contract obligations lazily.
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
    // limited-twin substitution set and the exit-post shape are fixed up front.
    // No precondition guard is prepared -- a function's facts are gated by its
    // `f%pre` token, released at the call.
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
    // (pure ops, the entry `assume`, `Snap`/a bound `inhale`/`Unfold` for heap-dependent
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
    let (steps, facts, token_steps) = rb.into_function_parts()?;
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
        token_steps,
        facts,
    })))
}

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
    // No precondition guard: like every other function, an abstract function's
    // fact is gated by its `f%pre` token, released at the call.
    let guards = Vec::new();
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
        // An abstract function has no body, hence no propagated callee tokens.
        token_steps: Vec::new(),
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
        // read. In a function body that heap is the one the entry bound `inhale`
        // reconstructs from the snapshot parameter, so this failing means a read
        // outside the declared precondition. `chunk_under_pc` lets an address
        // that only aliases a held chunk under this instruction's branch (e.g.
        // `y.f` where `x == y` holds here) still frame.
        InstKind::Pure(_, PureInst::Deref(heap, loc)) => {
            let addr = state.get_val(ctx, loc);
            let held = get_heap(state, heap);
            let perm = state.loc_kind(loc).and_then(|k| {
                let c = chunk_under_pc(ctx, held.chunks_of(&k), addr, pc_lits)?
                    .clone();
                // Frame against the gated perm: a conditionally-held location
                // frames only where its guard holds.
                Some(c.gated_perm(ctx))
            });
            match perm {
                // A bare (or absent) perm: the goal `0 < leaf` is discharged by
                // the caller exactly as before (flag-OFF byte-identical).
                None => {
                    let zero = expr!(ctx, 0/1);
                    let goal = ctx.add(Symbolic::Binary(BinOp::LtR, [zero, zero]));
                    vec![(goal, VerifyError::InsufficientPermission)]
                }
                Some(p @ ChunkPerm::Leaf { .. }) => {
                    let leaf = p.as_leaf().unwrap();
                    let zero = expr!(ctx, 0/1);
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
                        vec![(expr!(ctx, false), VerifyError::InsufficientPermission)]
                    }
                }
            }
        }
        // `not(perm < 0)` desugared to an `Ite`. Applies to a location combine, a
        // resource inhale/exhale, and fold/unfold (a consuming op with a negative
        // scale would flip `heap_subtract` into permission fabrication).
        //
        // A wildcard is positive by construction (assumed `0 < w` at creation) and
        // the e-graph has no real-order reasoning to *prove* `¬(w < 0)`; Silicon
        // likewise skips the assertion for a constrainable ARP, so a
        // wildcard-bearing permission carries no `perm ≥ 0` obligation.
        InstKind::Heap(
            HeapInst::Add { perm, .. }
            | HeapInst::Sub { perm, .. }
            | HeapInst::Inhale { perm, .. }
            | HeapInst::Exhale { perm, .. },
        ) if state.perm_is_wild(perm) => vec![],
        // A resource op carries the resource's **boolean**, so at zero permission
        // it would assume or assert facts about a footprint it transferred no
        // share of — a vacuous operation. Viper rejects `fold`/`unfold` at a
        // possibly-zero amount too, so this mirrors it rather than diverging.
        // Free today: every resource op carries a literal `1/1`, and `0 < 1/1`
        // const-folds.
        InstKind::Heap(HeapInst::Inhale { perm, .. } | HeapInst::Exhale { perm, .. }) => {
            let perm = eval_perm(ctx, state, perm);
            let goal = expr!(ctx, (0/1) <r {perm});
            vec![(
                goal,
                VerifyError::SideCondition("permission must be positive"),
            )]
        }
        // Slot ops carry no boolean, so moving zero permission says nothing and
        // is legal — and they carry every gated amount (`b ? 1/1 : 0` is exactly
        // `0` on the `!b` path), so a strict rule here would reject every
        // conditional `acc`.
        InstKind::Heap(
            HeapInst::Add { perm, .. } | HeapInst::Sub { perm, .. },
        ) => {
            let perm = eval_perm(ctx, state, perm);
            let zero = expr!(ctx, 0/1);
            // Permission must not be negative: not (perm < 0).
            let goal = expr!(ctx, not ({perm} <r {zero}));
            vec![(
                goal,
                VerifyError::SideCondition("permission may be negative"),
            )]
        }
        // `not(divisor == 0)` desugared to an `Ite`. The divisor is homogeneous
        // with the result (casts), so the VMIR result type gives the zero's type.
        InstKind::Pure(ty, PureInst::Binary(op, _, r)) if op.is_div_or_mod() => {
            let rv = state.get_val(ctx, r);
            let zero = zero_of(ctx, ty);
            // Divisor must be non-zero: not (divisor == 0).
            let goal = expr!(ctx, not ({rv} == {zero}));
            vec![(goal, VerifyError::SideCondition("divisor may be zero"))]
        }
        _ => vec![],
    }
}

/// Zero literal of the given numeric type (`Real` fallback for non-numeric).
fn zero_of(ctx: &mut VerifyContext<'_>, ty: &Type) -> egg::Id {
    match ty {
        Type::Int => ctx.add(Symbolic::Lit(Literal::Int(num::BigInt::from(0)))),
        _ => expr!(ctx, 0/1),
    }
}

#[cfg(test)]
mod e2e;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::lang::Symbolic;
    use crate::verify::test_support::fresh_ctx;












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
