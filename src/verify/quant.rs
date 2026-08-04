//! The program-level **recipe table**: every syntactic `forall` in the program,
//! compiled once into registry-resolved pure steps + trigger patterns, and named
//! by a [`RecipeId`] that rides in the payload of a
//! [`Symbolic::Forall`](crate::verify::lang::Symbolic::Forall) e-node.
//!
//! The table is built **before any verification unit runs** (`verify::verify`) and
//! frozen thereafter: instantiation can materialize new forall *nodes* mid-run
//! (an outer instance builds its inner quantifier with the outer σ as capture
//! children) but never a new *recipe* — nesting is closure-converted at
//! translation, so the inner body is already interned. That is what lets the
//! single instantiation rule hold a plain `Arc` snapshot of the table with no
//! staleness risk: egg cannot inject rules into a running `Runner`, but it does
//! see a new *e-node* on the next iteration.

use std::collections::HashMap;
use std::sync::Arc;

use typed_index_collections::TiVec;

use crate::verify::declaration::{prepare_body, prepare_trig_term};
use crate::verify::error::VerifyError;
use crate::verify::func_registry::FuncRegistry;
use crate::verify::lang::RecipeId;
use crate::verify::rewrite::{AxiomInst, PreparedTerm};
use crate::vmir::{self, InstKind, PureInst, Val};

/// A compiled `forall` body: the pure steps, the boolean result, the binder arity,
/// and the trigger groups (alternatives — a match of any one instantiates).
/// Temps: the captures first (they are the node's children, so their count is the
/// node's arity), then the `n_bound` binders (σ), then one per step.
pub(crate) struct QuantRecipe {
    pub(crate) n_bound: usize,
    /// Alternative trigger groups; each group is a conjunctive multi-pattern.
    /// Grown when a second `forall` dedups onto this entry with a different
    /// trigger (triggers are not part of a recipe's identity — see [`BodyKey`]).
    pub(crate) groups: Vec<Vec<PreparedTerm>>,
    pub(crate) insts: Vec<AxiomInst>,
    pub(crate) res: Val,
}

/// The identity of a recipe — the body, **without** the triggers. Two `forall`s
/// that denote the same proposition (same body, same arities) share one entry,
/// hence one e-node, so assuming either releases both trigger sets' instances.
/// Alpha-equivalence is free: binders are already positional temps.
#[derive(PartialEq, Eq, Hash)]
struct BodyKey {
    n_caps: usize,
    n_bound: usize,
    insts: Vec<AxiomInst>,
    res: Val,
}

#[derive(Default)]
pub(crate) struct RecipeTable {
    recipes: TiVec<RecipeId, QuantRecipe>,
    /// Dedup index: body ⟹ recipe. Trigger groups merge onto the hit.
    by_body: HashMap<BodyKey, RecipeId>,
    /// Lookup index for the eval walk: the syntactic `forall` ⟹ its recipe. A
    /// `vmir::Forall` is `Hash + Eq`, so no id bookkeeping is needed on the IR.
    by_forall: HashMap<vmir::Forall, RecipeId>,
}

impl RecipeTable {
    pub(crate) fn get(&self, id: RecipeId) -> &QuantRecipe {
        &self.recipes[id]
    }

    pub(crate) fn ids(&self) -> impl Iterator<Item = RecipeId> + '_ {
        self.recipes.keys()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.recipes.is_empty()
    }

    /// The recipe of an already-interned `forall`. Every syntactic `forall` is
    /// interned by [`build_recipe_table`] before any unit is walked, so a miss is
    /// a bug, not a program error.
    pub(crate) fn id_of(&self, q: &vmir::Forall) -> Result<RecipeId, VerifyError> {
        self.by_forall
            .get(q)
            .copied()
            .ok_or(VerifyError::Unimplemented("forall recipe not interned"))
    }
}

/// Compile every `forall` in the program into the table, in one pass over all
/// declarations. Bodies are heap-free and pure, so only the pure inst streams
/// matter.
pub(crate) fn build_recipe_table(
    alloc: &mut FuncRegistry,
    program: &vmir::Program,
) -> Result<Arc<RecipeTable>, VerifyError> {
    let mut table = RecipeTable::default();
    for decl in program.decls.iter() {
        match decl {
            vmir::Declaration::Axiom(ax) => intern_insts(alloc, &mut table, &ax.body.insts)?,
            vmir::Declaration::Function(f) => {
                if let Some(body) = &f.body {
                    intern_insts(alloc, &mut table, &body.insts)?;
                }
            }
            vmir::Declaration::Resource(r) => {
                if let Some(body) = &r.body {
                    intern_insts(alloc, &mut table, &body.insts)?;
                }
            }
            // Methods are block-structured; the trigger table is order-agnostic,
            // so intern the flattened stream (method verification itself is
            // disconnected on this branch — see `verify_method`).
            vmir::Declaration::Method(m) => intern_insts(alloc, &mut table, &m.flatten())?,
            vmir::Declaration::Domain(_) | vmir::Declaration::Adt(_) => {}
        }
    }
    Ok(Arc::new(table))
}

fn intern_insts(
    alloc: &mut FuncRegistry,
    table: &mut RecipeTable,
    insts: &[vmir::Inst],
) -> Result<(), VerifyError> {
    for inst in insts {
        if let InstKind::Pure(_, PureInst::Forall(q)) = &inst.kind {
            intern(alloc, table, q)?;
        }
    }
    Ok(())
}

/// Compile one `forall` and intern it, **innermost-first**: its nested `forall`s
/// are interned first, so `prepare_body` can name each of them by id while
/// compiling this body. Merges the trigger groups into an existing entry when the
/// body dedups. Idempotent.
fn intern(
    alloc: &mut FuncRegistry,
    table: &mut RecipeTable,
    q: &vmir::Forall,
) -> Result<RecipeId, VerifyError> {
    intern_insts(alloc, table, &q.body.insts)?;

    let insts = prepare_body(alloc, table, &q.body.insts)?;
    let groups: Vec<Vec<PreparedTerm>> = q
        .triggers
        .iter()
        .map(|g| {
            g.terms
                .iter()
                .map(|t| prepare_trig_term(alloc, t))
                .collect()
        })
        .collect();
    let key = BodyKey {
        n_caps: q.captures.len(),
        n_bound: q.bound.len(),
        insts: insts.clone(),
        res: q.body.res.clone(),
    };
    let id = match table.by_body.get(&key) {
        Some(&id) => {
            let entry = &mut table.recipes[id];
            for g in groups {
                if !entry.groups.contains(&g) {
                    entry.groups.push(g);
                }
            }
            id
        }
        None => {
            let id = table.recipes.push_and_get_key(QuantRecipe {
                n_bound: q.bound.len(),
                groups,
                insts,
                res: q.body.res.clone(),
            });
            table.by_body.insert(key, id);
            id
        }
    };
    table.by_forall.insert(q.clone(), id);
    Ok(id)
}
