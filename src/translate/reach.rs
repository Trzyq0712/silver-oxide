//! Per-block reaching-condition algebra for the method-body CFG linearizer.
//!
//! A block is lowered under its *reaching condition* — the disjunction of the
//! path conditions of its incoming edges. These helpers build that condition as
//! a `(PathConds, Val)` pair: boolean `Val`s are desugared to ternaries (the IR
//! has no `Not`/`And`/`Or`), constant-folded over `TRUE`/`FALSE`, and the OR of
//! edge cubes is minimized by adjacency so straight-line code keeps a trivial
//! `<>` guard. Also builds the phi (`ite`) environment merge at joins.

use std::collections::{HashMap, HashSet};

use lasso::Spur;

use crate::translate::sink::Sink;
use crate::viper::cfg::BlockId;
use crate::vmir::{FALSE, PathConds, Polarity, PureInst, TRUE, Type, Val};

/// `!v`, constant-folded over `true`/`false`.
pub(crate) fn not_val(sink: &mut Sink, v: Val) -> Val {
    if v == TRUE {
        FALSE
    } else if v == FALSE {
        TRUE
    } else {
        sink.emit_pure(Type::Bool, PureInst::Ternary(v, FALSE, TRUE))
    }
}

/// `a && b` as `a ? b : false`, constant-folded.
pub(crate) fn and_val(sink: &mut Sink, a: Val, b: Val) -> Val {
    if a == TRUE {
        b
    } else if b == TRUE {
        a
    } else if a == FALSE || b == FALSE {
        FALSE
    } else {
        sink.emit_pure(Type::Bool, PureInst::Ternary(a, b, FALSE))
    }
}

/// `a || b` as `a ? true : b`, constant-folded.
fn or_val(sink: &mut Sink, a: Val, b: Val) -> Val {
    if a == FALSE {
        b
    } else if b == FALSE {
        a
    } else if a == TRUE || b == TRUE {
        TRUE
    } else {
        sink.emit_pure(Type::Bool, PureInst::Ternary(a, TRUE, b))
    }
}

/// Materialize a path condition into a single boolean `Val` (conjunction of its
/// literals; `true` for the empty pc).
fn reach_val_of(sink: &mut Sink, pc: &PathConds) -> Val {
    let mut acc = TRUE;
    for (v, pol) in &pc.conds {
        let lit = match pol {
            Polarity::Positive => v.clone(),
            Polarity::Negative => not_val(sink, v.clone()),
        };
        acc = and_val(sink, acc, lit);
    }
    acc
}

/// The reaching condition of a block, as a `(pc, reach_val)` pair, from its
/// incoming `(pred, edge_val, edge_pc)` edges. The reach is the `OR` of the edge
/// path conditions (cubes); [`merge_cubes`] minimizes them by adjacency
/// (`P∧x ∨ P∧!x ⇒ P`). If they collapse to one cube it becomes the conjunctive
/// pc (a diamond → its prefix; a full `n`-way split → `<>`); otherwise the
/// residual cubes are OR'd into a single materialized reach literal. Always
/// exactly the block's reach condition, hence sound.
pub(crate) fn block_reach(
    sink: &mut Sink,
    edges: &[(BlockId, Val, PathConds)],
) -> (PathConds, Val) {
    if edges.is_empty() {
        // Unreachable (filtered out before lowering); keep it fully gated.
        return (
            PathConds {
                conds: vec![(FALSE, Polarity::Positive)],
            },
            FALSE,
        );
    }
    if let [(_, ev, epc)] = edges {
        return (epc.clone(), ev.clone());
    }

    let mut cubes: Vec<PathConds> = Vec::new();
    for (_, _, epc) in edges {
        if !cubes.contains(epc) {
            cubes.push(epc.clone());
        }
    }
    merge_cubes(&mut cubes);

    if let [only] = cubes.as_slice() {
        let pc = only.clone();
        let rv = reach_val_of(sink, &pc);
        return (pc, rv);
    }
    let mut rv = FALSE;
    for cube in &cubes {
        let cv = reach_val_of(sink, cube);
        rv = or_val(sink, rv, cv);
    }
    (
        PathConds {
            conds: vec![(rv.clone(), Polarity::Positive)],
        },
        rv,
    )
}

/// Boolean cube minimization: while two cubes are *adjacent* (identical literals
/// except one variable at opposite polarity), replace the pair with the shared
/// sub-cube. Value-preserving (`P∧x ∨ P∧!x = P`), so the disjunction is unchanged
/// — it just shrinks. Only equal-length cubes merge, so the innermost differing
/// literal collapses first and cascades outward, giving the LIFO/innermost-first
/// reduction a structured nest (or a goto split re-covering a subcube) expects.
fn merge_cubes(cubes: &mut Vec<PathConds>) {
    loop {
        let mut found = None;
        'search: for i in 0..cubes.len() {
            for j in (i + 1)..cubes.len() {
                if let Some(m) = merge_adjacent(&cubes[i], &cubes[j]) {
                    found = Some((i, j, m));
                    break 'search;
                }
            }
        }
        let Some((i, j, m)) = found else { break };
        cubes.remove(j); // j > i, so remove it first to keep index `i` valid
        cubes.remove(i);
        if !cubes.contains(&m) {
            cubes.push(m);
        }
    }
}

/// Two cubes merge iff they share every literal except exactly one variable that
/// appears with opposite polarity; the result drops that variable.
fn merge_adjacent(a: &PathConds, b: &PathConds) -> Option<PathConds> {
    if a.conds.len() != b.conds.len() {
        return None;
    }
    let a_only: Vec<(Val, Polarity)> = a
        .conds
        .iter()
        .filter(|l| !b.conds.contains(l))
        .cloned()
        .collect();
    let b_only: Vec<(Val, Polarity)> = b
        .conds
        .iter()
        .filter(|l| !a.conds.contains(l))
        .cloned()
        .collect();
    if a_only.len() != 1 || b_only.len() != 1 {
        return None;
    }
    let (va, pa) = &a_only[0];
    let (vb, pb) = &b_only[0];
    if va != vb || pa == pb {
        return None;
    }
    let conds = a
        .conds
        .iter()
        .filter(|(v, p)| !(v == va && p == pa))
        .cloned()
        .collect();
    Some(PathConds { conds })
}

/// Build a block's entry environment by phi-merging its predecessors' exit
/// environments. A single predecessor inherits directly; multiple predecessors
/// reconcile each variable with a nested `ite` over the edge conditions (the
/// last arm unguarded, since the edges are exhaustive). Variables that agree
/// across all predecessors pass through unchanged.
pub(crate) fn build_entry_env(
    sink: &mut Sink,
    edges: &[(BlockId, Val)],
    exit_env: &HashMap<BlockId, HashMap<Spur, Val>>,
    var_types: &HashMap<Spur, Type>,
) -> HashMap<Spur, Val> {
    if let [(p, _)] = edges {
        return exit_env.get(p).cloned().unwrap_or_default();
    }
    let mut names: HashSet<Spur> = HashSet::new();
    for (p, _) in edges {
        if let Some(e) = exit_env.get(p) {
            names.extend(e.keys().copied());
        }
    }
    let mut out: HashMap<Spur, Val> = HashMap::new();
    for name in names {
        let entries: Vec<(Val, Val)> = edges
            .iter()
            .filter_map(|(p, ev)| exit_env.get(p)?.get(&name).map(|v| (ev.clone(), v.clone())))
            .collect();
        let Some((_, first)) = entries.first() else {
            continue;
        };
        if entries.iter().all(|(_, v)| v == first) {
            out.insert(name, first.clone());
            continue;
        }
        let ty = var_types.get(&name).cloned().unwrap_or(Type::Int);
        let mut acc = entries.last().unwrap().1.clone();
        for (ev, v) in entries[..entries.len() - 1].iter().rev() {
            acc = sink.emit_pure(ty.clone(), PureInst::Ternary(ev.clone(), v.clone(), acc));
        }
        out.insert(name, acc);
    }
    out
}
