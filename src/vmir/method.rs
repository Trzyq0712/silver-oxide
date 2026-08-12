use crate::vmir::display::VmirDisplay;
use crate::vmir::{Declaration, HeapVal, Inst, InstKind, MemberId, PathConds, Val};
use derive_more::{From, Into};
use lasso::Spur;
use std::fmt::{self, Display, Formatter};
use typed_index_collections::TiVec;

/// A method, lowered to a **block-structured** VMIR: the basic-block CFG is
/// preserved (not linearized) so a later verification stage can merge
/// predecessor heaps/permissions at real joins structurally. Blocks are stored
/// in topological order — every block precedes its successors, so a flat walk
/// (`flatten`) is a valid linearization and the `blocks` index of a predecessor
/// is always smaller than its successor's.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub name: Spur,
    pub blocks: TiVec<BlockId, Block>,
    /// The unique entry block (`Preds::Entry`); derivable, stored for convenience.
    pub entry: BlockId,
}

/// Index of a [`Block`] within a [`Method`]. Distinct from
/// [`crate::viper::cfg::BlockId`]: the VMIR index space is larger — it includes
/// the synthetic blocks minted when an n-ary (multi-goto) join is normalised
/// into a chain of binary joins.
#[derive(Debug, From, Into, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct BlockId(pub usize);

/// A basic block: a straight-line body plus a join phase that reconciles its
/// predecessors. Transforms an entry state `(env, h_in)` — derived from
/// [`Block::preds`] — into an exit state `(env', h_out)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    /// The block's **control** cube (its reaching path condition), shared by all
    /// its insts. `<>` for a straight-line/entry block.
    pub cube: PathConds,
    pub preds: Preds,
    /// Join phase: the phi (`Ternary`) reconciliations of variables that differ
    /// across predecessors (a heap `Merge` will join here too, a later stage).
    /// Empty for an entry or a pass-through single-predecessor block.
    pub join: Vec<Inst>,
    /// Body phase: straight-line SSA — the block's lowered statements/terminator.
    pub body: Vec<Inst>,
    /// The block's exit heap (the linear heap after the body, for now — the
    /// per-predecessor merge is a later stage).
    pub h_out: HeapVal,
}

/// How a block's predecessors reach it — the join-source form (forward edges are
/// its inverse). Joins are **binary**: an n-way merge is a chain of these.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Preds {
    /// The entry block: 0 predecessors. `h_in = entry_heap`, env = params.
    Entry,
    /// Exactly one predecessor. `h_in = pred.h_out`.
    From(BlockId),
    /// Two predecessors merged under `cond`: `then_` is taken when `cond` holds,
    /// `els` otherwise. `els` is the **unguarded** fall-through arm (the phi's
    /// last arm), so the select is `cond ? then_ : els`.
    Join {
        cond: Val,
        then_: BlockId,
        els: BlockId,
    },
}

impl Method {
    /// Concatenate every block's `join ++ body` in stored (topological) order.
    /// A valid linearization of the method — the on-ramp back to the flat
    /// verifier, and the migration oracle (for diamond methods this reproduces
    /// the pre-block linear stream byte-for-byte).
    pub fn flatten(&self) -> Vec<Inst> {
        self.iter_insts().cloned().collect()
    }

    /// Borrowing iterator over every instruction in stored (topological) order —
    /// `join ++ body` per block. Cheaper than [`Method::flatten`] when the caller
    /// only needs to scan (the yielded refs borrow `self`, so no temporary to
    /// keep alive).
    pub fn iter_insts(&self) -> impl Iterator<Item = &Inst> {
        self.blocks
            .iter()
            .flat_map(|b| b.join.iter().chain(&b.body))
    }
}

// ======================
// DISPLAY INFRASTRUCTURE
// ======================

/// Count the value/heap temps an instruction slice produces, to advance the
/// running `eN`/`hN` display counters across blocks. Mirrors the inst-walker
/// (`vmir/inst.rs`): a `Pure` inst yields a value temp; a `Heap` inst yields a
/// heap temp, plus a value temp when it is snapshot-yielding.
fn count_temps(insts: &[Inst], decls: &TiVec<MemberId, Declaration>) -> (usize, usize) {
    let mut vals = 0;
    let mut heaps = 0;
    for inst in insts {
        match &inst.kind {
            InstKind::Pure(..) => vals += 1,
            InstKind::Heap(hi) => {
                if hi.produces_heap() {
                    heaps += 1;
                }
                if hi.snap_yield(decls).is_some() {
                    vals += 1;
                }
            }
            InstKind::Assume(_) | InstKind::Assert(_) | InstKind::Refute(_) => {}
        }
    }
    (vals, heaps)
}

impl<'a> Display for VmirDisplay<'a, &'a Method> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);
        writeln!(f, "method {name} {{")?;
        // Global positional `eN`/`hN` numbering, threaded across blocks in stored
        // (topological) order so ids match the flat stream.
        let mut e_idx = 0usize;
        let mut h_idx = 0usize;
        for (bid, blk) in self.item.blocks.iter_enumerated() {
            // Header: `bbK <cube>[ from bbP | join <cond> [bbT, bbE]]:`.
            let cube = Cube(&blk.cube);
            match &blk.preds {
                Preds::Entry => writeln!(f, "  bb{} {cube}:", bid.0)?,
                Preds::From(p) => writeln!(f, "  bb{} {cube} from bb{}:", bid.0, p.0)?,
                Preds::Join { cond, then_, els } => writeln!(
                    f,
                    "  bb{} {cube} join {cond} [bb{}, bb{}]:",
                    bid.0, then_.0, els.0
                )?,
            }
            // Join phase (phis), then body phase — each labelled, insts indented
            // one level deeper. Counters advance across both.
            if !blk.join.is_empty() {
                writeln!(f, "    join:")?;
                write!(f, "{}", self.with_nested((e_idx, h_idx, &blk.join[..])))?;
                let (dv, dh) = count_temps(&blk.join, self.decls);
                e_idx += dv;
                h_idx += dh;
            }
            writeln!(f, "    body:")?;
            write!(f, "{}", self.with_nested((e_idx, h_idx, &blk.body[..])))?;
            let (dv, dh) = count_temps(&blk.body, self.decls);
            e_idx += dv;
            h_idx += dh;
        }
        write!(f, "}}")
    }
}

/// Renders a block's control cube, forcing `<>` for the empty (top-level) cube
/// so a block header always shows its guard (unlike the inline `PathConds`
/// `Display`, which prints nothing when empty).
struct Cube<'a>(&'a PathConds);

impl Display for Cube<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.0.conds.is_empty() {
            write!(f, "<>")
        } else {
            write!(f, "{}", self.0)
        }
    }
}
