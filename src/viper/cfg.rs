//! Control-flow analysis of a typed Viper method body.
//!
//! Builds a basic-block CFG from the structured `If`/`Block` statements and the
//! `Label`/`Goto` jumps. We analyse Viper here; VMIR is always emitted flat, so
//! a later linearization pass walks this CFG (topologically — it is a DAG) to
//! emit PathCond-gated straight-line VMIR.
//!
//! Loops are rejected: a `goto` that forms a back-edge makes the block graph
//! cyclic, which is reported as [`CfgError::Loop`]. (Source `while` never
//! reaches the typed AST — typecheck rejects it.)

use std::collections::{HashMap, HashSet};

use derive_more::{From, Into};
use lasso::Spur;
use petgraph::algo::{tarjan_scc, toposort};
use petgraph::prelude::DiGraphMap;
use typed_index_collections::TiVec;

use crate::viper::typed::{PureMethodExp, Statement, StmtBlock};

/// Index of a basic block within a [`Cfg`].
#[derive(Debug, From, Into, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct BlockId(pub usize);

/// How a basic block transfers control to its successor(s).
#[derive(Debug, Clone)]
pub enum Terminator {
    /// Unconditional successor (a fall-through or an explicit `goto`).
    Goto(BlockId),
    /// Two-way branch on a pure condition (from an `if`).
    Branch {
        cond: PureMethodExp,
        then_: BlockId,
        else_: BlockId,
    },
    /// Method exit — control falls off the end of the body.
    Return,
}

/// A maximal straight-line run of statements with a single entry and a single
/// terminator.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub stmts: Vec<Statement>,
    pub term: Terminator,
    /// The source label this block is the target of, if any (also an `old[L]`
    /// heap-capture point).
    pub label: Option<Spur>,
}

/// The basic-block control-flow graph of a method body. Acyclic by
/// construction (loops are rejected during the build).
#[derive(Debug, Clone)]
pub struct Cfg {
    pub blocks: TiVec<BlockId, BasicBlock>,
    pub entry: BlockId,
    pub labels: HashMap<Spur, BlockId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CfgError {
    /// A `goto` forms a back-edge: the method contains a loop. Carries the
    /// blocks of one cyclic strongly-connected component.
    Loop(Vec<BlockId>),
    /// A `goto` targets a label that is never declared.
    UndefinedLabel(Spur),
}

/// Which outgoing edge of a predecessor reaches a block: an unconditional
/// `goto`/fall-through, or the then/else arm of a `Branch` (the branch
/// condition must hold / must not hold to take it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeSide {
    Goto,
    Then,
    Else,
}

impl Cfg {
    /// Blocks in topological (dependency) order — every block precedes its
    /// successors. Infallible: the graph is acyclic by construction.
    pub fn topo_order(&self) -> Vec<BlockId> {
        let g = block_graph(&self.blocks);
        toposort(&g, None).expect("CFG is acyclic by construction")
    }

    /// For each block, its predecessors paired with the edge that reaches it.
    pub fn predecessors(&self) -> TiVec<BlockId, Vec<(BlockId, EdgeSide)>> {
        let mut preds: TiVec<BlockId, Vec<(BlockId, EdgeSide)>> =
            self.blocks.iter().map(|_| Vec::new()).collect();
        for (id, blk) in self.blocks.iter_enumerated() {
            match &blk.term {
                Terminator::Goto(t) => preds[*t].push((id, EdgeSide::Goto)),
                Terminator::Branch { then_, else_, .. } => {
                    preds[*then_].push((id, EdgeSide::Then));
                    preds[*else_].push((id, EdgeSide::Else));
                }
                Terminator::Return => {}
            }
        }
        preds
    }

    /// The set of blocks reachable from the entry (the rest are dead code an
    /// `if`/`goto` left behind and need not be lowered).
    pub fn reachable(&self) -> HashSet<BlockId> {
        let mut seen = HashSet::new();
        let mut stack = vec![self.entry];
        while let Some(b) = stack.pop() {
            if seen.insert(b) {
                stack.extend(successors(&self.blocks[b].term));
            }
        }
        seen
    }
}

/// Build the basic-block CFG of a method body, rejecting loops (back-edge
/// `goto`s) and `goto`s to undefined labels.
pub fn build_cfg(body: &StmtBlock) -> Result<Cfg, CfgError> {
    let mut builder = Builder::default();
    let entry = builder.new_block();
    // Control reaching the end of the body (any still-open block) returns.
    if let Some(tail) = builder.process(&body.0, Some(entry)) {
        builder.open_seal(tail, Terminator::Return);
    }
    builder.finish(entry)
}

#[derive(Default)]
struct Builder {
    blocks: TiVec<BlockId, BlockData>,
    /// Block for each label seen (declared or merely referenced by a `goto`).
    labels: HashMap<Spur, BlockId>,
    /// Labels actually declared by a `label` statement (a subset of `labels`).
    defined: HashSet<Spur>,
}

#[derive(Default)]
struct BlockData {
    stmts: Vec<Statement>,
    term: Option<Terminator>,
    label: Option<Spur>,
}

impl Builder {
    fn new_block(&mut self) -> BlockId {
        self.blocks.push_and_get_key(BlockData::default())
    }

    /// The block for label `l`, created on first reference (a `goto` may precede
    /// the `label` declaration).
    fn label_block(&mut self, l: Spur) -> BlockId {
        if let Some(&b) = self.labels.get(&l) {
            return b;
        }
        let b = self.new_block();
        self.blocks[b].label = Some(l);
        self.labels.insert(l, b);
        b
    }

    /// Set a block's terminator, but only if it is still open (the first
    /// terminator wins).
    fn open_seal(&mut self, b: BlockId, t: Terminator) {
        if self.blocks[b].term.is_none() {
            self.blocks[b].term = Some(t);
        }
    }

    /// The current open block, creating a fresh one at an unreachable point
    /// (`*cur == None`, e.g. just after a `goto`) so a statement is not dropped.
    fn ensure(&mut self, cur: &mut Option<BlockId>) -> BlockId {
        if let Some(b) = *cur {
            return b;
        }
        let b = self.new_block();
        *cur = Some(b);
        b
    }

    /// Process a statement sequence starting in `cur` (an open block, or `None`
    /// at an unreachable point). Returns the open block control reaches after
    /// the sequence, or `None` if it ends unreachable (e.g. after a `goto`).
    fn process(&mut self, stmts: &[Statement], mut cur: Option<BlockId>) -> Option<BlockId> {
        for s in stmts {
            match s {
                Statement::If(cond, then, els) => {
                    let b = self.ensure(&mut cur);
                    let then_e = self.new_block();
                    let else_e = self.new_block();
                    self.open_seal(
                        b,
                        Terminator::Branch {
                            cond: cond.clone(),
                            then_: then_e,
                            else_: else_e,
                        },
                    );
                    let then_x = self.process(&then.0, Some(then_e));
                    let else_stmts = els.as_ref().map(|b| b.0.as_slice()).unwrap_or(&[]);
                    let else_x = self.process(else_stmts, Some(else_e));
                    // Arms that fall through merge; arms ending in goto/return
                    // (returned `None`) do not.
                    let merge = self.new_block();
                    if let Some(tx) = then_x {
                        self.open_seal(tx, Terminator::Goto(merge));
                    }
                    if let Some(ex) = else_x {
                        self.open_seal(ex, Terminator::Goto(merge));
                    }
                    cur = Some(merge);
                }
                Statement::Block(inner) => {
                    cur = self.process(&inner.0, cur);
                }
                Statement::Label(l) => {
                    self.defined.insert(*l);
                    let lb = self.label_block(*l);
                    if let Some(b) = cur {
                        self.open_seal(b, Terminator::Goto(lb));
                    }
                    cur = Some(lb);
                }
                Statement::Goto(l) => {
                    let lb = self.label_block(*l);
                    let b = self.ensure(&mut cur);
                    self.open_seal(b, Terminator::Goto(lb));
                    cur = None;
                }
                // Everything else is straight-line: append to the current block.
                _ => {
                    let b = self.ensure(&mut cur);
                    self.blocks[b].stmts.push(s.clone());
                }
            }
        }
        cur
    }

    fn finish(self, entry: BlockId) -> Result<Cfg, CfgError> {
        let Builder {
            blocks,
            labels,
            defined,
        } = self;

        // Every referenced label must be declared.
        for &l in labels.keys() {
            if !defined.contains(&l) {
                return Err(CfgError::UndefinedLabel(l));
            }
        }

        // Finalize: a still-open block falls off the end → Return.
        let blocks: TiVec<BlockId, BasicBlock> = blocks
            .into_iter()
            .map(|bd| BasicBlock {
                stmts: bd.stmts,
                term: bd.term.unwrap_or(Terminator::Return),
                label: bd.label,
            })
            .collect();

        // Loop rejection: the block graph must be acyclic.
        let graph = block_graph(&blocks);
        if toposort(&graph, None).is_err() {
            return Err(CfgError::Loop(cyclic_blocks(&graph)));
        }

        Ok(Cfg {
            blocks,
            entry,
            labels,
        })
    }
}

fn successors(t: &Terminator) -> Vec<BlockId> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::Branch { then_, else_, .. } => vec![*then_, *else_],
        Terminator::Return => vec![],
    }
}

fn block_graph(blocks: &TiVec<BlockId, BasicBlock>) -> DiGraphMap<BlockId, ()> {
    let mut g = DiGraphMap::new();
    for (id, _) in blocks.iter_enumerated() {
        g.add_node(id);
    }
    for (id, b) in blocks.iter_enumerated() {
        for succ in successors(&b.term) {
            g.add_edge(id, succ, ());
        }
    }
    g
}

/// The blocks of one cyclic SCC (size > 1, or a self-loop), for error reporting.
fn cyclic_blocks(g: &DiGraphMap<BlockId, ()>) -> Vec<BlockId> {
    for scc in tarjan_scc(g) {
        if scc.len() > 1 || (scc.len() == 1 && g.contains_edge(scc[0], scc[0])) {
            return scc;
        }
    }
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::viper::typed::{Literal, PureExpKind, Statement, StmtBlock, Type, TypedPureExp};
    use lasso::Rodeo;

    /// A trivial straight-line statement (contents irrelevant to the CFG).
    fn nop() -> Statement {
        Statement::Var(vec![], None)
    }

    /// A trivial pure condition for `if`s.
    fn cond() -> PureMethodExp {
        TypedPureExp {
            ty: Type::Bool,
            exp: Box::new(PureExpKind::Const(Literal::Bool(true))),
        }
    }

    fn block(stmts: Vec<Statement>) -> StmtBlock {
        StmtBlock(stmts)
    }

    #[test]
    fn straight_line_is_one_block() {
        let cfg = build_cfg(&block(vec![nop(), nop()])).unwrap();
        assert_eq!(cfg.blocks.len(), 1);
        let entry = &cfg.blocks[cfg.entry];
        assert_eq!(entry.stmts.len(), 2);
        assert!(matches!(entry.term, Terminator::Return));
    }

    #[test]
    fn if_else_branches_and_merges() {
        let body = block(vec![Statement::If(
            cond(),
            block(vec![nop()]),
            Some(block(vec![nop()])),
        )]);
        let cfg = build_cfg(&body).unwrap();
        // entry(branch) + then + else + merge.
        assert_eq!(cfg.blocks.len(), 4);
        let Terminator::Branch { then_, else_, .. } = cfg.blocks[cfg.entry].term else {
            panic!("entry should branch");
        };
        // Both arms fall through to the same merge block, which returns.
        let Terminator::Goto(tm) = cfg.blocks[then_].term else {
            panic!("then arm should fall through")
        };
        let Terminator::Goto(em) = cfg.blocks[else_].term else {
            panic!("else arm should fall through")
        };
        assert_eq!(tm, em);
        assert!(matches!(cfg.blocks[tm].term, Terminator::Return));
    }

    #[test]
    fn if_without_else_routes_else_to_merge() {
        let body = block(vec![Statement::If(cond(), block(vec![nop()]), None)]);
        let cfg = build_cfg(&body).unwrap();
        assert_eq!(cfg.blocks.len(), 4);
        let Terminator::Branch { then_, else_, .. } = cfg.blocks[cfg.entry].term else {
            panic!("entry should branch");
        };
        // Both arms reach the same merge block.
        let Terminator::Goto(tm) = cfg.blocks[then_].term else {
            panic!()
        };
        let Terminator::Goto(em) = cfg.blocks[else_].term else {
            panic!()
        };
        assert_eq!(tm, em);
    }

    #[test]
    fn forward_goto_is_acyclic() {
        let mut r = Rodeo::default();
        let l = r.get_or_intern("L");
        let body = block(vec![Statement::Goto(l), nop(), Statement::Label(l), nop()]);
        let cfg = build_cfg(&body).unwrap();
        assert_eq!(cfg.labels.get(&l).copied(), Some(BlockId(1)));
        assert!(matches!(cfg.blocks[cfg.entry].term, Terminator::Goto(b) if b == BlockId(1)));
    }

    #[test]
    fn backward_goto_is_a_loop() {
        let mut r = Rodeo::default();
        let l = r.get_or_intern("L");
        let body = block(vec![Statement::Label(l), nop(), Statement::Goto(l)]);
        assert!(matches!(build_cfg(&body), Err(CfgError::Loop(_))));
    }

    #[test]
    fn goto_undefined_label_rejected() {
        let mut r = Rodeo::default();
        let l = r.get_or_intern("L");
        let body = block(vec![Statement::Goto(l)]);
        assert!(matches!(build_cfg(&body), Err(CfgError::UndefinedLabel(ll)) if ll == l));
    }

    #[test]
    fn arm_ending_in_goto_leaves_one_merge_predecessor() {
        let mut r = Rodeo::default();
        let l = r.get_or_intern("L");
        // if (c) { goto L } ; label L ; nop
        let body = block(vec![
            Statement::If(cond(), block(vec![Statement::Goto(l)]), None),
            Statement::Label(l),
            nop(),
        ]);
        let cfg = build_cfg(&body).unwrap();
        // No loop, label defined, builds fine.
        assert!(cfg.labels.contains_key(&l));
        let Terminator::Branch { then_, .. } = cfg.blocks[cfg.entry].term else {
            panic!("entry should branch");
        };
        // The then-arm jumps to the label, not the merge.
        assert!(
            matches!(cfg.blocks[then_].term, Terminator::Goto(b) if Some(&b) == cfg.labels.get(&l))
        );
    }
}
