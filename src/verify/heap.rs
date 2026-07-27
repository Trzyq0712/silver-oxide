use std::rc::Rc;

use lasso::Spur;

use crate::verify::context::VerifyContext;
use crate::verify::lang::Symbolic;
use crate::vmir::{Bound, Literal, Type};

/// A chunk's permission as an explicit term, held OUTSIDE the union-find so a
/// control-flow join can build a structural `Select` that collapses without
/// saturation. `Leaf` is an e-class id (a literal `1/1`, a symbolic real, a
/// wildcard-bearing term, or a program-written `c ==> acc` gate) and is treated
/// as OPAQUE — never structurally decomposed. `Select` is built ONLY by the
/// Stage-4 join merge ([`ChunkPerm::select`]). With `SILVER_OXIDE_BLOCK_MERGE`
/// off every perm is a `Leaf` and [`ChunkPerm::to_id`] is the identity.
#[derive(Debug, Clone)]
pub enum ChunkPerm {
    Leaf(egg::Id),
    Select {
        cond: egg::Id,
        then: Box<ChunkPerm>,
        els: Box<ChunkPerm>,
    },
}

impl ChunkPerm {
    pub fn leaf(id: egg::Id) -> Self {
        ChunkPerm::Leaf(id)
    }

    /// Structural equality with LEAVES compared by e-class `find` (so a `1/1`
    /// from either arm counts as equal). O(size), no saturation.
    fn same(ctx: &VerifyContext<'_>, a: &ChunkPerm, b: &ChunkPerm) -> bool {
        match (a, b) {
            (ChunkPerm::Leaf(x), ChunkPerm::Leaf(y)) => {
                ctx.egraph.find(*x) == ctx.egraph.find(*y)
            }
            (
                ChunkPerm::Select {
                    cond: c1,
                    then: t1,
                    els: e1,
                },
                ChunkPerm::Select {
                    cond: c2,
                    then: t2,
                    els: e2,
                },
            ) => {
                ctx.egraph.find(*c1) == ctx.egraph.find(*c2)
                    && Self::same(ctx, t1, t2)
                    && Self::same(ctx, e1, e2)
            }
            _ => false,
        }
    }

    /// The join-select smart constructor. `cond` is the then-edge reach value.
    /// Applies, in order: (i) same-amount collapse (`then ≡ els ⇒ then`, the
    /// give-back / untouched kill); (ii) dead-arm drop when `cond` const-folds
    /// to a boolean literal in the ground graph (no `assume`); (iii) otherwise a
    /// `Select`. Deterministic, bounded, no budget.
    pub fn select(
        ctx: &mut VerifyContext<'_>,
        cond: egg::Id,
        then: ChunkPerm,
        els: ChunkPerm,
    ) -> Self {
        if Self::same(ctx, &then, &els) {
            return then;
        }
        let cond_c = ctx.egraph.find(cond);
        match ctx.egraph[cond_c].data.known() {
            Some(Literal::Bool(true)) => return then,
            Some(Literal::Bool(false)) => return els,
            _ => {}
        }
        ChunkPerm::Select {
            cond,
            then: Box::new(then),
            els: Box::new(els),
        }
    }

    /// Lower to an e-graph id — ONLY where the prover needs an e-class
    /// (sufficiency, bound/non-alias axioms, `perm > 0` framing). For a `Leaf`
    /// this is the identity (no node added), so with the flag off the migrated
    /// heap ops are byte-identical to Stage 3.
    pub fn to_id(&self, ctx: &mut VerifyContext<'_>) -> egg::Id {
        match self {
            ChunkPerm::Leaf(id) => *id,
            ChunkPerm::Select { cond, then, els } => {
                let t = then.to_id(ctx);
                let e = els.to_id(ctx);
                ctx.add(Symbolic::Ite([*cond, t, e]))
            }
        }
    }

    /// A representative e-class id for debug display, WITHOUT mutating the graph
    /// (a `Leaf`'s id, or a `Select`'s condition). Viz only — not a real perm id.
    pub fn repr_id(&self) -> egg::Id {
        match self {
            ChunkPerm::Leaf(id) => *id,
            ChunkPerm::Select { cond, .. } => *cond,
        }
    }

    /// Whether any leaf carries a wildcard. Wildcard perms stay `Leaf` and never
    /// enter a `Select`, so in practice this walks a single leaf.
    pub fn has_wildcard(&self, ctx: &VerifyContext<'_>) -> bool {
        match self {
            ChunkPerm::Leaf(id) => super::declaration::contains_wildcard(ctx, *id),
            ChunkPerm::Select { then, els, .. } => {
                then.has_wildcard(ctx) || els.has_wildcard(ctx)
            }
        }
    }
}

/// The **kind** of a heap location: a field/predicate group, the held value
/// type, and the permission bound. This is exactly the content of a location's
/// `Type::Addr` — the chunks of one kind share a group in the heap. Sourced
/// straight from VMIR (the address's `Type::Addr`), never from e-graph inference.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LocationKind {
    pub group: Spur,
    pub value: Type,
    pub bound: Bound,
}

impl LocationKind {
    /// Extract the kind from an address type. `None` for a non-`Addr` type.
    pub fn from_addr_type(ty: &Type) -> Option<Self> {
        match ty {
            Type::Addr {
                group,
                value,
                bound,
            } => Some(Self {
                group: *group,
                value: (**value).clone(),
                bound: bound.clone(),
            }),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Chunk {
    /// The address e-class this chunk sits at (its identity within a group).
    pub(crate) addr: egg::Id,
    pub(crate) perm: ChunkPerm,
    pub(crate) value: egg::Id,
    /// Recipe provenance of `value` — the recipe-space temp a certificate walk
    /// (function/resource verification) associates with the held value, so a
    /// later `Deref` purifies to the pure term this chunk was produced from.
    /// `None` in method bodies (no recipe is built) and for values without a
    /// pure recipe (fresh, merged).
    pub(crate) recipe: Option<crate::vmir::Val>,
}

impl Chunk {
    /// Build a chunk from a bare permission id (the common case). Wraps the id
    /// as a `ChunkPerm::Leaf`.
    pub fn new(addr: egg::Id, perm: egg::Id, value: egg::Id) -> Self {
        Self::new_perm(addr, ChunkPerm::Leaf(perm), value)
    }

    /// Build a chunk from an explicit permission term (the join merge's select).
    pub fn new_perm(addr: egg::Id, perm: ChunkPerm, value: egg::Id) -> Self {
        Self {
            addr,
            perm,
            value,
            recipe: None,
        }
    }

    /// The chunk's permission lowered to an e-class id.
    pub fn perm_id(&self, ctx: &mut VerifyContext<'_>) -> egg::Id {
        self.perm.to_id(ctx)
    }

    pub fn with_recipe(mut self, recipe: Option<crate::vmir::Val>) -> Self {
        self.recipe = recipe;
        self
    }
}

/// Symbolic heap: chunks partitioned by [`LocationKind`]. Each group is an
/// `Rc<[Chunk]>` so cloning a heap (frequent — one per instruction) shares the
/// group slices; mutating one group copies just that slice (copy-on-write). The
/// outer `im::HashMap` is itself structurally shared.
///
/// Within a group, identity is the chunk's `addr` e-class — today at most one
/// chunk per address (the same-address merge happens in `declaration.rs`). The
/// vec shape is the prerequisite for the lazy Σ-ite permission model (chunks
/// accumulating per `acc`), which lands later.
#[derive(Debug, Clone)]
pub struct Heap {
    groups: im::HashMap<LocationKind, Rc<[Chunk]>>,
}

impl Heap {
    pub fn empty() -> Self {
        Self {
            groups: im::HashMap::new(),
        }
    }

    /// The chunks of one location kind (empty slice if none held).
    pub fn chunks_of(&self, kind: &LocationKind) -> &[Chunk] {
        self.groups.get(kind).map(|r| &r[..]).unwrap_or(&[])
    }

    /// The chunk held at `addr` within `kind`'s group (exact e-class match).
    pub fn chunk(&self, kind: &LocationKind, addr: egg::Id) -> Option<&Chunk> {
        self.chunks_of(kind).iter().find(|c| c.addr == addr)
    }

    pub fn perm_at(
        &self,
        ctx: &mut VerifyContext<'_>,
        kind: &LocationKind,
        addr: egg::Id,
    ) -> Option<egg::Id> {
        self.chunk(kind, addr).map(|c| c.perm.to_id(ctx))
    }

    /// Insert `chunk` into `kind`'s group, replacing any chunk already at the
    /// same `addr` (preserving today's one-chunk-per-address semantics).
    pub fn with_chunk(&self, kind: &LocationKind, chunk: Chunk) -> Self {
        let mut v: Vec<Chunk> = self
            .groups
            .get(kind)
            .map(|r| r.to_vec())
            .unwrap_or_default();
        match v.iter_mut().find(|c| c.addr == chunk.addr) {
            Some(slot) => *slot = chunk,
            None => v.push(chunk),
        }
        Self {
            groups: self.groups.update(kind.clone(), v.into()),
        }
    }

    /// Drop the chunk at `addr` in `kind`'s group (removing the group if empty).
    pub fn without_chunk(&self, kind: &LocationKind, addr: egg::Id) -> Self {
        let Some(group) = self.groups.get(kind) else {
            return self.clone();
        };
        let v: Vec<Chunk> = group.iter().filter(|c| c.addr != addr).cloned().collect();
        let groups = if v.is_empty() {
            self.groups.without(kind)
        } else {
            self.groups.update(kind.clone(), v.into())
        };
        Self { groups }
    }

    /// Every chunk in the heap, paired with its location kind.
    pub fn entries(&self) -> impl Iterator<Item = (&LocationKind, &Chunk)> {
        self.groups
            .iter()
            .flat_map(|(k, cs)| cs.iter().map(move |c| (k, c)))
    }
}
