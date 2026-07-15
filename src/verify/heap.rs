use std::rc::Rc;

use lasso::Spur;

use crate::vmir::{Bound, Type};

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
    pub(crate) perm: egg::Id,
    pub(crate) value: egg::Id,
}

impl Chunk {
    pub fn new(addr: egg::Id, perm: egg::Id, value: egg::Id) -> Self {
        Self { addr, perm, value }
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

    pub fn perm_at(&self, kind: &LocationKind, addr: egg::Id) -> Option<egg::Id> {
        self.chunk(kind, addr).map(|c| c.perm)
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
