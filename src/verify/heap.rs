#[derive(Debug, Clone)]
pub struct Chunk {
    pub(crate) perm: egg::Id,
    pub(crate) value: egg::Id,
}

impl Chunk {
    pub fn new(perm: egg::Id, value: egg::Id) -> Self {
        Self { perm, value }
    }
}

#[derive(Debug, Clone)]
pub struct Heap {
    /// Maps from an address to a permission amount and a value.
    chunks: im::HashMap<egg::Id, Chunk>,
}

impl Heap {
    pub fn empty() -> Self {
        Self {
            chunks: im::HashMap::new(),
        }
    }

    pub fn chunk(&self, addr: egg::Id) -> Option<&Chunk> {
        self.chunks.get(&addr)
    }

    pub fn perm_at(&self, addr: egg::Id) -> Option<egg::Id> {
        self.chunk(addr).map(|chunk| chunk.perm)
    }

    pub fn value_at(&self, addr: egg::Id) -> Option<egg::Id> {
        self.chunk(addr).map(|chunk| chunk.value)
    }

    pub fn with_chunk(&self, addr: egg::Id, chunk: Chunk) -> Self {
        Self {
            chunks: self.chunks.update(addr, chunk),
        }
    }

    pub fn entries(&self) -> impl Iterator<Item = (egg::Id, &Chunk)> {
        self.chunks.iter().map(|(addr, chunk)| (*addr, chunk))
    }
}
