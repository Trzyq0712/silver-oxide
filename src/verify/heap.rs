//! Heap - collection of permission chunks

use crate::verify::chunk::Chunk;
use crate::verify::term::Term;

/// Heap stores all the permission chunks
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Heap {
    chunks: Vec<Chunk>,
}

impl Heap {
    /// Create an empty heap
    pub fn new() -> Self {
        Heap {
            chunks: Vec::new(),
        }
    }
    
    /// Add a chunk to the heap
    pub fn add_chunk(&mut self, chunk: Chunk) {
        self.chunks.push(chunk);
    }
    
    /// Find all chunks matching a location
    pub fn find_chunks(&self, location: &Term) -> Vec<&Chunk> {
        self.chunks
            .iter()
            .filter(|chunk| chunk.location_matches(location))
            .collect()
    }
    
    /// Find and remove a chunk matching a location with sufficient permission
    /// Returns the chunk if found, None otherwise
    /// Note: In real implementation, we'd need to check permission amounts via SMT
    pub fn consume_chunk(&mut self, location: &Term) -> Option<Chunk> {
        if let Some(pos) = self.chunks.iter().position(|c| c.location_matches(location)) {
            Some(self.chunks.remove(pos))
        } else {
            None
        }
    }
    
    /// Get all chunks
    pub fn chunks(&self) -> &[Chunk] {
        &self.chunks
    }
    
    /// Remove all chunks (useful for testing)
    pub fn clear(&mut self) {
        self.chunks.clear();
    }
}

impl Default for Heap {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::term::Sort;
    
    #[test]
    fn test_heap_operations() {
        let mut heap = Heap::new();
        
        let loc = Term::fresh("loc", Sort::Snap);
        let val = Term::fresh_int("val");
        let chunk = Chunk::new(loc.clone(), Term::FullPerm, val);
        
        heap.add_chunk(chunk.clone());
        
        let found = heap.find_chunks(&loc);
        assert_eq!(found.len(), 1);
        
        let consumed = heap.consume_chunk(&loc);
        assert!(consumed.is_some());
        
        let found_after = heap.find_chunks(&loc);
        assert_eq!(found_after.len(), 0);
    }
}
