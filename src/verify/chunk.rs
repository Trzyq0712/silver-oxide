//! Chunks - basic heap permissions for VMIR resources
//! In VMIR, resources define permission patterns and are auto-unfolded
//! Chunks represent the actual permissions held at runtime

use crate::verify::term::Term;

/// A chunk represents a permission to a specific location
/// In VMIR, all heap access goes through addresses (&T types)
/// 
/// For example, with field f_: Int and object x:
/// - The location is the term representing f_(x) 
/// - This has type &Int (resource address)
/// - We hold some permission amount to this address
/// - We have a snapshot (symbolic value) at this address
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Chunk {
    /// The location (address term) - e.g., f_(x) where f_: Ref -> &Int
    /// This identifies what we have permission to
    pub location: Term,
    
    /// The permission amount held
    pub perm: Term,
    
    /// The snapshot (symbolic value at this location)
    /// This is what * (dereference) would return
    pub snap: Term,
}

impl Chunk {
    /// Create a new chunk
    pub fn new(location: Term, perm: Term, snap: Term) -> Self {
        Chunk {
            location,
            perm,
            snap,
        }
    }
    
    /// Check if this chunk's location matches the given term
    pub fn location_matches(&self, location: &Term) -> bool {
        &self.location == location
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::term::Sort;
    
    #[test]
    fn test_chunk_creation() {
        // Create symbolic location (e.g., f_(x))
        let loc = Term::fresh("f_x", Sort::Snap);
        let val = Term::fresh_int("val");
        let perm = Term::FullPerm;
        
        let chunk = Chunk::new(loc.clone(), perm, val);
        
        assert!(chunk.location_matches(&loc));
    }
}
