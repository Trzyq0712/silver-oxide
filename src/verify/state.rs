//! Verification state - combines stack (Store) and heap
//! Inspired by Silicon's State.scala

use crate::verify::store::Store;
use crate::verify::heap::Heap;
use crate::verify::term::Term;

/// Verification state combines:
/// - Store (stack): maps local variables to symbolic terms
/// - Heap: collection of permission chunks
/// - Path conditions: symbolic constraints we know to be true
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// The store (stack) - local variable bindings
    pub store: Store,
    
    /// The heap - permission chunks
    pub heap: Heap,
    
    /// Path conditions - pure facts (not yet implemented as separate type)
    /// For now, we keep it simple
    pub path_conditions: Vec<Term>,
}

impl State {
    /// Create a new empty state
    pub fn new() -> Self {
        State {
            store: Store::new(),
            heap: Heap::new(),
            path_conditions: Vec::new(),
        }
    }
    
    /// Add a path condition (pure fact)
    pub fn assume(&mut self, condition: Term) {
        self.path_conditions.push(condition);
    }
    
    /// Get all path conditions
    pub fn path_conditions(&self) -> &[Term] {
        &self.path_conditions
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}
