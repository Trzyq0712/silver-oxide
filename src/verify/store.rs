//! Store - maps local variables to symbolic terms
//! Inspired by Silicon's Store.scala

use crate::verify::term::{Term, Identifier};
use std::collections::HashMap;

/// Local variable identifier
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LocalVar(pub String);

/// Store maps local variables to their symbolic terms
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Store {
    bindings: HashMap<LocalVar, Term>,
}

impl Store {
    /// Create an empty store
    pub fn new() -> Self {
        Store {
            bindings: HashMap::new(),
        }
    }
    
    /// Bind a variable to a term
    pub fn bind(&mut self, var: LocalVar, term: Term) {
        self.bindings.insert(var, term);
    }
    
    /// Look up a variable's term
    pub fn get(&self, var: &LocalVar) -> Option<&Term> {
        self.bindings.get(var)
    }
    
    /// Check if a variable is bound
    pub fn contains(&self, var: &LocalVar) -> bool {
        self.bindings.contains_key(var)
    }
    
    /// Create a new store with an additional binding (immutable update)
    pub fn with_binding(&self, var: LocalVar, term: Term) -> Self {
        let mut new_bindings = self.bindings.clone();
        new_bindings.insert(var, term);
        Store { bindings: new_bindings }
    }
    
    /// Get all bindings
    pub fn bindings(&self) -> &HashMap<LocalVar, Term> {
        &self.bindings
    }
}

impl Default for Store {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::term::Sort;
    use num::BigInt;
    
    #[test]
    fn test_store_operations() {
        let mut store = Store::new();
        let x = LocalVar("x".to_string());
        
        assert!(!store.contains(&x));
        
        store.bind(x.clone(), Term::IntLit(BigInt::from(42)));
        assert!(store.contains(&x));
        
        match store.get(&x) {
            Some(Term::IntLit(n)) => assert_eq!(*n, BigInt::from(42)),
            _ => panic!("Expected IntLit(42)"),
        }
    }
    
    #[test]
    fn test_immutable_update() {
        let store1 = Store::new();
        let x = LocalVar("x".to_string());
        let y = LocalVar("y".to_string());
        
        let store2 = store1.with_binding(x.clone(), Term::IntLit(BigInt::from(1)));
        let store3 = store2.with_binding(y.clone(), Term::IntLit(BigInt::from(2)));
        
        // store1 should be unchanged
        assert!(!store1.contains(&x));
        
        // store2 should have x
        assert!(store2.contains(&x));
        assert!(!store2.contains(&y));
        
        // store3 should have both
        assert!(store3.contains(&x));
        assert!(store3.contains(&y));
    }
}
