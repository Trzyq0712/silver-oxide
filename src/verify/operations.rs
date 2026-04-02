//! Basic verification operations - inhale, exhale, assume, assert
//! These are the core operations for symbolic execution

use crate::verify::{State, chunk::Chunk, store::LocalVar, term::Term};

/// Inhale a permission to a location
/// This adds a chunk to the heap representing the permission
pub fn inhale(state: &mut State, location: Term, perm: Term, snap: Term) {
    let chunk = Chunk::new(location, perm, snap);
    state.heap.add_chunk(chunk);
}

/// Exhale a permission to a location
/// This removes a matching chunk from the heap
/// Returns an error if no matching chunk exists
pub fn exhale(state: &mut State, location: &Term, perm: &Term) -> Result<(), ExhaleError> {
    // Find and consume a chunk matching the location
    // In a full implementation, we'd need to:
    // 1. Check if location aliases with any chunk's location (via Z3)
    // 2. Check if we have enough permission (perm_in_chunk >= perm via Z3)
    // 3. Split the chunk if needed (perm_in_chunk > perm)
    
    // For now, simple exact match removal
    let chunk = state.heap.consume_chunk(location)
        .ok_or(ExhaleError::NoMatchingChunk)?;
    
    // TODO: Check permission amount and potentially add remainder back
    
    Ok(())
}

/// Bind a variable in the store
pub fn bind_var(state: &mut State, var: LocalVar, term: Term) {
    state.store.bind(var, term);
}

/// Look up a variable from the store
pub fn lookup_var<'a>(state: &'a State, var: &LocalVar) -> Option<&'a Term> {
    state.store.get(var)
}

/// Assume a pure condition (add to path conditions)
pub fn assume(state: &mut State, condition: Term) {
    state.assume(condition);
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExhaleError {
    NoMatchingChunk,
    InsufficientPermission,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::term::Sort;
    
    #[test]
    fn test_inhale_exhale() {
        let mut state = State::new();
        
        let loc = Term::fresh("loc", Sort::Snap);
        let perm = Term::FullPerm;
        let snap = Term::fresh_int("val");
        
        // Inhale permission
        inhale(&mut state, loc.clone(), perm.clone(), snap.clone());
        assert_eq!(state.heap.chunks().len(), 1);
        
        // Exhale permission
        let result = exhale(&mut state, &loc, &perm);
        assert!(result.is_ok());
        assert_eq!(state.heap.chunks().len(), 0);
        
        // Exhaling again should fail
        let result = exhale(&mut state, &loc, &perm);
        assert_eq!(result, Err(ExhaleError::NoMatchingChunk));
    }
    
    #[test]
    fn test_variable_binding() {
        let mut state = State::new();
        
        let var = LocalVar("x".to_string());
        let val = Term::IntLit(num::BigInt::from(42));
        
        bind_var(&mut state, var.clone(), val.clone());
        
        let looked_up = lookup_var(&state, &var);
        assert_eq!(looked_up, Some(&val));
    }
    
    #[test]
    fn test_assume() {
        let mut state = State::new();
        
        let cond = Term::BoolLit(true);
        assume(&mut state, cond.clone());
        
        assert_eq!(state.path_conditions().len(), 1);
        assert_eq!(state.path_conditions()[0], cond);
    }
}
