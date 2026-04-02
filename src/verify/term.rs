//! Symbolic terms - the core representation for symbolic execution.
//! Inspired by Silicon's Terms.scala - but without eager simplification

use std::sync::atomic::{AtomicUsize, Ordering};
use num::{BigInt, BigRational};

/// Unique identifier for terms
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Identifier(pub String);

/// Sort (type) of terms
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    Bool,
    Int,
    Ref,
    Perm,
    /// Resource snapshot sort (opaque)
    Snap,
}

/// Terms are the symbolic representation of values
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// Variable (symbolic value)
    Var(Identifier, Sort),
    
    /// Integer literal
    IntLit(BigInt),
    
    /// Boolean literal
    BoolLit(bool),
    
    /// Null reference
    Null,
    
    // ===== Integer Arithmetic =====
    Plus(Box<Term>, Box<Term>),
    Minus(Box<Term>, Box<Term>),
    Times(Box<Term>, Box<Term>),
    
    // ===== Boolean Logic =====
    Not(Box<Term>),
    And(Vec<Term>),
    Or(Vec<Term>),
    Implies(Box<Term>, Box<Term>),
    
    // ===== Comparisons =====
    /// Equality
    Eq(Box<Term>, Box<Term>),
    /// Less than
    Lt(Box<Term>, Box<Term>),
    /// Less than or equal
    Le(Box<Term>, Box<Term>),
    
    // ===== Permissions =====
    /// No permission (0)
    NoPerm,
    /// Full permission (1)
    FullPerm,
    /// Fractional permission (rational number)
    FracPerm(BigRational),
    /// Permission addition
    PermPlus(Box<Term>, Box<Term>),
    /// Permission subtraction
    PermMinus(Box<Term>, Box<Term>),
    /// Permission multiplication
    PermTimes(Box<Term>, Box<Term>),
    /// Permission less than
    PermLt(Box<Term>, Box<Term>),
    /// Permission less than or equal
    PermLe(Box<Term>, Box<Term>),
    
    // ===== Conditional =====
    /// If-then-else: Ite(condition, then_val, else_val)
    Ite(Box<Term>, Box<Term>, Box<Term>),
}

/// Counter for generating fresh identifiers
static FRESH_COUNTER: AtomicUsize = AtomicUsize::new(0);

impl Term {
    /// Get the sort (type) of this term
    pub fn sort(&self) -> Sort {
        match self {
            Term::Var(_, sort) => sort.clone(),
            Term::IntLit(_) => Sort::Int,
            Term::BoolLit(_) => Sort::Bool,
            Term::Null => Sort::Ref,
            
            Term::Plus(..) | Term::Minus(..) | Term::Times(..) => Sort::Int,
            
            Term::Not(..) | Term::And(..) | Term::Or(..) | Term::Implies(..) => Sort::Bool,
            Term::Eq(..) | Term::Lt(..) | Term::Le(..) => Sort::Bool,
            
            Term::NoPerm | Term::FullPerm | Term::FracPerm(..) 
            | Term::PermPlus(..) | Term::PermMinus(..) | Term::PermTimes(..) => Sort::Perm,
            
            Term::PermLt(..) | Term::PermLe(..) => Sort::Bool,
            
            Term::Ite(_, then_val, _) => then_val.sort(),
        }
    }
    
    /// Create a fresh symbolic variable
    pub fn fresh(name: &str, sort: Sort) -> Self {
        let id = FRESH_COUNTER.fetch_add(1, Ordering::SeqCst);
        Term::Var(Identifier(format!("${}_{}", name, id)), sort)
    }
    
    /// Create a fresh integer variable
    pub fn fresh_int(name: &str) -> Self {
        Self::fresh(name, Sort::Int)
    }
    
    /// Create a fresh reference variable
    pub fn fresh_ref(name: &str) -> Self {
        Self::fresh(name, Sort::Ref)
    }
    
    /// Create a fresh permission variable
    pub fn fresh_perm(name: &str) -> Self {
        Self::fresh(name, Sort::Perm)
    }
    
    /// Create a fresh snapshot variable
    pub fn fresh_snap(name: &str) -> Self {
        Self::fresh(name, Sort::Snap)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_fresh_variables() {
        let v1 = Term::fresh_int("x");
        let v2 = Term::fresh_int("x");
        
        // Different fresh variables should not be equal
        assert_ne!(v1, v2);
        
        // Both should have Int sort
        assert_eq!(v1.sort(), Sort::Int);
        assert_eq!(v2.sort(), Sort::Int);
    }
    
    #[test]
    fn test_permission_terms() {
        use num::FromPrimitive;
        
        let half = Term::FracPerm(BigRational::new(
            BigInt::from(1), 
            BigInt::from(2)
        ));
        
        assert_eq!(half.sort(), Sort::Perm);
        assert_eq!(Term::NoPerm.sort(), Sort::Perm);
        assert_eq!(Term::FullPerm.sort(), Sort::Perm);
    }
}
