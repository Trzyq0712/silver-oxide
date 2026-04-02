use crate::silver;
use crate::translate::signatures::SignatureContext;
use crate::vmir::{MemberId, Type as VmirType};
use lasso::Rodeo;
use rusttyc::types::{Arity, Partial, Preliminary, Variant};
use rusttyc::{TcKey, TcVar, TypeChecker};
use std::collections::HashMap;
use std::fmt;

/// Type system for Silver expressions
/// This represents the types in the Silver language with a lattice structure
/// for rusttyc-based type checking
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// Boolean type
    Bool,
    /// Integer type
    Int,
    /// Real/rational number type
    Real,
    /// Reference type
    Ref,
    /// Domain type with identifier
    Domain(MemberId),
    /// Address/pointer to another type
    AddrOf(Box<Type>),
    /// Either an Int or Real
    Numeric,
    /// Top type (supertype of all types)
    Top,
}

/// Error type for type checking
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeErr(pub String);

impl fmt::Display for TypeErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Type error: {}", self.0)
    }
}

impl std::error::Error for TypeErr {}

impl Variant for Type {
    type Err = TypeErr;

    fn arity(&self) -> Arity {
        match self {
            // Address types have arity 1 (the type they point to)
            Type::AddrOf(_) => Arity::Fixed(1),
            // All other types are scalar (arity 0)
            _ => Arity::Fixed(0),
        }
    }

    fn top() -> Self {
        Type::Top
    }

    /// Compute the meet (greatest lower bound) of two types
    /// This is used by rusttyc to resolve type constraints
    fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err> {
        use Type::*;

        let variant = match (lhs.variant, rhs.variant) {
            // Top meets with anything to give that thing
            (Top, x) | (x, Top) => Ok(x),

            // Identical types meet to themselves
            (Bool, Bool) => Ok(Bool),
            (Int, Int) => Ok(Int),
            (Real, Real) => Ok(Real),
            (Ref, Ref) => Ok(Ref),
            (Numeric, Numeric) => Ok(Numeric),

            // Numeric can become Int or Real or Perm based on context
            (Numeric, Int) | (Int, Numeric) => Ok(Int),
            (Numeric, Real) | (Real, Numeric) => Ok(Real),

            // Domains with same ID
            (Domain(id1), Domain(id2)) if id1 == id2 => Ok(Domain(id1)),

            // Address types - check inner types match
            (AddrOf(inner1), AddrOf(inner2)) => {
                if *inner1 == *inner2 {
                    Ok(AddrOf(inner1))
                } else {
                    Err(TypeErr(format!(
                        "Incompatible address types: &{:?} vs &{:?}",
                        inner1, inner2
                    )))
                }
            }

            // All other combinations are incompatible
            (t1, t2) => Err(TypeErr(format!(
                "Cannot unify types: {:?} and {:?}",
                t1, t2
            ))),
        }?;

        // Compute arity for result
        let least_arity = match &variant {
            AddrOf(_) => 1,
            _ => 0,
        };

        Ok(Partial {
            variant,
            least_arity,
        })
    }
}

impl Type {
    /// Convert a SilverType to a VMIR Type
    pub fn to_vmir_type(&self) -> VmirType {
        match self {
            Type::Bool => VmirType::Bool,
            Type::Int => VmirType::Int,
            Type::Real => VmirType::Real,
            Type::Ref => VmirType::Ref,
            Type::Domain(id) => VmirType::Domain(*id),
            Type::AddrOf(inner) => VmirType::Addr(Box::new(inner.to_vmir_type())),
            Type::Top | Type::Numeric => {
                panic!("Cannot convert {:?} type to VMIR", self)
            }
        }
    }

    /// Create a SilverType from a VMIR Type
    pub fn from_vmir_type(ty: &VmirType) -> Self {
        match ty {
            VmirType::Bool => Type::Bool,
            VmirType::Int => Type::Int,
            VmirType::Real => Type::Real,
            VmirType::Ref => Type::Ref,
            VmirType::Domain(id) => Type::Domain(*id),
            VmirType::Addr(inner) => Type::AddrOf(Box::new(Type::from_vmir_type(inner))),
        }
    }
}
