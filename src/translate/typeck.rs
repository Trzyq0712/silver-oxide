use crate::silver;
use crate::vmir::{MemberId, Type as VmirType};
use crate::translate::signatures::SignatureContext;
use lasso::Rodeo;
use rusttyc::types::{Arity, Partial, Variant, Preliminary};
use rusttyc::{TcKey, TypeChecker, TcVar};
use std::collections::HashMap;
use std::fmt;

/// Type system for Silver expressions
/// This represents the types in the Silver language with a lattice structure
/// for rusttyc-based type checking
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SilverType {
    /// Boolean type
    Bool,
    /// Integer type
    Int,
    /// Real/rational number type
    Real,
    /// Reference type
    Ref,
    /// Permission type (subtype of Real, used for access permissions)
    Perm,
    /// Domain type with identifier
    Domain(MemberId),
    /// Address/pointer to another type
    AddrOf(Box<SilverType>),
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

impl Variant for SilverType {
    type Err = TypeErr;

    fn arity(&self) -> Arity {
        match self {
            // Address types have arity 1 (the type they point to)
            SilverType::AddrOf(_) => Arity::Fixed(1),
            // All other types are scalar (arity 0)
            _ => Arity::Fixed(0),
        }
    }

    fn top() -> Self {
        SilverType::Top
    }

    /// Compute the meet (greatest lower bound) of two types
    /// This is used by rusttyc to resolve type constraints
    fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err> {
        use SilverType::*;

        let variant = match (lhs.variant, rhs.variant) {
            // Top meets with anything to give that thing
            (Top, x) | (x, Top) => Ok(x),

            // Identical types meet to themselves
            (Bool, Bool) => Ok(Bool),
            (Int, Int) => Ok(Int),
            (Real, Real) => Ok(Real),
            (Ref, Ref) => Ok(Ref),
            (Perm, Perm) => Ok(Perm),

            // Perm is a subtype of Real
            (Perm, Real) | (Real, Perm) => Ok(Perm),

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

impl SilverType {
    /// Convert a SilverType to a VMIR Type
    pub fn to_vmir_type(&self) -> VmirType {
        match self {
            SilverType::Bool => VmirType::Bool,
            SilverType::Int => VmirType::Int,
            SilverType::Real | SilverType::Perm => VmirType::Real,
            SilverType::Ref => VmirType::Ref,
            SilverType::Domain(id) => VmirType::Domain(*id),
            SilverType::AddrOf(inner) => VmirType::Addr(Box::new(inner.to_vmir_type())),
            SilverType::Top => panic!("Cannot convert Top type to VMIR"),
        }
    }

    /// Create a SilverType from a VMIR Type
    pub fn from_vmir_type(ty: &VmirType) -> Self {
        match ty {
            VmirType::Bool => SilverType::Bool,
            VmirType::Int => SilverType::Int,
            VmirType::Real => SilverType::Real,
            VmirType::Ref => SilverType::Ref,
            VmirType::Domain(id) => SilverType::Domain(*id),
            VmirType::Addr(inner) => {
                SilverType::AddrOf(Box::new(SilverType::from_vmir_type(inner)))
            }
        }
    }
}

/// No variables needed for our type system (we use TcKeys for terms only)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NoVar;
impl TcVar for NoVar {}

/// Context for type checking a Silver program
pub struct TypeCheckContext {
    /// The rusttyc type checker
    tc: TypeChecker<SilverType, NoVar>,
    /// Map from expression pointers to type keys
    /// We use raw pointer as a unique identifier for each Exp node
    exp_keys: HashMap<*const silver::Exp, TcKey>,
    /// Signature context for looking up function/method types
    signatures: SignatureContext,
    /// Name interner
    interner: Rodeo<MemberId>,
}

impl TypeCheckContext {
    pub fn new(signatures: SignatureContext, interner: Rodeo<MemberId>) -> Self {
        Self {
            tc: TypeChecker::new(),
            exp_keys: HashMap::new(),
            signatures,
            interner,
        }
    }

    /// Type check a Silver program and return the resolved type table
    pub fn type_check(
        mut self,
        _program: &silver::Program,
    ) -> Result<HashMap<TcKey, Preliminary<SilverType>>, TypeErr> {
        // Walk the AST and generate constraints
        // TODO: Implement constraint generation
        
        // For now, just resolve the (empty) constraint system
        self.tc.type_check_preliminary()
            .map_err(|e| TypeErr(format!("Type checking failed: {:?}", e)))
    }

    /// Get or create a type key for an expression
    fn get_or_create_key(&mut self, exp: &silver::Exp) -> TcKey {
        let ptr = exp as *const silver::Exp;
        *self.exp_keys.entry(ptr).or_insert_with(|| self.tc.new_term_key())
    }

    /// Impose a constraint that an expression has a specific type
    fn constrain_type(&mut self, exp: &silver::Exp, ty: SilverType) -> Result<(), TypeErr> {
        let key = self.get_or_create_key(exp);
        self.tc.impose(key.concretizes_explicit(ty))
            .map_err(|e| TypeErr(format!("Failed to impose constraint: {:?}", e)))
    }
}

// TODO: Add constraint generation by walking the AST
// Will be implemented in next phase when we add permission constraints


