use crate::translate::signatures::SignatureContext;
use crate::vmir::{MemberId, Type as VmirType};
use crate::{silver, vmir};
use lasso::Rodeo;
use rusttyc::types::{Arity, Partial, Preliminary, Variant};
use rusttyc::{Constructable, TcKey, TcVar, TypeChecker};
use std::collections::HashMap;
use std::fmt;

pub type VmirTc = TypeChecker<TcType, vmir::Val>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TcType {
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
    Addr,
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

impl TcVar for vmir::Val {}

impl Variant for TcType {
    type Err = TypeErr;

    fn arity(&self) -> Arity {
        match self {
            // Address types have arity 1 (the type they point to)
            TcType::Addr => Arity::Fixed(1),
            // All other types are scalar (arity 0)
            _ => Arity::Fixed(0),
        }
    }

    fn top() -> Self {
        TcType::Top
    }

    fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err> {
        use TcType::*;

        let variant = match (lhs.variant, rhs.variant) {
            // Top meets with anything to give that thing
            (Top, x) | (x, Top) => x,

            // Numeric is the supertype of both Int and Real
            (Numeric, x @ (Numeric | Int | Real)) | (x @ (Numeric | Int | Real), Numeric) => x,

            // Identical types meet to themselves
            (Bool, Bool) => Bool,
            (Ref, Ref) => Ref,
            (Addr, Addr) => Addr,
            (Int, Int) => Int,
            (Real, Real) => Real,

            // Domains with same ID
            (Domain(id1), Domain(id2)) if id1 == id2 => Domain(id1),

            // All other combinations are incompatible
            (t1, t2) => Err(TypeErr(format!(
                "Cannot unify types: {:?} and {:?}",
                t1, t2
            )))?,
        };

        let least_arity = match &variant {
            Addr => 1,
            _ => 0,
        };

        Ok(Partial {
            variant,
            least_arity,
        })
    }
}

impl Constructable for TcType {
    type Type = VmirType;

    fn construct(
        &self,
        children: &[Self::Type],
    ) -> Result<Self::Type, <Self as rusttyc::ContextSensitiveVariant>::Err> {
        Ok(match self {
            TcType::Bool => VmirType::Bool,
            TcType::Int => VmirType::Int,
            TcType::Real => VmirType::Real,
            TcType::Numeric => VmirType::Real,
            TcType::Ref => VmirType::Ref,
            TcType::Domain(id) => VmirType::Domain(*id),
            TcType::Addr => {
                let inner = children
                    .get(0)
                    .ok_or_else(|| TypeErr("AddrOf missing child type".to_string()))?;
                VmirType::Addr(Box::new(inner.clone()))
            }
            TcType::Top => Err(TypeErr("Abstract type in VMIR".to_string()))?,
        })
    }
}

impl From<&VmirType> for TcType {
    fn from(value: &VmirType) -> Self {
        match value {
            VmirType::Bool => TcType::Bool,
            VmirType::Int => TcType::Int,
            VmirType::Real => TcType::Real,
            VmirType::Ref => TcType::Ref,
            VmirType::Domain(id) => TcType::Domain(*id),
            VmirType::Addr(_) => TcType::Addr,
        }
    }
}
