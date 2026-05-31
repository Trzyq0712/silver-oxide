use rusttyc::Constructable;
use rusttyc::types::{Arity, Partial, Variant};

use crate::viper::typed::Type;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ViperTcType {
    Bool,
    Int,
    Real,
    Ref,
    Numeric, // supertype of Int and Real
    Top,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TcTypeErr(pub String);

impl std::fmt::Display for TcTypeErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Type error: {}", self.0)
    }
}

impl std::error::Error for TcTypeErr {}

impl Variant for ViperTcType {
    type Err = TcTypeErr;

    fn arity(&self) -> Arity {
        Arity::Fixed(0)
    }

    fn top() -> Self {
        ViperTcType::Top
    }

    fn meet(lhs: Partial<Self>, rhs: Partial<Self>) -> Result<Partial<Self>, Self::Err> {
        use ViperTcType::*;
        let variant = match (lhs.variant, rhs.variant) {
            (Top, x) | (x, Top) => x,
            (Numeric, Numeric) => Numeric,
            (Numeric, x @ (Int | Real)) | (x @ (Int | Real), Numeric) => x,
            (Bool, Bool) => Bool,
            (Ref, Ref) => Ref,
            (Int, Int) => Int,
            (Real, Real) => Real,
            (t1, t2) => {
                return Err(TcTypeErr(format!("Cannot unify {:?} and {:?}", t1, t2)));
            }
        };
        Ok(Partial {
            variant,
            least_arity: 0,
        })
    }
}

impl Constructable for ViperTcType {
    type Type = Type;

    fn construct(
        &self,
        _children: &[Self::Type],
    ) -> Result<Self::Type, <Self as rusttyc::ContextSensitiveVariant>::Err> {
        Ok(match self {
            ViperTcType::Bool => Type::Bool,
            ViperTcType::Int => Type::Int,
            ViperTcType::Real | ViperTcType::Numeric => Type::Real,
            ViperTcType::Ref => Type::Ref,
            ViperTcType::Top => {
                return Err(TcTypeErr("Cannot construct abstract type".to_string()));
            }
        })
    }
}

pub fn type_to_tc(ty: &Type) -> ViperTcType {
    match ty {
        Type::Bool => ViperTcType::Bool,
        Type::Int => ViperTcType::Int,
        Type::Real => ViperTcType::Real,
        Type::Ref => ViperTcType::Ref,
        Type::Generic(_) | Type::Collection(_) | Type::Domain(..) => ViperTcType::Top,
    }
}
