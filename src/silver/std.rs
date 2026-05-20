use lasso::Spur;

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinType {
    Seq,
    Set,
    Multiset,
    Map,
}

impl Exp {
    pub fn unknown(exp: ExpKind) -> Self {
        Self {
            ty: InferenceType::Unknown,
            kind: Box::new(exp),
        }
    }
    pub fn impure(exp: ExpKind) -> Self {
        Self {
            ty: InferenceType::Impure,
            kind: Box::new(exp),
        }
    }
}

impl Ident {
    // pub fn set() -> Self {
    //     Self("Set".to_string())
    // }
    //
    // pub fn multiset() -> Self {
    //     Self("Multiset".to_string())
    // }
    //
    // pub fn seq() -> Self {
    //     Self("Seq".to_string())
    // }
    //
    // pub fn map() -> Self {
    //     Self("Map".to_string())
    // }

    // pub fn builtin_type(&self) -> Option<BuiltinType> {
    //     let bt = match self.0.as_str() {
    //         "Set" => BuiltinType::Set,
    //         "Multiset" => BuiltinType::Multiset,
    //         "Seq" => BuiltinType::Seq,
    //         "Map" => BuiltinType::Map,
    //         _ => return None,
    //     };
    //     Some(bt)
    // }

    pub fn id(&self) -> Spur {
        match self {
            Self::Interned(id) => *id,
            _ => panic!("Expected identifier to be interned"),
        }
    }
}

impl ConstKind {
    pub fn bool(b: bool) -> Self {
        ConstKind::Bool(b)
    }

    pub fn rational(n: isize) -> num::BigRational {
        num::BigInt::from(n).into()
    }

    pub fn none() -> Self {
        ConstKind::Real(ConstKind::rational(0))
    }

    pub fn write() -> Self {
        ConstKind::Real(ConstKind::rational(1))
    }

    pub fn wildcard() -> Self {
        ConstKind::Wildcard
    }
}

impl From<ConstKind> for Exp {
    fn from(value: ConstKind) -> Self {
        Exp::impure(ExpKind::Const(value))
    }
}

impl ExpKind {
    pub fn bool(b: bool) -> Exp {
        ConstKind::bool(b).into()
    }

    pub fn none() -> Exp {
        ConstKind::none().into()
    }

    pub fn write() -> Exp {
        ConstKind::write().into()
    }

    pub fn wildcard() -> Exp {
        ConstKind::wildcard().into()
    }
}

impl Signature {
    pub fn field(f: IdnDeclTyped) -> Self {
        Self {
            name: f.idn,
            args: vec![ArgOrType::Type(Type::Ref)],
            ret: vec![ArgOrType::Type(f.ty)],
        }
    }
}
