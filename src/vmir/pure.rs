use crate::vmir::{FunctionCall, HeapVal};
use std::fmt::{self, Display, Formatter};

/// A value can be either a literal or a temporary variable defined earlier.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Val {
    Literal(Literal),
    Temp(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinOp {
    Plus,
    Minus,
    Mult,
    /// SIDECOND: The second operand must be non-zero.
    Div,
    /// SIDECOND: The second operand must be non-zero.
    Mod,
    Eq,
    Lt,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Null,
    Bool(bool),
    Int(num::BigInt),
    Real(num::BigRational),
}

pub const NULL: Val = Val::Literal(Literal::Null);
pub const TRUE: Val = Val::Literal(Literal::Bool(true));
pub const FALSE: Val = Val::Literal(Literal::Bool(false));

pub fn none() -> Val {
    Val::Literal(Literal::Real(num::BigInt::from(0).into()))
}
pub fn write() -> Val {
    Val::Literal(Literal::Real(num::BigInt::from(1).into()))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PureInst<P> {
    Fresh,
    Binary(BinOp, Val, Val),
    Ternary(Val, Val, Val),
    Deref(HeapVal, Val),
    FunctionCall(HeapVal, FunctionCall),
    Ext(P),
}

// ======================
// DISPLAY INFRASTRUCTURE
// ======================

impl Display for Val {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Val::Literal(lit) => write!(f, "{lit}"),
            Val::Temp(i) => write!(f, "e{i}"),
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let op = match self {
            BinOp::Plus => "+",
            BinOp::Minus => "-",
            BinOp::Mult => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Eq => "==",
            BinOp::Lt => "<",
        };
        write!(f, "{op}")
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Null => write!(f, "null"),
            Literal::Bool(b) => write!(f, "{b}"),
            Literal::Int(v) => write!(f, "{v}"),
            Literal::Real(v) => write!(f, "{v}"),
        }
    }
}

/// Generate a `Display for VmirDisplay<'_, &'_ PureInst<$p>>` impl for a
/// concrete extension payload type `$p`. We instantiate per-`p` rather
/// than as a fully generic impl to avoid the HRTB recursion the Rust
/// trait solver hits when proving
/// `VmirDisplay<&PureInst<X>>: Display` for unbounded `X`.
#[macro_export]
macro_rules! impl_pure_inst_display {
    ($p:ty) => {
        impl<'a> ::std::fmt::Display
            for $crate::vmir::display::VmirDisplay<'a, &'a $crate::vmir::PureInst<$p>>
        where
            $crate::vmir::display::VmirDisplay<'a, &'a $p>: ::std::fmt::Display,
        {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                use $crate::vmir::PureInst;
                match self.item {
                    PureInst::Fresh => write!(f, "fresh"),
                    PureInst::Binary(op, lhs, rhs) => write!(f, "{lhs} {op} {rhs}"),
                    PureInst::Ternary(cond, then_val, else_val) => {
                        write!(f, "{cond} ? {then_val} : {else_val}")
                    }
                    PureInst::Deref(heap, loc) => write!(f, "*[{heap}] {loc}"),
                    PureInst::FunctionCall(heap, call) => {
                        write!(f, "{}[{heap}](", self.interner.resolve(&call.function))?;
                        for (i, arg) in call.args.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{arg}")?;
                        }
                        write!(f, ")")
                    }
                    PureInst::Ext(ext) => write!(f, "{}", self.with(ext)),
                }
            }
        }
    };
}
