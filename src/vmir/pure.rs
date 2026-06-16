use crate::vmir::display::VmirDisplay;
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
pub enum PureInst {
    Fresh,
    Binary(BinOp, Val, Val),
    Ternary(Val, Val, Val),
    /// Cast an Int value to a Real
    RealCast(Val),
    /// Read a value from a heap at a given location.
    Deref(HeapVal, Val),
    /// Query the permission amount of an address in a heap.
    Perm(HeapVal, Val),
    /// A function application. The heap is the function's context heap, present
    /// only for heap-dependent functions (`None` for heap-independent ones).
    FunctionCall(Option<HeapVal>, FunctionCall),
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
            // Reals are permission amounts: always show as a fraction (no space),
            // e.g. `1/1`, `1/2`, `0/1` — never the reduced integer form.
            Literal::Real(v) => write!(f, "{}/{}", v.numer(), v.denom()),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a PureInst> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            PureInst::Fresh => write!(f, "fresh"),
            PureInst::Binary(op, lhs, rhs) => write!(f, "{lhs} {op} {rhs}"),
            PureInst::RealCast(v) => write!(f, "real({v})"),
            PureInst::Ternary(cond, then_val, else_val) => {
                write!(f, "{cond} ? {then_val} : {else_val}")
            }
            PureInst::Deref(heap, loc) => write!(f, "*[{heap}] {loc}"),
            PureInst::FunctionCall(heap, call) => {
                write!(f, "{}(", self.interner.resolve(&call.function))?;
                for (i, arg) in call.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")?;
                // Context heap only for heap-dependent functions.
                if let Some(heap) = heap {
                    write!(f, "[{heap}]")?;
                }
                Ok(())
            }
            PureInst::Perm(heap, loc) => write!(f, "perm[{heap}] {loc}"),
        }
    }
}
