use crate::vmir::display::VmirDisplay;
use crate::vmir::{FunctionCall, HeapVal, MemberId};
use lasso::Rodeo;
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
pub enum PureInst<P> {
    Fresh,
    Binary(BinOp, Val, Val),
    Ternary(Val, Val, Val),
    /// Cast an Int value to Real (`real(v)`).
    RealCast(Val),
    Deref(HeapVal, Val),
    FunctionCall(HeapVal, FunctionCall),
    Ext(P),
}

impl<P: crate::vmir::inst::UsesPc> PureInst<P> {
    pub fn uses_pc(&self) -> bool {
        match self {
            PureInst::Fresh | PureInst::Ternary(..) | PureInst::RealCast(..) => false,
            PureInst::Binary(op, _, _) => matches!(op, BinOp::Div | BinOp::Mod),
            PureInst::Deref(..) | PureInst::FunctionCall(..) => true,
            PureInst::Ext(ext) => ext.uses_pc(),
        }
    }
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

/// Rendering hook for the `PureInst::Ext` payload. Implementors emit
/// the textual form of the extension (interner is provided for
/// `MemberId` lookups). The bound `P: PureExtRender` on the generic
/// `Display for VmirDisplay<&PureInst<P>>` impl below sidesteps HRTB
/// recursion in the trait solver — `PureInst<_>` doesn't impl this
/// trait, so the solver can't speculatively unify `P = PureInst<_>`.
pub trait PureExtRender {
    fn render(&self, f: &mut Formatter<'_>, interner: &Rodeo<MemberId>) -> fmt::Result;
}

impl PureExtRender for ! {
    fn render(&self, _: &mut Formatter<'_>, _: &Rodeo<MemberId>) -> fmt::Result {
        match *self {}
    }
}

impl<'a, P: PureExtRender> Display for VmirDisplay<'a, &'a PureInst<P>> {
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
                write!(f, ")[{heap}]")
            }
            PureInst::Ext(ext) => ext.render(f, self.interner),
        }
    }
}
