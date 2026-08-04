use crate::vmir::display::VmirDisplay;
use crate::vmir::{FunctionCall, HeapVal, MemberId, Type};
use std::fmt::{self, Display, Formatter};

/// A value can be either a literal or a temporary variable defined earlier.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Val {
    Literal(Literal),
    Temp(usize),
}

/// A binary operator, **tagged with the sort of its operands** (`I` = `Int`,
/// `R` = `Real`, i.e. Viper's `Perm`).
///
/// Viper writes one `+` for both integer and permission addition; the sort is
/// recovered during lowering, where the typed AST still has it. Carrying it on the
/// operator is what lets an e-graph rewrite *produce* a literal: `x - x => 0` has
/// no operand literal to read a sort off, and the wrong choice puts an `Int` and a
/// `Real` literal in one e-class — a type error the analysis panics on.
///
/// `Eq` is deliberately **not** tagged: it also compares `Bool`, `Ref`, ADTs and
/// snapshots, so a two-sort tag does not fit it, and none of its rules need to
/// synthesise a typed literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinOp {
    AddI,
    AddR,
    SubI,
    SubR,
    MulI,
    MulR,
    /// SIDECOND: The second operand must be non-zero.
    DivI,
    /// SIDECOND: The second operand must be non-zero.
    DivR,
    /// SIDECOND: The second operand must be non-zero. `Int`-only by typing, so
    /// it needs no sort tag.
    Mod,
    LtI,
    LtR,
    /// Polymorphic over every type — see the type note above.
    Eq,
}

impl BinOp {
    /// The operand sort, or `None` for the polymorphic `Eq`.
    pub fn sort(self) -> Option<Type> {
        use BinOp::*;
        match self {
            AddI | SubI | MulI | DivI | Mod | LtI => Some(Type::Int),
            AddR | SubR | MulR | DivR | LtR => Some(Type::Real),
            Eq => None,
        }
    }

    /// Whether this is the division-or-modulo family, whose non-zero-divisor
    /// side condition is checked without consulting a heap.
    pub fn is_div_or_mod(self) -> bool {
        matches!(self, BinOp::DivI | BinOp::DivR | BinOp::Mod)
    }

    /// Whether this is one of the additive operators, in either sort.
    pub fn is_additive(self) -> bool {
        matches!(self, BinOp::AddI | BinOp::AddR | BinOp::SubI | BinOp::SubR)
    }
}

/// Pick the sort-tagged operator for `ty`. Each panics on a non-numeric operand
/// type: the typed Viper AST has already rejected `+` on a `Bool` or an ADT, so
/// reaching one of these means the lowering handed over the wrong type, and
/// silently guessing a sort would plant a type error deep in the e-graph.
macro_rules! sorted_ctor {
    ($($name:ident => $int:ident / $real:ident),* $(,)?) => {
        impl BinOp {
            $(
                pub fn $name(ty: &Type) -> BinOp {
                    match ty {
                        Type::Int => BinOp::$int,
                        Type::Real => BinOp::$real,
                        other => panic!(
                            concat!("`", stringify!($name), "` on a non-numeric operand type: {:?}"),
                            other
                        ),
                    }
                }
            )*
        }
    };
}

sorted_ctor! {
    add => AddI / AddR,
    sub => SubI / SubR,
    mul => MulI / MulR,
    div => DivI / DivR,
    lt  => LtI  / LtR,
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
    /// A (possibly generic) Silver `function` application. Always pure and
    /// heap-free: a heap-dependent function takes its precondition **snapshot**
    /// (built by [`PureInst::Snap`] at the call site) as an ordinary trailing
    /// argument. Generics (`type_args`) live inside the `FunctionCall`.
    FunctionCall(FunctionCall),
    /// `snap[heap] R(args)` — narrow `heap` to the snapshot of the self-framed
    /// resource `R(args)`: the tuple of `heap`'s chunk values at `R`'s footprint
    /// addresses, each member `present ? Some(v) : None`. Produces a `Val` of
    /// type `Type::Snap(resource)`.
    ///
    /// SIDECOND (implicit precondition check, exhale-shaped, **no** heap
    /// mutation): for every footprint slot, `heap` must hold sufficient
    /// permission (`perm(heap, addr_k) >= perm_k`) under the pc, and the
    /// resource's boolean condition is **asserted**. No separate
    /// `Assert`/`Assume` is emitted around this instruction.
    Snap {
        resource: MemberId,
        args: Vec<Val>,
        heap: HeapVal,
    },
    /// Construct ADT value: variant `variant` of the ADT `adt` instantiated at
    /// `type_args`, over `args`. The ADT is named by its (possibly generic)
    /// declaration `MemberId`; `type_args` is its monomorphization (empty for a
    /// non-generic ADT). Replaces a synthetic-constructor `FunctionCall`.
    AdtCons {
        adt: crate::vmir::MemberId,
        type_args: Vec<crate::vmir::Type>,
        variant: usize,
        args: Vec<Val>,
    },
    /// Project field `field` of variant `variant` of the ADT `adt` instantiated
    /// at `type_args`, from `base` (`field`-th constructor argument). Replaces a
    /// synthetic-destructor `FunctionCall`.
    AdtProj {
        adt: crate::vmir::MemberId,
        type_args: Vec<crate::vmir::Type>,
        variant: usize,
        field: usize,
        base: Val,
    },
    /// The discriminator tag (variant index) of `base : adt[type_args]`.
    /// Replaces a synthetic `@tag` `FunctionCall`.
    AdtTag {
        adt: crate::vmir::MemberId,
        type_args: Vec<crate::vmir::Type>,
        base: Val,
    },
    /// An inline, nestable pure `forall` (see [`Forall`](crate::vmir::Forall)).
    /// Produces the quantified `Bool`; its captures are values of *this* temp
    /// space, its body a self-contained stream in its own.
    Forall(Box<crate::vmir::Forall>),
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
        // The sort suffix is part of the token (`+i` / `+r`), so a VMIR dump and
        // an e-graph rewrite pattern name the same operator the same way.
        let op = match self {
            BinOp::AddI => "+i",
            BinOp::AddR => "+r",
            BinOp::SubI => "-i",
            BinOp::SubR => "-r",
            BinOp::MulI => "*i",
            BinOp::MulR => "*r",
            BinOp::DivI => "/i",
            BinOp::DivR => "/r",
            BinOp::Mod => "%",
            BinOp::LtI => "<i",
            BinOp::LtR => "<r",
            BinOp::Eq => "==",
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
            PureInst::Snap {
                resource,
                args,
                heap,
            } => {
                write!(f, "snap[{heap}] {}(", self.member(*resource))?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            // `FunctionCall` renders itself (`name[heap](args)`) via its own
            // `VmirDisplay` impl, which resolves the callee `MemberId` → name.
            PureInst::FunctionCall(call) => write!(f, "{}", self.with(call)),
            PureInst::Perm(heap, loc) => write!(f, "perm[{heap}] {loc}"),
            PureInst::AdtCons {
                adt, variant, args, ..
            } => {
                write!(f, "{}(", self.adt_variant(*adt, *variant))?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            PureInst::AdtProj {
                adt,
                variant,
                field,
                base,
                ..
            } => write!(f, "{}.{field}({base})", self.adt_variant(*adt, *variant)),
            PureInst::AdtTag { adt, base, .. } => {
                write!(f, "{}@tag({base})", self.member(*adt))
            }
            PureInst::Forall(q) => write!(f, "{}", self.with(&**q)),
        }
    }
}
