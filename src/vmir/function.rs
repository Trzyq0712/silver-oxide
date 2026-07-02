use crate::vmir::display::VmirDisplay;
use crate::vmir::{HeapVal, Inst, MemberId, Precond, TyParams, Type, Val};
use lasso::Spur;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    pub name: Spur,
    /// Type-parameter arity — a function is generic only in the type-params used
    /// in its declaration (params/ret). `0` for a non-generic function; a lifted
    /// domain function carries its owning domain's arity.
    pub ty_params: TyParams,
    pub params: Params,
    pub ret: Type,
    /// Precondition framing. `SelfFramed` ⟹ precondition-free ⟹ **heap-free**
    /// (domain functions, field `@addr`s, precond-free functions).
    /// `Ctx(f#requires, args)` ⟹ the `#requires` resource framed at `args`
    /// supplies the context heap in `HeapVal::Temp(0)`. `args` are the *leading*
    /// params — for an `f#ensures` contract function they exclude the trailing
    /// `result` param.
    pub precond: Precond,
    /// The function's definition, when it has a body. `None` ⟹ abstract /
    /// uninterpreted. A boolean-returning contract function (`f#ensures`) stores
    /// its lowered postcondition here; a function *with* a postcondition ends its
    /// body by invoking its `f#ensures` and asserting the result. There is no
    /// postcondition builtin — the `f`→`f#ensures` link lives only in the
    /// frontend's `contracts` map, which stitches the definition-side `assert`
    /// and every use-side `assume`.
    pub body: Option<FunctionBody>,
}

/// A pure function body: a stream of pure/heap instructions plus the result
/// `Val`. Mirrors [`crate::vmir::ResourceBody`] but returns a single value with
/// no heap delta (a function produces a value, not a heap change).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionBody {
    pub insts: Vec<Inst>,
    pub res: Val,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Params(Vec<Type>);

impl From<Vec<Type>> for Params {
    fn from(v: Vec<Type>) -> Self {
        Self(v)
    }
}

impl FromIterator<Type> for Params {
    fn from_iter<I: IntoIterator<Item = Type>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

/// A function invocation.
///
/// A (possibly generic) function application. `type_args` records the result-type
/// instantiation for the verifier's `FuncApp` payload (empty for a fully-concrete
/// result). `heap` is the context heap — `Some` only for heap-dependent
/// (precond-carrying) functions; `None` for heap-free (precond-free / domain)
/// calls.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionCall {
    pub function: MemberId,
    pub type_args: Vec<Type>,
    pub heap: Option<HeapVal>,
    pub args: Args,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Args(Vec<Val>);

impl From<Vec<Val>> for Args {
    fn from(v: Vec<Val>) -> Self {
        Self(v)
    }
}

impl Args {
    pub fn iter(&self) -> std::slice::Iter<'_, Val> {
        self.0.iter()
    }
}

impl Display for VmirDisplay<'_, &'_ Params> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, param) in self.item.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{i}: {}", self.with(param))?;
        }
        write!(f, ")")
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Function> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);
        let params = &self.item.params;
        let ret = &self.item.ret;
        // `ty_params` renders the generic arity (`<1>`), or nothing when
        // non-generic.
        write!(
            f,
            "function {name}{}{} -> {}",
            self.item.ty_params,
            self.with(params),
            self.with(ret)
        )?;
        // A precondition resource frames the body's context heap in `h0`, so
        // body-emitted heaps start at `h1`; show it as `[req(a0, …)]`. A
        // self-framed (heap-free) function counts heaps from `h0`.
        let heap_base = match &self.item.precond {
            Precond::Ctx(req_id, args) => {
                write!(f, " [{}(", self.member(*req_id))?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")]")?;
                1usize
            }
            Precond::SelfFramed => 0usize,
        };
        match &self.item.body {
            None => Ok(()),
            Some(body) => {
                writeln!(f, " {{")?;
                write!(
                    f,
                    "{}",
                    self.with((self.item.params.0.len(), heap_base, &body.insts[..]))
                )?;
                writeln!(f, "  result: {}", body.res)?;
                write!(f, "}}")
            }
        }
    }
}

impl Display for Args {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, arg) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{arg}")?;
        }
        write!(f, ")")
    }
}

impl Display for VmirDisplay<'_, &'_ FunctionCall> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let function = self.member(self.item.function);
        let args = &self.item.args;
        // A heap-dependent (precond) call leads with `call[h] ` — the prefix flags
        // heap dependence and carries the context heap. A heap-free (precond-free)
        // call renders bare, like any other pure application.
        if let Some(heap) = &self.item.heap {
            write!(f, "call[{heap}] ")?;
        }
        write!(f, "{function}")?;
        // A generic call shows its full type-argument instantiation in angle
        // brackets (`[..]` is reserved for heaps / addr groups).
        if !self.item.type_args.is_empty() {
            write!(f, "<")?;
            for (i, t) in self.item.type_args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", self.with(t))?;
            }
            write!(f, ">")?;
        }
        write!(f, "{args}")
    }
}
