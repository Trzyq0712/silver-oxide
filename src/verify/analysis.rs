use std::collections::HashMap;
use std::sync::Arc;

use egg::{Analysis, DidMerge, EGraph, Id};
use num::BigRational;

use crate::verify::lang::{FuncId, Symbolic};
use crate::vmir::{BinOp, Literal, MemberId, Type};

/// Const-fold analysis data: a three-state lattice over an e-class's folded
/// value. **Type-free**: only the literal is tracked (types are reconstructed
/// for visualization from the side oracle in `verify::context`).
///
/// - `Unknown`: not (yet) a constant.
/// - `Known(lit)`: folds to `lit`.
/// - `Ctor(f, tys)`: the e-class holds an application of ADT constructor `f` at
///   instantiation `tys`. This is what gives us **constructor distinctness**
///   without the SMT tag encoding: an SMT solver cannot enumerate the terms of an
///   equivalence class, so it must project class membership into a `tag(..)` term
///   and pay O(variants) axioms plus a trigger to fire them. Here the closure is
///   the data structure, so a variant clash is just a lattice conflict — no
///   axioms, no `tag` term needed, and it is detected even when the program never
///   mentions a discriminator.
/// - `Inconsistent`: two **same-typed** literals of differing value were merged
///   (e.g. `true == false`, `5 == 6`), or two **different constructors of one ADT
///   head at one instantiation** were merged (ADT constructors are free, so
///   `Cons(..) == Nil` is a contradiction) — the e-class, and thus the whole
///   verification unit, is contradictory. Merging across *different* types
///   (literals of different types, or constructors of different heads /
///   instantiations) is instead a verifier panic: a genuine type error, not a
///   fact about the program.
#[derive(Debug, Clone, PartialEq)]
pub enum Data {
    Unknown,
    Known(Literal),
    Ctor(FuncId, Box<[Type]>),
    Inconsistent,
}

impl Data {
    /// The folded literal, if this e-class is a known constant.
    pub fn known(&self) -> Option<&Literal> {
        match self {
            Data::Known(lit) => Some(lit),
            _ => None,
        }
    }

    /// Whether this e-class merged conflicting same-typed literals.
    pub fn is_inconsistent(&self) -> bool {
        matches!(self, Data::Inconsistent)
    }
}

/// Whether two literals are of the same VMIR type (so a value conflict is an
/// inconsistency rather than a type error).
fn same_type(a: &Literal, b: &Literal) -> bool {
    use Literal::*;
    matches!(
        (a, b),
        (Bool(_), Bool(_)) | (Int(_), Int(_)) | (Real(_), Real(_)) | (Null, Null)
    )
}

#[derive(Default, Debug, Clone)]
pub struct ConstFold {
    /// Constructor id → the ADT head it belongs to (from
    /// `FuncRegistry::ctor_table`). Any `FuncApp` whose id is absent is an
    /// ordinary function, not a constructor. Empty by default (tests without
    /// ADTs), which simply disables the distinctness lattice.
    ctors: Arc<HashMap<FuncId, MemberId>>,
}

impl ConstFold {
    pub fn new(ctors: Arc<HashMap<FuncId, MemberId>>) -> Self {
        Self { ctors }
    }

    /// The ADT head of `f`, if `f` is a constructor.
    fn head_of(&self, f: FuncId) -> Option<MemberId> {
        self.ctors.get(&f).copied()
    }
}

impl Analysis<Symbolic> for ConstFold {
    type Data = Data;

    fn make(egraph: &mut EGraph<Symbolic, Self>, enode: &Symbolic, _id: Id) -> Self::Data {
        use Data::{Ctor, Inconsistent, Known, Unknown};
        match enode {
            Symbolic::Lit(lit) => Known(lit.clone()),

            Symbolic::FuncApp(f, tys, _) if egraph.analysis.head_of(*f).is_some() => {
                Ctor(*f, tys.clone())
            }

            // A quantifier is opaque to constant folding: its truth is decided by
            // the instantiation rule (guarded merges with `true`), never by its
            // payload or its capture children.
            Symbolic::Fresh(_)
            | Symbolic::Wildcard(_)
            | Symbolic::FuncApp(..)
            | Symbolic::Forall(..) => Unknown,

            Symbolic::RealCast(c) => match &egraph[*c].data {
                Known(Literal::Int(n)) => Known(Literal::Real(BigRational::from(n.clone()))),
                Known(_) | Ctor(..) => unreachable!("RealCast operand must be an integer literal"),
                Inconsistent => Inconsistent,
                Unknown => Unknown,
            },

            Symbolic::Binary(op, [l, r]) => match (&egraph[*l].data, &egraph[*r].data) {
                (Inconsistent, _) | (_, Inconsistent) => Inconsistent,
                // Disequality, the other half of what the SMT `tag` encoding buys:
                // distinct constructors of one ADT are distinct values, so an `==`
                // between them folds to `false` outright. No `tag` term and no
                // `tag_bounds` axiom needed — the constructor identity is right
                // there in the operand's e-class.
                (Ctor(f, ftys), Ctor(g, gtys))
                    if *op == BinOp::Eq
                        && f != g
                        && ftys == gtys
                        && egraph.analysis.head_of(*f) == egraph.analysis.head_of(*g) =>
                {
                    Known(Literal::Bool(false))
                }
                (Known(lv), Known(rv)) => eval_binary(*op, lv, rv).map_or(Unknown, Known),
                _ => Unknown,
            },

            Symbolic::Ite([c, t, e]) => match &egraph[*c].data {
                Known(Literal::Bool(true)) => egraph[*t].data.clone(),
                Known(Literal::Bool(false)) => egraph[*e].data.clone(),
                Known(_) | Ctor(..) => unreachable!("Condition of ITE must be a boolean literal"),
                Inconsistent => Inconsistent,
                Unknown => Unknown,
            },
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        use Data::{Ctor, Inconsistent, Known, Unknown};
        match (&*a, &b) {
            (Inconsistent, Inconsistent) => DidMerge(false, false),
            (Inconsistent, _) => DidMerge(false, true),
            (_, Inconsistent) => {
                *a = Inconsistent;
                DidMerge(true, false)
            }
            (Ctor(f, ftys), Ctor(g, gtys)) => {
                // Distinctness. Only comparable within one instantiation: the type
                // args are part of the operator's identity (the polymorphic
                // e-graph keeps `List[Int]::Nil` and `List[Bool]::Nil` apart by
                // discriminant), so a clash across instantiations is a type error,
                // not a contradiction.
                let (fh, gh) = (self.head_of(*f), self.head_of(*g));
                if fh != gh || ftys != gtys {
                    panic!(
                        "type error: merged constructors of different ADTs or \
                         instantiations: {f:?}{ftys:?} vs {g:?}{gtys:?}"
                    );
                }
                if f == g {
                    DidMerge(false, false)
                } else {
                    // Distinct variants of one ADT, same instantiation: free
                    // constructors are disjoint, so this class is contradictory.
                    *a = Inconsistent;
                    DidMerge(true, true)
                }
            }
            (Ctor(..), Known(lit)) | (Known(lit), Ctor(..)) => {
                panic!("type error: merged an ADT constructor with a literal: {lit:?}")
            }
            (Unknown, Ctor(..)) => {
                *a = b;
                DidMerge(true, false)
            }
            (Ctor(..), Unknown) => DidMerge(false, true),
            (Known(x), Known(y)) => {
                if x == y {
                    DidMerge(false, false)
                } else if same_type(x, y) {
                    // Same-typed conflict ⇒ contradiction (not a panic).
                    *a = Inconsistent;
                    DidMerge(true, true)
                } else {
                    panic!("type error: merged literals of different types: {x:?} vs {y:?}");
                }
            }
            (Unknown, Known(y)) => {
                *a = Known(y.clone());
                DidMerge(true, false)
            }
            (Known(_), Unknown) => DidMerge(false, true),
            (Unknown, Unknown) => DidMerge(false, false),
        }
    }

    fn modify(egraph: &mut EGraph<Symbolic, Self>, id: Id) {
        if let Data::Known(lit) = egraph[id].data.clone() {
            let lit_id = egraph.add(Symbolic::Lit(lit));
            egraph.union(id, lit_id);
        }
    }
}

/// Fold a binary op over two literals. The operator names its own operand sort,
/// so each arm matches exactly one literal pair; a mismatch means the operand
/// does not have the sort the operator claims, which is a lowering bug rather
/// than something to fold.
///
/// `None` for a literal division by zero: the term is unspecified (an
/// uninterpreted value, matching SMT semantics), not a fold-time panic —
/// well-definedness is a separate obligation, and never checked at all inside
/// an axiom body.
pub fn eval_binary(op: BinOp, l: &Literal, r: &Literal) -> Option<Literal> {
    use Literal::{Int, Real};
    /// Destructure the operands at the sort the operator declares, or panic.
    macro_rules! operands {
        ($variant:ident) => {
            match (l, r) {
                ($variant(a), $variant(b)) => (a, b),
                _ => unreachable!(
                    "operands are not {} for {op:?}: {l:?}, {r:?}",
                    stringify!($variant)
                ),
            }
        };
    }
    Some(match op {
        BinOp::AddI => {
            let (a, b) = operands!(Int);
            Int(a + b)
        }
        BinOp::AddR => {
            let (a, b) = operands!(Real);
            Real(a + b)
        }
        BinOp::SubI => {
            let (a, b) = operands!(Int);
            Int(a - b)
        }
        BinOp::SubR => {
            let (a, b) = operands!(Real);
            Real(a - b)
        }
        BinOp::MulI => {
            let (a, b) = operands!(Int);
            Int(a * b)
        }
        BinOp::MulR => {
            let (a, b) = operands!(Real);
            Real(a * b)
        }
        BinOp::Mod => {
            let (a, b) = operands!(Int);
            if *b == num::BigInt::ZERO {
                return None;
            }
            Int(a % b)
        }
        BinOp::DivI => {
            let (a, b) = operands!(Int);
            if *b == num::BigInt::ZERO {
                return None;
            }
            Int(a / b)
        }
        BinOp::DivR => {
            let (a, b) = operands!(Real);
            if *b == num::BigRational::from(num::BigInt::ZERO) {
                return None;
            }
            Real(a / b)
        }
        BinOp::LtI => {
            let (a, b) = operands!(Int);
            Literal::Bool(a < b)
        }
        BinOp::LtR => {
            let (a, b) = operands!(Real);
            Literal::Bool(a < b)
        }
        BinOp::Eq => Literal::Bool(l == r),
    })
}
