mod adt;
mod analyze;
mod domain;
mod function;
mod heap;
mod inst;
mod method;
mod pure;
mod resource;
mod ty;

pub mod display;

pub use ty::Type;

pub use heap::{Assign, HeapInst, HeapVal, Sign};
pub use pure::{BinOp, FALSE, Literal, NULL, PureInst, TRUE, Val, none, write};

pub use adt::{Adt, AdtVariant};
pub use analyze::{AnalysisError, AnalyzedProgram, DepGraph, analyze};
pub use domain::Domain;
pub use function::{Function, FunctionCall};
pub use inst::{Inst, InstKind, PathConds, Polarity};
pub use method::Method;
pub use resource::{Precond, Resource, ResourceBody, ResourceCall, Snapshot};
pub use ty::Bound;

use derive_more::{From, Into};
use lasso::{Rodeo, Spur};
use typed_index_collections::TiVec;

/// A dense index into [`Program::decls`]. Purely positional — it is **not** an
/// interner key; names are resolved through [`Program::name`].
#[derive(Debug, From, Into, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct MemberId(pub usize);

#[derive(Debug, Clone)]
pub struct Program {
    pub decls: TiVec<MemberId, Declaration>,
    /// Each member's name, for display/debug. VMIR proper references members by
    /// `MemberId`, never by name.
    pub names: TiVec<MemberId, Spur>,
    /// Cheap string repr for member (and constructor) names. Its `Spur` keys are
    /// independent of `MemberId`.
    pub interner: Rodeo,
    /// Location **group** tags (`Type::Addr.group`), interned separately — a group
    /// is just a name, never a declaration.
    pub groups: Rodeo<Spur>,
}

impl Program {
    /// The display name of a member.
    pub fn name(&self, id: MemberId) -> &str {
        self.interner.resolve(&self.names[id])
    }

    /// The member with the given name, if any. A linear scan — for tests/debug
    /// only; VMIR proper never looks a member up by string.
    pub fn id(&self, name: &str) -> Option<MemberId> {
        let s = self.interner.get(name)?;
        self.names
            .iter_enumerated()
            .find(|(_, n)| **n == s)
            .map(|(id, _)| id)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Declaration {
    Domain(Domain),
    Function(Function),
    Method(Method),
    Resource(Resource),
    Adt(Adt),
}
