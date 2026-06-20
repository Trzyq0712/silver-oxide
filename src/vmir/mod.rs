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
pub use function::{Bound, Function, FunctionCall, Location};
pub use inst::{Inst, InstKind, PathConds, Polarity};
pub use method::Method;
pub use resource::{Precond, Resource, ResourceBody, ResourceCall, Snapshot};

use derive_more::{From, Into};
use lasso::{Key, Rodeo};
use typed_index_collections::TiVec;

#[derive(Debug, From, Into, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct MemberId(pub usize);

unsafe impl Key for MemberId {
    fn into_usize(self) -> usize {
        self.0
    }

    fn try_from_usize(int: usize) -> Option<Self> {
        Some(Self(int))
    }
}

/// The monomorphic `Option[T]` ADT declaration id for one element type. The
/// constructor/projection/tag ids are minted by the verifier (`verify::mono`),
/// keyed by this `adt_id`, so only the declaration id is recorded here.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OptionInstance {
    pub adt_id: MemberId,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub decls: TiVec<MemberId, Declaration>,
    pub interner: Rodeo<MemberId>,
    pub option_instances: std::collections::HashMap<Type, OptionInstance>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Declaration {
    Domain(Domain),
    Function(Function),
    Location(Location),
    Method(Method),
    Resource(Resource),
    Adt(Adt),
}
