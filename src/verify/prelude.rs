//! Verifier builtins injected on entry — items the backend always provides,
//! regardless of how the VMIR was produced (Silver translation or hand-written).
//! Analogous to Rust's lang items: not part of any source program, supplied by
//! the compiler at the hand-off.
//!
//! Currently the only builtin is the generic `Option` ADT, used as the snapshot
//! membership type by `fold`/`unfold`. Once injected it is an ordinary
//! `Declaration::Adt`; the verifier locates it by the well-known name
//! [`OPTION`] and the monomorphization machinery treats it like any other
//! generic ADT.

use crate::vmir::{Adt, AdtVariant, Declaration, Program, Type};

/// The reserved interner name of the builtin `Option` ADT.
pub const OPTION: &str = "Option";

/// Return a copy of `program` with the verifier builtins appended. Builtin
/// declaration ids start past every existing id (preserving the interner/decls
/// index invariant), so existing ids — and any cached certificates keyed by
/// them — are unaffected.
pub fn with_prelude(program: &Program) -> Program {
    let mut program = program.clone();

    // Idempotent: if the builtins are already present, do nothing.
    if program.interner.get(OPTION).is_some() {
        return program;
    }

    // Generic `Option[T]`: `Some(T)` (variant 0, field 0 = the value) and
    // `None` (variant 1). The element type is the type parameter `Generic(0)`.
    let option = program.interner.get_or_intern(OPTION);
    debug_assert_eq!(usize::from(option), program.decls.len());
    program.decls.push(Declaration::Adt(Adt {
        variants: vec![
            AdtVariant {
                field_types: vec![Type::Generic(0)],
            },
            AdtVariant {
                field_types: vec![],
            },
        ],
    }));

    program
}
