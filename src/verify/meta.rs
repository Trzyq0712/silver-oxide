//! Verifier-side ADT metadata, *derived* from the VMIR declarations.
//!
//! The structural facts (which functions are constructors, tags and field
//! projections) live on the `Adt` / `Resource` declarations themselves. The
//! verifier walks the decls once and materialises the reduction-rule inputs it
//! needs; nothing is carried as a side-table on `vmir::Program`.

use std::collections::HashMap;

use crate::vmir::{Declaration, MemberId, Program};

/// The reduction relations the e-graph rewrite rules consume.
#[derive(Debug, Clone, Default)]
pub struct AdtMeta {
    /// Per-ADT `@tag` function id → (constructor id → tag index). Drives the
    /// discriminator reduction `Adt@tag(ctor_C(..)) ⇒ index_C`.
    pub tag_fns: HashMap<MemberId, HashMap<MemberId, usize>>,
    /// Destructor accessor function id → `(constructor id, field index)`. Drives
    /// the projection reduction `accessor(ctor_C(a0..an)) ⇒ a_index`.
    pub dtors: HashMap<MemberId, (MemberId, usize)>,
}

/// Derive [`AdtMeta`] from a program's declarations: ADT constructors/tags/
/// projections, plus predicate snapshots (single-constructor ADTs whose
/// projections must also reduce).
pub fn derive_adt_meta(program: &Program) -> AdtMeta {
    let mut meta = AdtMeta::default();
    for decl in &program.decls {
        match decl {
            Declaration::Adt(adt) => {
                let mut ctor_tags = HashMap::new();
                for c in &adt.constructors {
                    ctor_tags.insert(c.ctor_fn, c.tag);
                    for (i, &proj) in c.projections.iter().enumerate() {
                        meta.dtors.insert(proj, (c.ctor_fn, i));
                    }
                }
                meta.tag_fns.insert(adt.tag_fn, ctor_tags);
            }
            Declaration::Resource(r) => {
                if let Some(snap) = &r.snapshot {
                    for (i, &proj) in snap.projs.iter().enumerate() {
                        meta.dtors.insert(proj, (snap.cons, i));
                    }
                }
            }
            _ => {}
        }
    }
    meta
}
