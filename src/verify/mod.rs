use crate::vmir;

mod analysis;
mod context;
mod declaration;
mod heap;
pub mod lang;
mod meta;
mod mono;
mod prelude;
mod rewrite;
mod viz;

pub use declaration::{VerifyError, verify_resource};

/// Result for one verification unit (method or resource): its name and whether
/// verification succeeded.
pub type VerifyResult = (String, Result<(), VerifyError>);

/// Verify an already-analyzed program in dependency order. Returns one entry
/// per verification unit. Resources are verified self-contained (well-formed
/// side conditions) ahead of the methods that use them; methods are then
/// verified, reusing the resources' established proofs.
pub fn verify(analyzed: &vmir::AnalyzedProgram) -> Vec<VerifyResult> {
    // Inject verifier builtins (the `Option` ADT) on entry, so the rest of the
    // pipeline treats them like any other declaration.
    let program = prelude::with_prelude(&analyzed.program);
    let program = &program;
    let mut results = Vec::new();
    // Derive a linear order from the dependency graph; acyclicity was already
    // proven by `analyze`. A future parallel scheduler consumes the graph
    // directly instead.
    let order = petgraph::algo::toposort(&analyzed.dep_graph, None)
        .expect("dep_graph proven acyclic by analyze");
    // Resources are verified before the methods that use them (dependency
    // order), so each resource's proof certificate is cached and grafted at
    // call sites rather than re-walking the body.
    let mut certs: std::collections::HashMap<vmir::MemberId, context::ResourceCertificate> =
        std::collections::HashMap::new();
    for id in order {
        let name = program.interner.resolve(&id).to_string();
        let outcome = match &program.decls[id] {
            vmir::Declaration::Resource(r) => match declaration::verify_resource(program, &name, r)
            {
                Ok(cert) => {
                    if let Some(cert) = cert {
                        certs.insert(id, cert);
                    }
                    Some(Ok(()))
                }
                Err(e) => Some(Err(e)),
            },
            vmir::Declaration::Method(m) => {
                Some(declaration::verify_method(program, &name, m, &certs))
            }
            _ => None,
        };
        if let Some(outcome) = outcome {
            results.push((name, outcome));
        }
    }
    results
}
