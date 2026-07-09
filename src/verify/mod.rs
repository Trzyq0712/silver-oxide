use crate::vmir;

mod analysis;
mod cert;
mod context;
mod declaration;
mod error;
mod func_registry;
mod heap;
pub mod lang;
mod rewrite;
mod stats;
mod types;
mod viz;

pub use error::VerifyError;
pub use stats::VerifyStats;

/// Result for one verification unit (method or resource): its name and whether
/// verification succeeded.
pub type VerifyResult = (String, Result<(), VerifyError>);

/// Verify an already-analyzed program in dependency order. Returns one entry
/// per verification unit. Resources are verified self-contained (well-formed
/// side conditions) ahead of the methods that use them; methods are then
/// verified, reusing the resources' established proofs.
pub fn verify(analyzed: &vmir::AnalyzedProgram) -> Vec<VerifyResult> {
    verify_with_stats(analyzed).0
}

/// Like [`verify`], but also returns the aggregated [`VerifyStats`] (e-graph
/// cost metrics) for the whole run — used by the performance regression tests.
pub fn verify_with_stats(analyzed: &vmir::AnalyzedProgram) -> (Vec<VerifyResult>, VerifyStats) {
    let program = &analyzed.program;
    let mut results = Vec::new();
    // Derive a linear order from the dependency graph; acyclicity was already
    // proven by `analyze`. A future parallel scheduler consumes the graph
    // directly instead.
    let order = petgraph::algo::toposort(&analyzed.dep_graph, None)
        .expect("dep_graph proven acyclic by analyze");
    // Refine the order: all functions/resources before any method (valid —
    // nothing ever depends on a method). Domain axioms are assumed in every
    // unit and may call Silver functions; verifying methods last guarantees
    // every function certificate exists by the time the main assertion-bearing
    // units (methods) assume the axioms. (Inside the function/resource passes
    // an axiom mentioning a not-yet-verified function stays sound — the call
    // is merely uninterpreted, i.e. weaker.)
    let (early, methods): (Vec<_>, Vec<_>) = order
        .into_iter()
        .partition(|&id| !matches!(program.decls[id], vmir::Declaration::Method(_)));
    let order = early.into_iter().chain(methods);
    // Resources are verified before the methods that use them (dependency
    // order), so each resource's proof certificate is cached and grafted at
    // call sites rather than re-walking the body.
    let mut certs: std::collections::HashMap<vmir::MemberId, cert::ResourceDefinition> =
        std::collections::HashMap::new();
    // Verified function bodies, cached in dependency order (callees before
    // callers). Each unit's `assume_axioms` installs one lazy unfold rule per
    // entry here (see `rewrite::function_rule`), which installs the
    // definitional equality `f(args) == body` the moment a `FuncApp(f, ..)`
    // occurrence is seen during that unit's own saturation.
    let mut fn_certs: std::collections::HashMap<
        vmir::MemberId,
        std::sync::Arc<cert::FunctionDefinition>,
    > = std::collections::HashMap::new();
    // Shared function-id registry: one per run so ADT/builtin ids stay
    // consistent across certificate grafts. Threaded `&mut` into each unit.
    let mut alloc = func_registry::FuncRegistry::new(program);
    for id in order {
        let name = program.name(id).to_string();
        let outcome = match &program.decls[id] {
            vmir::Declaration::Resource(r) => {
                match declaration::verify_resource(program, &name, r, &certs, &fn_certs, &mut alloc)
                {
                    Ok(cert) => {
                        if let Some(cert) = cert {
                            certs.insert(id, cert);
                        }
                        Some(Ok(()))
                    }
                    Err(e) => Some(Err(e)),
                }
            }
            vmir::Declaration::Function(f) => {
                match declaration::verify_function(program, &name, f, &certs, &fn_certs, &mut alloc)
                {
                    // Abstract functions produce no certificate and no result row.
                    Ok(None) => None,
                    Ok(Some(cert)) => {
                        fn_certs.insert(id, cert);
                        Some(Ok(()))
                    }
                    Err(e) => Some(Err(e)),
                }
            }
            vmir::Declaration::Method(m) => Some(declaration::verify_method(
                program, &name, m, &certs, &fn_certs, &mut alloc,
            )),
            _ => None,
        };
        if let Some(outcome) = outcome {
            results.push((name, outcome));
        }
    }
    let stats = alloc.into_stats();
    (results, stats)
}
