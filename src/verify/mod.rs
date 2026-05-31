use crate::vmir;

mod analysis;
mod context;
mod heap;
pub mod lang;
mod method;

pub use method::VerifyError;

/// Result for one method: its name and whether verification succeeded.
pub type MethodResult = (String, Result<(), VerifyError>);

/// Verify an already-analyzed program in dependency order. Returns one
/// entry per method body. Resources and functions are scheduled ahead of
/// methods but are not verified yet (future work); only method bodies are
/// verified.
pub fn verify(analyzed: &vmir::AnalyzedProgram) -> Vec<MethodResult> {
    let program = &analyzed.program;
    let mut results = Vec::new();
    for &id in &analyzed.order {
        if let vmir::Declaration::Method(m) = &program.decls[id] {
            let name = program.interner.resolve(&id).to_string();
            let outcome = method::verify_method(program, &name, m);
            results.push((name, outcome));
        }
    }
    results
}
