use crate::vmir;

mod context;
mod heap;
pub mod lang;
mod method;

pub use method::VerifyError;

/// Result for one method: its name and whether verification succeeded.
pub type MethodResult = (String, Result<(), VerifyError>);

/// Verify all methods in `program`. Returns one entry per method body.
pub fn verify(program: &vmir::Program) -> Vec<MethodResult> {
    let mut results = Vec::new();
    for (id, decl) in program.decls.iter_enumerated() {
        if let vmir::Declaration::Method(m) = decl {
            let name = program.interner.resolve(&id).to_string();
            let outcome = method::verify_method(program, &name, m);
            results.push((name, outcome));
        }
    }
    results
}
