use crate::vmir;

mod context;
mod heap;
mod heap_exp;
pub mod lang;
mod method;

pub fn verify(program: &vmir::Program) {
    for (id, decl) in program.decls.iter_enumerated() {
        if let vmir::Declaration::Method(method) = decl {
            let method_name = program.interner.resolve(&id);
            method::verify_method(program, method_name, method);
        }
    }
}
