//! Reads a Silver program from stdin, runs the full pre-processing pipeline
//! (intern → globals → resolve calls → inline macros → typecheck) and debug-dumps
//! the resulting typed `final_ast::Program`, so the inferred types can be inspected.
//!
//! Usage: `cargo run --bin typecheck < cases/foo.vpr`

use silver_oxide::silver::{
    GlobalsCollector, IdentCollector, inline_macros, resolve_call_kinds, show, silver_parser,
    typecheck_program, walk::AstWalkable,
};
use std::io::Read;

fn main() {
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .expect("read stdin");

    let mut program = silver_parser::sil_program(&input).expect("parse failed");

    let mut ident_collector = IdentCollector::default();
    program.walk_mut(&mut ident_collector);
    let interner = ident_collector.finalize();

    let mut globals_collector = GlobalsCollector::new(&interner);
    program.walk(&mut globals_collector);
    let globals = globals_collector.finalize().expect("globals error");

    resolve_call_kinds(&mut program, &interner, &globals).expect("call resolution failed");
    inline_macros(&mut program, &interner).expect("macro inlining failed");

    match typecheck_program(&mut program, &interner, &globals) {
        Ok(typed) => {
            eprintln!("typecheck OK");
            println!("{}", show(&typed, &interner));
        }
        Err(errors) => {
            eprintln!("typecheck FAILED with {} error(s):", errors.len());
            for e in &errors {
                eprintln!("  - {e}");
            }
            std::process::exit(1);
        }
    }
}
