//! Parse a Silver file, typecheck it, lower to VMIR, and print the resulting
//! `vmir::Program`.
//!
//! Usage: `cargo run --bin translate -- cases/foo.vpr`

use silver_oxide::translate;
use silver_oxide::viper::{
    GlobalsCollector, IdentCollector, disambiguate, inline_macros, typecheck_program, viper_parser,
    walk::AstWalkable,
};
use std::{error::Error, fs};

fn main() -> Result<(), Box<dyn Error>> {
    let file = std::env::args()
        .nth(1)
        .ok_or("usage: translate <file.vpr>")?;
    let input = fs::read_to_string(&file)?;

    let mut program = viper_parser::vpr_program(&input)?;

    let mut ident_collector = IdentCollector::default();
    program.walk_mut(&mut ident_collector);
    let interner = ident_collector.finalize();

    let mut globals_collector = GlobalsCollector::new(&interner);
    program.walk(&mut globals_collector);
    let globals = globals_collector.finalize().expect("globals error");

    disambiguate(&mut program, &interner, &globals).expect("disambiguation failed");
    inline_macros(&mut program, &interner).expect("macro inlining failed");

    let typed = typecheck_program(&mut program, &interner, &globals)
        .map_err(|e| format!("typecheck failed: {e:?}"))?;

    let vmir = translate::translate(&typed, &interner, &globals)
        .map_err(|e| format!("translation failed: {e:?}"))?;

    println!("{}", vmir);
    Ok(())
}
