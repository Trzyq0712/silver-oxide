use silver_oxide::{silver_parser, translate::VmirTranslator, silver::walk::AstWalker};
use std::{error::Error, fs};

fn main() -> Result<(), Box<dyn Error>> {
    let file = std::env::args().skip(1).next().unwrap();
    let input = fs::read_to_string(file)?;
    let program = silver_parser::sil_program(&input)?;

    println!("=== Silver AST ===");
    println!("{:#?}", program);

    let mut translator = VmirTranslator::new();
    translator.walk_program(&program);

    println!("\n=== VMIR AST (Debug) ===");
    println!("{:#?}", translator.program);

    println!("\n=== VMIR AST (Display) ===");
    println!("{}", translator.program);

    Ok(())
}
