use silver_oxide::{silver_parser, translate::VmirTranslator};
use std::{error::Error, fs};

fn main() -> Result<(), Box<dyn Error>> {
    let file = std::env::args().skip(1).next().unwrap();
    let input = fs::read_to_string(file)?;
    let program = silver_parser::sil_program(&input)?;

    println!("=== Silver AST ===");
    println!("{:#?}", program);

    let vmir_program = VmirTranslator::translate(&program).unwrap();

    println!("\n=== VMIR AST (Debug) ===");
    println!("{:#?}", vmir_program);

    println!("\n=== VMIR AST (Display) ===");
    println!("{}", vmir_program);

    Ok(())
}
