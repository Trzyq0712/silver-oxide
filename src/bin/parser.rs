use silver_oxide::silver_parser;
use std::{error::Error, fs};

fn main() -> Result<(), Box<dyn Error>> {
    let file = std::env::args().skip(1).next().unwrap();
    let input = fs::read_to_string(file)?;
    let program = silver_parser::sil_program(&input)?;

    dbg!(program);

    Ok(())
}
