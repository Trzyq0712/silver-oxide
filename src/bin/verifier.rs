use silver_oxide::{silver_parser, translate::VmirTranslator};
use std::{error::Error, fs};

fn main() -> Result<(), Box<dyn Error>> {
    let file = std::env::args().skip(1).next().unwrap_or_else(|| {
        eprintln!("Usage: verifier <viper-file>");
        std::process::exit(1);
    });

    let input = fs::read_to_string(&file)?;

    println!("=== Parsing Viper program ===");
    let silver_program = silver_parser::sil_program(&input)?;

    println!("\n=== Translating to VMIR ===");
    let vmir_program = VmirTranslator::translate(&silver_program).unwrap();

    println!("{}", vmir_program);

    // println!("\n=== Verifying VMIR program ===");
    // let verifier = Verifier::new(vmir_program);
    // let result = verifier.verify();
    //
    // println!("\n=== Verification Result ===");
    // if result.is_success() {
    //     println!("✓ Program verified successfully!");
    //     Ok(())
    // } else {
    //     println!("✗ Verification failed");
    //     for (id, res) in &result.results {
    //         if let Err(e) = res {
    //             println!("  Member {:?}: {}", id, e);
    //         }
    //     }
    //     std::process::exit(1);
    // }
    Ok(())
}
