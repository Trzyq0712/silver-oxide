//! Parse + typecheck + translate + verify.
//!
//! Usage: `cargo run --bin verifier -- cases/foo.vpr`

use silver_oxide::pipeline;
use std::{error::Error, path::Path};

fn main() -> Result<(), Box<dyn Error>> {
    let file = std::env::args()
        .nth(1)
        .ok_or("usage: verifier <file.vpr>")?;

    match pipeline::run_file_timed(Path::new(&file)) {
        Err(e) => eprintln!("[PIPELINE-ERROR] {e}"),
        Ok((results, timings)) => {
            if results.is_empty() {
                println!("[INFO] no method bodies to verify");
            } else {
                for (name, outcome) in &results {
                    match outcome {
                        Ok(()) => println!("  [OK] {name}"),
                        Err(e) => println!("  [FAIL] {name}: {e}"),
                    }
                }
            }
            eprintln!("[TIMING]\n{timings}");
        }
    }

    Ok(())
}
