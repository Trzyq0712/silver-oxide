//! Parse + typecheck + translate + verify.
//!
//! Usage: `cargo run --bin verify -- cases/foo.vpr`

use silver_oxide::pipeline;
use std::{error::Error, path::Path};

fn main() -> Result<(), Box<dyn Error>> {
    let file = std::env::args().nth(1).ok_or("usage: verify <file.vpr>")?;

    match pipeline::run_file_timed(Path::new(&file)) {
        Err(e) => eprintln!("[PIPELINE-ERROR] {e}"),
        Ok((results, timings, member_times, stats)) => {
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
            let mut breakdown = member_times.clone();
            breakdown.sort_by(|a, b| b.1.cmp(&a.1));
            eprintln!("[VERIFY-BREAKDOWN] (slowest first)");
            for (name, dur) in &breakdown {
                eprintln!("  {name:<24} {dur:>10.3?}");
            }
            eprintln!("[STATS] {stats:?}");
        }
    }

    Ok(())
}
