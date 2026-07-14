//! Parse + typecheck + translate + verify.
//!
//! Usage: `cargo run --bin verify -- [--breakdown] cases/foo.vpr`
//!
//! `--breakdown` (`-b`) prints per-member verify times, slowest first.

use silver_oxide::pipeline;
use std::{error::Error, path::Path};

fn main() -> Result<(), Box<dyn Error>> {
    let mut file = None;
    let mut breakdown = false;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--breakdown" | "-b" => breakdown = true,
            _ => file = Some(arg),
        }
    }
    let file = file.ok_or("usage: verify [--breakdown] <file.vpr>")?;

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
            if breakdown {
                let mut rows = member_times.clone();
                rows.sort_by(|a, b| b.1.cmp(&a.1));
                eprintln!("[VERIFY-BREAKDOWN] (slowest first)");
                for (name, dur) in &rows {
                    eprintln!("  {name:<24} {dur:>10.3?}");
                }
                let mut rules: Vec<_> = stats.rule_timing.0.iter().collect();
                rules.sort_by(|a, b| (b.1.search + b.1.apply).total_cmp(&(a.1.search + a.1.apply)));
                eprintln!("[RULE-TIMING] (search+apply, slowest first)");
                for (name, t) in rules.iter().take(20) {
                    eprintln!(
                        "  {name:<40} search {:>8.1}ms  apply {:>8.1}ms",
                        t.search * 1e3,
                        t.apply * 1e3
                    );
                }
            }
            eprintln!("[STATS] {stats:?}");
        }
    }

    Ok(())
}
