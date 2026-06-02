//! Measure the cost of spawning a Z3 process that does (almost) nothing, as
//! invoked from a Rust binary — the per-query floor a solver-based backend pays.
//!
//! Usage: `z3probe [z3-path] [iterations]` (defaults: `z3`, 30).
//! Spawns `z3 -smt2 -in`, sends a trivial `(check-sat)` (empty context → `sat`,
//! proving Z3 actually ran), then `(exit)`, timing each round-trip.

use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

fn one_round(z3: &str) -> (Duration, String) {
    let start = Instant::now();
    let mut child = Command::new(z3)
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("failed to spawn z3 — check the path");

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    // Trivial query: nothing asserted, so Z3 answers `sat` immediately. Then quit.
    writeln!(stdin, "(check-sat)\n(exit)").unwrap();
    drop(stdin);

    // Read Z3's reply (proves the binary was actually executed and responded).
    let mut reply = String::new();
    BufReader::new(stdout).read_line(&mut reply).ok();
    child.wait().unwrap();

    (start.elapsed(), reply.trim().to_string())
}

fn main() {
    let z3 = std::env::args().nth(1).unwrap_or_else(|| "z3".to_string());
    let n: usize = std::env::args()
        .nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(30);

    // First call confirms Z3 is reachable and reports its reply + version.
    let (first, reply) = one_round(&z3);
    let version = Command::new(&z3)
        .arg("--version")
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_default();
    println!("z3 path : {z3}");
    println!("z3 says : {version}");
    println!("reply   : {reply:?}  (proves Z3 ran)");
    println!("first   : {first:.3?}");

    let mut times: Vec<Duration> = Vec::with_capacity(n);
    for _ in 0..n {
        times.push(one_round(&z3).0);
    }
    times.sort();
    let sum: Duration = times.iter().sum();
    let avg = sum / n as u32;
    let min = times[0];
    let median = times[n / 2];
    let max = times[n - 1];
    println!("\nspawn+check-sat+exit over {n} runs:");
    println!("  min {min:.3?}  median {median:.3?}  avg {avg:.3?}  max {max:.3?}");
}
