//! Verification-cost regression gate. For each `benchmarks/*.vpr` (which must
//! verify clean), capture the verifier's *deterministic* cost metrics and
//! compare them, exact-match, against a committed baseline under
//! `benchmarks/baseline/<name>.txt`.
//!
//! egg is deterministic for a fixed rule set + input, so any change in work done
//! moves a metric and fails this test with a `before → after` diff — silent
//! slowdowns cannot slip in. Refresh baselines deliberately after a justified
//! change:
//!
//! ```text
//! UPDATE_PERF_BASELINE=1 cargo test --test perf_regression
//! ```
//!
//! and review the resulting diff. See `plans/verification-perf-regression.md`.

use std::path::{Path, PathBuf};

use silver_oxide::pipeline;

fn benchmarks_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("benchmarks")
}

fn collect_benchmarks() -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(benchmarks_dir())
        .expect("benchmarks/ dir exists")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "vpr"))
        .collect();
    v.sort();
    v
}

/// Render a `before → after` line diff so a regression is readable.
fn diff(baseline: &str, current: &str) -> String {
    let base: std::collections::BTreeMap<&str, &str> =
        baseline.lines().filter_map(|l| l.split_once('=')).collect();
    let cur: std::collections::BTreeMap<&str, &str> =
        current.lines().filter_map(|l| l.split_once('=')).collect();
    let mut keys: Vec<&str> = base.keys().chain(cur.keys()).copied().collect();
    keys.sort();
    keys.dedup();
    let mut out = String::new();
    for k in keys {
        let (b, c) = (base.get(k), cur.get(k));
        if b != c {
            out.push_str(&format!(
                "  {k}: {} → {}\n",
                b.copied().unwrap_or("(absent)"),
                c.copied().unwrap_or("(absent)")
            ));
        }
    }
    out
}

#[test]
fn verification_cost_matches_baseline() {
    let update = std::env::var_os("UPDATE_PERF_BASELINE").is_some();
    let baseline_dir = benchmarks_dir().join("baseline");
    let benches = collect_benchmarks();
    assert!(!benches.is_empty(), "no benchmarks found");

    let mut failures = Vec::new();
    for bench in benches {
        let name = bench.file_stem().unwrap().to_str().unwrap().to_string();
        let (results, _timings, stats) =
            pipeline::run_file_timed(&bench).unwrap_or_else(|e| panic!("{name}: pipeline {e}"));
        // A benchmark must verify clean — a failing program has no stable cost.
        for (unit, outcome) in &results {
            assert!(
                outcome.is_ok(),
                "{name}: unit `{unit}` failed to verify: {outcome:?} \
                 (benchmarks must verify OK)"
            );
        }

        let current = stats.snapshot_string();
        let baseline_path = baseline_dir.join(format!("{name}.txt"));

        if update {
            std::fs::write(&baseline_path, &current).expect("write baseline");
            continue;
        }

        let baseline = std::fs::read_to_string(&baseline_path).unwrap_or_else(|_| {
            panic!(
                "{name}: missing baseline {}; run `UPDATE_PERF_BASELINE=1 cargo test \
                 --test perf_regression` to create it",
                baseline_path.display()
            )
        });
        if baseline != current {
            failures.push(format!(
                "{name}: verification cost changed\n{}",
                diff(&baseline, &current)
            ));
        }
    }

    if update {
        eprintln!("[perf] baselines updated; review the diff before committing");
        return;
    }
    assert!(
        failures.is_empty(),
        "verification cost regressed (rerun with UPDATE_PERF_BASELINE=1 if intended):\n\n{}",
        failures.join("\n")
    );
}
