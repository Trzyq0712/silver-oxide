//! Cost metrics for one `verify::verify` run, used by the performance
//! regression tests. The *deterministic* counters (egg is deterministic for a
//! fixed rule set + input) are gated as exact-match snapshots; the timing
//! fields are a non-gating trend (see `plans/verification-perf-regression.md`).

use std::collections::BTreeMap;

/// Wall-clock saturation time, broken into egg's phases. Non-deterministic —
/// reported for trends, never compared in the gating snapshot.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct Timing {
    /// e-matching: finding rule left-hand-side matches.
    pub search: f64,
    /// applying the matched rewrites.
    pub apply: f64,
    /// congruence-closure rebuild after unions.
    pub rebuild: f64,
}

impl Timing {
    pub fn total(&self) -> f64 {
        self.search + self.apply + self.rebuild
    }
}

/// Verifier work performed over a run. The non-`timing` fields are deterministic
/// and form the gated cost snapshot.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VerifyStats {
    /// `saturate()` calls (full rule set).
    pub saturations: u64,
    /// `reduce()` calls (terminating reductions only).
    pub reduces: u64,
    /// total egg `Runner` iterations across all saturations/reductions/probes.
    pub sat_iterations: u64,
    /// peak e-graph size observed in any iteration.
    pub egraph_nodes_peak: usize,
    pub egraph_classes_peak: usize,
    /// total rule applications, and a per-rule breakdown.
    pub rule_applications: u64,
    pub per_rule: BTreeMap<String, u64>,
    /// `prove_under_pc` calls, and how many reached the expensive Tier-3
    /// clone+saturate path (the clearest deterioration signal).
    pub prove_calls: u64,
    pub prove_tier3: u64,
    /// Non-deterministic timing (excluded from `Eq` / the gated snapshot).
    pub timing: TimingTrend,
    /// Per-rule search/apply wall clock (excluded from `Eq` / the snapshot).
    pub rule_timing: RuleTimingTrend,
}

/// `Timing` wrapper whose `PartialEq`/`Eq` ignore the floats, so `VerifyStats`
/// can derive `Eq` and be compared by its deterministic fields alone.
#[derive(Debug, Clone, Copy, Default)]
pub struct TimingTrend(pub Timing);

impl PartialEq for TimingTrend {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for TimingTrend {}

/// Wall-clock seconds one rule spent in its searcher/applier over the whole
/// run. Non-deterministic — a trend, never gated.
#[derive(Debug, Clone, Copy, Default)]
pub struct RuleTime {
    pub search: f64,
    pub apply: f64,
}

/// Per-rule timing map wrapper, `Eq`-transparent like [`TimingTrend`] so the
/// gated snapshot stays purely deterministic. `Debug` is a count summary — the
/// full map is rendered by `verify --breakdown`.
#[derive(Clone, Default)]
pub struct RuleTimingTrend(pub BTreeMap<String, RuleTime>);

impl std::fmt::Debug for RuleTimingTrend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RuleTimingTrend({} rules)", self.0.len())
    }
}

impl PartialEq for RuleTimingTrend {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for RuleTimingTrend {}

impl VerifyStats {
    /// A stable, human-readable rendering of the **deterministic** fields only
    /// (timing excluded), one `key=value` per line, sorted. This is the gated
    /// cost snapshot compared against a committed baseline.
    pub fn snapshot_string(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("saturations={}\n", self.saturations));
        s.push_str(&format!("reduces={}\n", self.reduces));
        s.push_str(&format!("sat_iterations={}\n", self.sat_iterations));
        s.push_str(&format!("egraph_nodes_peak={}\n", self.egraph_nodes_peak));
        s.push_str(&format!(
            "egraph_classes_peak={}\n",
            self.egraph_classes_peak
        ));
        s.push_str(&format!("rule_applications={}\n", self.rule_applications));
        s.push_str(&format!("prove_calls={}\n", self.prove_calls));
        s.push_str(&format!("prove_tier3={}\n", self.prove_tier3));
        // `per_rule` is a BTreeMap → already sorted, hence deterministic.
        for (rule, n) in &self.per_rule {
            s.push_str(&format!("rule.{rule}={n}\n"));
        }
        s
    }

    /// Fold one finished `Runner`'s iterations into the stats.
    pub(crate) fn record_run(&mut self, iterations: &[egg::Iteration<()>]) {
        for it in iterations {
            self.sat_iterations += 1;
            self.egraph_nodes_peak = self.egraph_nodes_peak.max(it.egraph_nodes);
            self.egraph_classes_peak = self.egraph_classes_peak.max(it.egraph_classes);
            for (rule, n) in &it.applied {
                self.rule_applications += *n as u64;
                *self.per_rule.entry(rule.to_string()).or_default() += *n as u64;
            }
            self.timing.0.search += it.search_time;
            self.timing.0.apply += it.apply_time;
            self.timing.0.rebuild += it.rebuild_time;
        }
    }
}
