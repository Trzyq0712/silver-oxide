//! How `unreachable!()` encodes, and whether reaching it is an obligation.
//!
//! Three distinct things get called "unreachable" and they do not encode alike:
//! the `unreachable!()` macro (a panic), a MIR `Unreachable` terminator (emitted for
//! genuinely dead control flow, e.g. after an exhaustive discriminant switch), and
//! `unreachable_unchecked` (UB, not encodable at all — deliberately absent here).

#![allow(dead_code)]

pub enum Kind {
    A,
    B,
    C,
}

/// `unreachable!()` in an arm the caller cannot reach *by construction of the enum*: the
/// match is exhaustive over three variants and the fourth arm does not exist. Nothing to
/// discharge — this is the baseline.
pub fn unreachable_exhaustive(k: &Kind) -> i32 {
    match k {
        Kind::A => 1,
        Kind::B => 2,
        Kind::C => 3,
    }
}

/// `unreachable!()` in an arm ruled out by an equality guard. Discharging this needs the
/// pc, not the enum: `k` is `A`, so the `B`/`C` arms are dead.
pub fn unreachable_guarded_eq(k: &Kind, flag: bool) -> i32 {
    if flag {
        match k {
            Kind::A => 1,
            Kind::B => 2,
            Kind::C => 3,
        }
    } else {
        1
    }
}

/// `unreachable!()` reachable only under a contradictory integer pc — the equality case,
/// which Tier A shows we can discharge.
pub fn unreachable_contradiction_eq(x: i32) -> i32 {
    if x == 0 {
        if x != 0 {
            unreachable!();
        }
        0
    } else {
        x
    }
}

/// The same, but the contradiction is an order fact: `0 < x` and `x < 0`. This is the
/// Tier B shape, so it should fail for the same reason `0 < d ==> d != 0` fails.
pub fn unreachable_contradiction_order(x: i32) -> i32 {
    if 0 < x {
        if x < 0 {
            unreachable!();
        }
        0
    } else {
        x
    }
}

/// A genuinely reachable `unreachable!()`. If explicit panics are unchecked (they are, in
/// this encoding), this verifies — which is exactly what the case is here to record.
pub fn unreachable_actually_reachable(x: i32) -> i32 {
    if x == 0 {
        unreachable!();
    }
    x
}
