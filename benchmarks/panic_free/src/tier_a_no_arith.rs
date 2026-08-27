//! Tier A: panic-freedom that needs NO arithmetic reasoning.
//!
//! Every check here is discharged by matching the failure condition syntactically against
//! the path condition, or by a constant. If any of these fail, the gap is in goal
//! normalisation / pc propagation, not in arithmetic.
//!
//! With overflow checks on, `a / d` carries TWO obligations: `d != 0` and
//! `!(a == i32::MIN && d == -1)`. Every dividend here is therefore a literal, which makes
//! the second obligation constant-false and leaves the divide-by-zero check alone as the
//! thing under test. Variable dividends live in Tier B.

#![allow(dead_code)]

/// The guard IS the negated check: MIR emits `assert(!(d == 0))`, pc has `d != 0`.
pub fn div_guard_ne(d: i32) -> i32 {
    if d != 0 { 100 / d } else { 0 }
}

/// Same, spelled as an equality guard on the else arm.
pub fn div_guard_eq_else(d: i32) -> i32 {
    if d == 0 { 0 } else { 100 / d }
}

/// Remainder carries the same divide-by-zero check as division.
pub fn rem_guard_ne(d: i32) -> i32 {
    if d != 0 { 100 % d } else { 0 }
}

/// Divisor is a non-zero literal: the check is `7 == 0`, constant-false.
pub fn div_by_literal(a: i32) -> i32 {
    a / 7
}

/// Divisor flows through a local before use; still syntactically the guarded value.
pub fn div_guard_through_local(d: i32) -> i32 {
    if d != 0 {
        let k = d;
        100 / k
    } else {
        0
    }
}

/// Two divisions under one guard. No arithmetic on the results — combining them would
/// add an addition-overflow obligation and drag the case into Tier C.
pub fn div_twice_one_guard(d: i32) -> i32 {
    if d != 0 {
        let x = 100 / d;
        let _y = 200 / d;
        x
    } else {
        0
    }
}

/// Nested guards: the inner division is guarded two levels up.
pub fn div_guard_nested(d: i32, flag: bool) -> i32 {
    if d != 0 {
        if flag { 100 / d } else { 0 }
    } else {
        0
    }
}

/// An explicit `panic!` in a branch the guard makes unreachable. Encodes to a
/// `assert false` reachable only under a contradictory pc.
pub fn explicit_panic_unreachable(x: i32) -> i32 {
    if x == 0 {
        if x != 0 {
            panic!("unreachable");
        }
        0
    } else {
        x
    }
}

/// Exhaustive match: no unreachable-arm panic to discharge, but Prusti still emits the
/// discriminant well-formedness obligations.
pub enum Kind {
    A,
    B,
    C,
}

pub fn match_exhaustive(k: &Kind) -> i32 {
    match k {
        Kind::A => 1,
        Kind::B => 2,
        Kind::C => 3,
    }
}

/// Divisor is a match result that is non-zero on every arm — needs arm-wise reasoning but
/// no arithmetic: each arm's value is a literal.
pub fn div_by_match_literal(a: i32, k: &Kind) -> i32 {
    let d = match k {
        Kind::A => 1,
        Kind::B => 2,
        Kind::C => 4,
    };
    a / d
}
