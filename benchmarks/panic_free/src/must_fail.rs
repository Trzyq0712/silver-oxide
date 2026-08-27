//! Soundness side: every member here CAN panic, so every member must be REJECTED.
//!
//! A pass in this file is an unsoundness, not a win. Kept separate from the tiers so a
//! sweep can assert the two directions independently: tiers = completeness, this =
//! soundness.

#![allow(dead_code)]
#![allow(unconditional_panic)]
#![allow(arithmetic_overflow)]

/// Unguarded division: `d` may be zero.
pub fn div_unguarded(a: i32, d: i32) -> i32 {
    a / d
}

/// Guard on the wrong variable.
pub fn div_guard_wrong_var(a: i32, d: i32) -> i32 {
    if a != 0 { a / d } else { 0 }
}

/// Guard excludes only one of the two zero-reaching paths.
pub fn div_guard_incomplete(a: i32, d: i32) -> i32 {
    if 0 <= d { a / d } else { 0 }
}

/// The division-overflow trap: `i32::MIN / -1`. `d != 0` is not enough.
pub fn div_overflow_unguarded(a: i32, d: i32) -> i32 {
    if d != 0 { a / d } else { 0 }
}

/// Unguarded remainder.
pub fn rem_unguarded(a: i32, d: i32) -> i32 {
    a % d
}

/// Unbounded addition overflows.
pub fn add_unguarded(a: i32, b: i32) -> i32 {
    a + b
}

/// One-sided bound is not enough for a sum.
pub fn add_half_bounded(a: i32, b: i32) -> i32 {
    if a < 10000 { a + b } else { 0 }
}

/// Unbounded subtraction underflows.
pub fn sub_unguarded(a: i32, b: i32) -> i32 {
    a - b
}

/// Unbounded product overflows.
pub fn mul_unguarded(a: i32, b: i32) -> i32 {
    a * b
}

/// Negation traps at `i32::MIN`, which this guard does not exclude.
pub fn neg_unguarded(a: i32) -> i32 {
    if a < 0 { -a } else { 0 }
}

/// A reachable explicit panic.
pub fn explicit_panic_reachable(x: i32) -> i32 {
    if x == 0 {
        panic!("zero");
    }
    x
}

/// Guard is on a stale copy: `d` is reassigned to a possibly-zero value after the check.
pub fn div_guard_stale(a: i32, d: i32, e: i32) -> i32 {
    if d != 0 {
        let k = e;
        a / k
    } else {
        0
    }
}
