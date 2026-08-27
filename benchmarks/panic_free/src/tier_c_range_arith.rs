//! Tier C: panic-freedom that needs REAL arithmetic — interval propagation, sum/product
//! bounds, or transitivity through a computed value.
//!
//! Everything here is provable by a human (and by Silicon, which hands it to Z3), and is
//! expected to be out of reach for a pure e-graph until the interval analysis or the Z3
//! tier lands. These are the cases that motivate `z3_integration_plan.md`.

#![allow(dead_code)]

/// Sum bound: `a, b < 10000` and both non-negative, so `a + b` cannot overflow i32.
pub fn add_bounded(a: i32, b: i32) -> i32 {
    if 0 <= a && a < 10000 && 0 <= b && b < 10000 {
        a + b
    } else {
        0
    }
}

/// Difference bound on the other side: `a >= b` keeps the subtraction non-negative, and
/// both bounded keeps it in range.
pub fn sub_bounded(a: i32, b: i32) -> i32 {
    if 0 <= b && b <= a && a < 10000 {
        a - b
    } else {
        0
    }
}

/// Product bound: two factors under 1000 give a product under 1_000_000.
pub fn mul_bounded(a: i32, b: i32) -> i32 {
    if 0 <= a && a < 1000 && 0 <= b && b < 1000 {
        a * b
    } else {
        0
    }
}

/// Transitivity through a computed value: `d` is positive because it is a sum of a
/// non-negative and a positive, and only then is it a legal divisor.
pub fn div_by_computed_positive(a: i32, n: i32) -> i32 {
    if 0 <= n && n < 1000 {
        let d = n + 1;
        a / d
    } else {
        0
    }
}

/// A scaled divisor: `2 * n` is non-zero because `n` is at least one, and in range
/// because `n` is bounded.
pub fn div_by_scaled(a: i32, n: i32) -> i32 {
    if 1 <= n && n < 1000 {
        let d = 2 * n;
        a / d
    } else {
        0
    }
}

/// The classic average: needs `(a + b)` in range before the halving, and `2 != 0`.
pub fn average(a: i32, b: i32) -> i32 {
    if 0 <= a && a < 10000 && 0 <= b && b < 10000 {
        (a + b) / 2
    } else {
        0
    }
}

/// Chained accumulation: three bounded addends, so every partial sum stays in range.
pub fn sum_three_bounded(a: i32, b: i32, c: i32) -> i32 {
    if 0 <= a && a < 1000 && 0 <= b && b < 1000 && 0 <= c && c < 1000 {
        let s1 = a + b;
        let s2 = s1 + c;
        s2
    } else {
        0
    }
}

/// Remainder bounds the divisor of a later division: `a % 10` is in `-9..=9`, and the
/// guard then excludes zero — but the range fact is what makes the `+ 10` safe.
pub fn rem_then_div(a: i32) -> i32 {
    let r = a % 10;
    let d = r + 10;
    if d != 0 { 100 / d } else { 0 }
}

/// Sign reasoning through a negation: `-a` is safe because `a` is bounded away from
/// `i32::MIN` by an interval, not by an explicit `!=`.
pub fn neg_bounded(a: i32) -> i32 {
    if -1000 < a && a < 1000 { -a } else { 0 }
}

/// Interval intersection across a branch join: both arms leave `d` positive, so the
/// division after the join is safe under a joined fact rather than one arm's pc.
pub fn div_after_join(a: i32, flag: bool) -> i32 {
    let d = if flag { 3 } else { 5 };
    a / d
}
