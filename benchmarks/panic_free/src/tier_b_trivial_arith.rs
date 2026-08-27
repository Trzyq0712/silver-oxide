//! Tier B: panic-freedom that needs ONE step of arithmetic reasoning.
//!
//! Each check follows from the path condition by a single order/equality fact about
//! integers — `0 < d ==> d != 0`, `0 < d ==> d != -1`, `d < -1 ==> d != 0`. Nothing here
//! needs interval propagation or a sum bound; that is Tier C.
//!
//! With overflow checks on, a division by a *variable* divisor also needs
//! `!(a == i32::MIN && d == -1)`. Cases whose guard does not exclude `d == -1` use a
//! literal dividend so that obligation stays constant-false and the order fact is the
//! only thing under test.

#![allow(dead_code)]

/// `0 < d ==> d != 0` and `0 < d ==> d != -1`, so a variable dividend is safe. This is
/// the shape Prusti emits for `physics_step::body_damp` and `body_apply_impulse`, and the
/// one that fails today.
pub fn div_guard_gt_zero(a: i32, d: i32) -> i32 {
    if 0 < d { a / d } else { 0 }
}

/// The mirrored spelling: `d > 0`.
pub fn div_guard_gt_zero_flipped(a: i32, d: i32) -> i32 {
    if d > 0 { a / d } else { 0 }
}

/// `1 <= d`: non-strict order, one step from the literal.
pub fn div_guard_ge_one(a: i32, d: i32) -> i32 {
    if d >= 1 { a / d } else { 0 }
}

/// `d < 0 ==> d != 0` — the negative side of the same fact. Literal dividend, because
/// `d < 0` admits `d == -1` and would otherwise also carry the MIN/-1 obligation.
pub fn div_guard_lt_zero(d: i32) -> i32 {
    if d < 0 { 100 / d } else { 0 }
}

/// `d < -1` excludes both zero and minus one, so a variable dividend is safe again.
pub fn div_guard_lt_minus_one(a: i32, d: i32) -> i32 {
    if d < -1 { a / d } else { 0 }
}

/// Both signs excluded separately; the union covers every non-zero divisor.
pub fn div_guard_either_sign(d: i32) -> i32 {
    if 0 < d {
        100 / d
    } else if d < 0 {
        100 / d
    } else {
        0
    }
}

/// `0 < d` established one block earlier, used after unrelated statements — same fact,
/// longer pc-to-use distance. Deliberately no arithmetic on `b`.
pub fn div_guard_gt_zero_delayed(a: i32, b: i32, d: i32) -> i32 {
    if 0 < d {
        let t = b;
        let _u = t;
        a / d
    } else {
        0
    }
}

/// The MIN/-1 trap excluded on the dividend side instead: `d != 0` handles zero, and
/// `a != i32::MIN` handles the overflow. Two equality facts, no order reasoning.
pub fn div_overflow_guard_dividend(a: i32, d: i32) -> i32 {
    if d != 0 && a != -2147483648 { a / d } else { 0 }
}

/// Remainder with a variable dividend: `i32::MIN % -1` traps just as the division does.
pub fn rem_guard_gt_zero(a: i32, d: i32) -> i32 {
    if 0 < d { a % d } else { 0 }
}

/// Negation traps only at `i32::MIN`; the guard names it exactly.
pub fn neg_guard_not_min(a: i32) -> i32 {
    if a != -2147483648 { -a } else { 0 }
}
