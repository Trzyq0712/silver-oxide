//! Tier D: array-bounds panics. Split out because Prusti's array/slice support is thin —
//! if this file fails to encode it drops on its own without taking the arithmetic tiers
//! with it.

#![allow(dead_code)]

/// Constant index inside a fixed-size array: the check is literal-vs-literal.
pub fn index_const(a: &[i32; 8]) -> i32 {
    a[3]
}

/// Guarded index: `i < 8` is exactly the bound Prusti checks.
pub fn index_guard_lt_len(a: &[i32; 8], i: usize) -> i32 {
    if i < 8 { a[i] } else { 0 }
}

/// Guarded against the wrong bound — must be REJECTED.
pub fn index_guard_too_loose(a: &[i32; 8], i: usize) -> i32 {
    if i < 16 { a[i] } else { 0 }
}

/// Unguarded index — must be REJECTED.
pub fn index_unguarded(a: &[i32; 8], i: usize) -> i32 {
    a[i]
}
