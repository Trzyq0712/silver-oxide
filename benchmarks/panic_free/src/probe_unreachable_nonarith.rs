//! Unreachability that needs NO arithmetic: every contradiction here is between booleans,
//! enum discriminants, equalities, or values related by framing/congruence. No `<`, no
//! `+`, no interval — the only integer relation used is `==`/`!=`.
//!
//! `probe_unreachable.rs` established that `unreachable!()` is a real obligation. This
//! file asks the follow-up: does anything fail for a reason OTHER than the missing
//! `0 < d ==> d != 0` order fact? Every member must verify; a failure here is a
//! pc-propagation, join, congruence, or framing gap.

#![allow(dead_code)]

pub enum Kind {
    A,
    B,
    C,
}

pub struct Pair {
    pub x: i32,
    pub y: i32,
}

// ---------------------------------------------------------------- boolean contradictions

/// The simplest possible: `b` and `!b`.
pub fn bool_direct(b: bool) -> i32 {
    if b {
        if !b {
            unreachable!();
        }
        1
    } else {
        0
    }
}

/// Through a copy: the inner test is on a different local holding the same value.
pub fn bool_through_copy(b: bool) -> i32 {
    let c = b;
    if b {
        if !c {
            unreachable!();
        }
        1
    } else {
        0
    }
}

/// Through a negation stored in a local.
pub fn bool_through_negation(b: bool) -> i32 {
    let n = !b;
    if b {
        if n {
            unreachable!();
        }
        1
    } else {
        0
    }
}

/// Contradiction only visible after a join: both arms leave `flag` true.
pub fn bool_after_join(b: bool) -> i32 {
    let flag = if b { true } else { true };
    if !flag {
        unreachable!();
    }
    1
}

/// Three levels of nesting before the contradiction closes.
pub fn bool_nested_deep(b: bool, c: bool, d: bool) -> i32 {
    if b {
        if c {
            if d {
                if !b {
                    unreachable!();
                }
                1
            } else {
                2
            }
        } else {
            3
        }
    } else {
        0
    }
}

// ------------------------------------------------------------- equality contradictions

/// Two variables, equality against disequality. Integers, but no arithmetic.
pub fn eq_two_vars(x: i32, y: i32) -> i32 {
    if x == y {
        if x != y {
            unreachable!();
        }
        1
    } else {
        0
    }
}

/// Transitivity of equality: `x == y` and `y == z` make `x != z` impossible.
pub fn eq_transitive(x: i32, y: i32, z: i32) -> i32 {
    if x == y {
        if y == z {
            if x != z {
                unreachable!();
            }
            1
        } else {
            2
        }
    } else {
        0
    }
}

/// Equality against a literal, then a different literal.
pub fn eq_two_literals(x: i32) -> i32 {
    if x == 5 {
        if x == 7 {
            unreachable!();
        }
        1
    } else {
        0
    }
}

// --------------------------------------------------------------- enum discriminants

/// Inside the `A` arm, a second match cannot see `B` or `C`.
pub fn enum_rematch(k: &Kind) -> i32 {
    match k {
        Kind::A => match k {
            Kind::A => 1,
            Kind::B => unreachable!(),
            Kind::C => unreachable!(),
        },
        Kind::B => 2,
        Kind::C => 3,
    }
}

/// A discriminant equality carried in a boolean.
pub fn enum_via_bool(k: &Kind) -> i32 {
    let is_a = matches!(k, Kind::A);
    if is_a {
        match k {
            Kind::A => 1,
            Kind::B => unreachable!(),
            Kind::C => unreachable!(),
        }
    } else {
        0
    }
}

// ------------------------------------------------------- congruence, framing, calls

fn pick(p: &Pair) -> i32 {
    p.x
}

/// Determinism/congruence: two calls with the same argument give the same result.
pub fn call_congruence(p: &Pair) -> i32 {
    let a = pick(p);
    let b = pick(p);
    if a != b {
        unreachable!();
    }
    a
}

/// Framing across a write to an unrelated field: `p.x` is unchanged by writing `p.y`.
pub fn frame_other_field(p: &mut Pair, v: i32) -> i32 {
    let before = p.x;
    p.y = v;
    let after = p.x;
    if before != after {
        unreachable!();
    }
    after
}

/// Read-back of a value just written through a `&mut`.
pub fn write_then_read(p: &mut Pair, v: i32) -> i32 {
    p.x = v;
    let got = p.x;
    if got != v {
        unreachable!();
    }
    got
}

/// A guard established before a call must survive the call, which touches a different
/// field of the same struct.
fn set_y(p: &mut Pair, v: i32) {
    p.y = v;
}

pub fn guard_survives_call(p: &mut Pair, v: i32) -> i32 {
    let before = p.x;
    set_y(p, v);
    if p.x != before {
        unreachable!();
    }
    p.x
}
