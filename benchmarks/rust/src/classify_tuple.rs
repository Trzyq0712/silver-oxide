//! Benchmark input: **many sequential blocks, shallow nesting**.
//!
//! Unannotated Rust. A fixed-arity "buffer" (eight fields, no loops) classified
//! element by element through a match cascade, then summarised. Produces members with
//! a high block count where every cube is short — the opposite extreme from
//! `aabb_collide.rs`, and the case where a dominator chain barely exists.
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 classify_tuple.rs

#[derive(Clone, Copy)]
pub enum Kind {
    Digit,
    Letter,
    Space,
    Symbol,
}

pub struct Buf8 {
    pub c0: i32,
    pub c1: i32,
    pub c2: i32,
    pub c3: i32,
    pub c4: i32,
    pub c5: i32,
    pub c6: i32,
    pub c7: i32,
}

pub struct Counts {
    pub digits: i32,
    pub letters: i32,
    pub spaces: i32,
    pub symbols: i32,
}

pub fn counts_zero() -> Counts {
    Counts {
        digits: 0,
        letters: 0,
        spaces: 0,
        symbols: 0,
    }
}

pub fn classify(c: i32) -> Kind {
    if c == 32 {
        Kind::Space
    } else {
        if 48 <= c {
            if c <= 57 {
                Kind::Digit
            } else {
                if 97 <= c {
                    if c <= 122 {
                        Kind::Letter
                    } else {
                        Kind::Symbol
                    }
                } else {
                    if 65 <= c {
                        if c <= 90 {
                            Kind::Letter
                        } else {
                            Kind::Symbol
                        }
                    } else {
                        Kind::Symbol
                    }
                }
            }
        } else {
            Kind::Symbol
        }
    }
}

pub fn kind_code(k: Kind) -> i32 {
    match k {
        Kind::Digit => 0,
        Kind::Letter => 1,
        Kind::Space => 2,
        Kind::Symbol => 3,
    }
}

pub fn bump(cs: &mut Counts, k: Kind) {
    match k {
        Kind::Digit => {
            cs.digits = cs.digits + 1;
        }
        Kind::Letter => {
            cs.letters = cs.letters + 1;
        }
        Kind::Space => {
            cs.spaces = cs.spaces + 1;
        }
        Kind::Symbol => {
            cs.symbols = cs.symbols + 1;
        }
    }
}

/// Eight classify+bump pairs unrolled: 8 nested-branch classifications and 8 four-arm
/// matches in one member.
pub fn count_kinds(b: &Buf8) -> Counts {
    let mut cs = counts_zero();
    bump(&mut cs, classify(b.c0));
    bump(&mut cs, classify(b.c1));
    bump(&mut cs, classify(b.c2));
    bump(&mut cs, classify(b.c3));
    bump(&mut cs, classify(b.c4));
    bump(&mut cs, classify(b.c5));
    bump(&mut cs, classify(b.c6));
    bump(&mut cs, classify(b.c7));
    cs
}

pub fn digit_value(c: i32) -> i32 {
    if 48 <= c {
        if c <= 57 {
            c - 48
        } else {
            -1
        }
    } else {
        -1
    }
}

/// Accumulates a number from the leading digits, unrolled: each step's block is
/// guarded by "the previous step was still a digit".
pub fn parse_prefix(b: &Buf8) -> i32 {
    let mut acc = 0;
    let mut live = true;
    let d0 = digit_value(b.c0);
    if live {
        if d0 < 0 {
            live = false;
        } else {
            acc = acc * 10 + d0;
        }
    }
    let d1 = digit_value(b.c1);
    if live {
        if d1 < 0 {
            live = false;
        } else {
            acc = acc * 10 + d1;
        }
    }
    let d2 = digit_value(b.c2);
    if live {
        if d2 < 0 {
            live = false;
        } else {
            acc = acc * 10 + d2;
        }
    }
    let d3 = digit_value(b.c3);
    if live {
        if d3 < 0 {
            live = false;
        } else {
            acc = acc * 10 + d3;
        }
    }
    let d4 = digit_value(b.c4);
    if live {
        if d4 < 0 {
            live = false;
        } else {
            acc = acc * 10 + d4;
        }
    }
    acc
}

pub fn upcase(c: i32) -> i32 {
    if 97 <= c {
        if c <= 122 {
            c - 32
        } else {
            c
        }
    } else {
        c
    }
}

pub fn buf_upcase(b: &mut Buf8) {
    b.c0 = upcase(b.c0);
    b.c1 = upcase(b.c1);
    b.c2 = upcase(b.c2);
    b.c3 = upcase(b.c3);
    b.c4 = upcase(b.c4);
    b.c5 = upcase(b.c5);
    b.c6 = upcase(b.c6);
    b.c7 = upcase(b.c7);
}

pub fn buf_checksum(b: &Buf8) -> i32 {
    let k0 = kind_code(classify(b.c0));
    let k1 = kind_code(classify(b.c1));
    let k2 = kind_code(classify(b.c2));
    let k3 = kind_code(classify(b.c3));
    let k4 = kind_code(classify(b.c4));
    let k5 = kind_code(classify(b.c5));
    let k6 = kind_code(classify(b.c6));
    let k7 = kind_code(classify(b.c7));
    k0 + k1 * 2 + k2 * 3 + k3 * 4 + k4 * 5 + k5 * 6 + k6 * 7 + k7 * 8
}

pub fn counts_dominant(cs: &Counts) -> i32 {
    let mut best = 0;
    let mut n = cs.digits;
    if n < cs.letters {
        best = 1;
        n = cs.letters;
    }
    if n < cs.spaces {
        best = 2;
        n = cs.spaces;
    }
    if n < cs.symbols {
        best = 3;
    }
    best
}

pub fn buf_report(b: &mut Buf8) -> i32 {
    buf_upcase(b);
    let cs = count_kinds(b);
    let dom = counts_dominant(&cs);
    let sum = buf_checksum(b);
    let pre = parse_prefix(b);
    if pre < 0 {
        sum + dom
    } else {
        sum + dom + pre
    }
}
