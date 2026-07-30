//! Benchmark input: **block length × call density**.
//!
//! Unannotated Rust. Integer vector algebra where every operation is built from
//! calls to the smaller ones, so a single block accumulates many call obligations
//! (each call = a fold/unfold plus a snapshot round-trip) with almost no branching.
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 vec3_math.rs

pub struct V3 {
    pub x: i32,
    pub y: i32,
    pub z: i32,
}

pub struct Basis {
    pub u: V3,
    pub v: V3,
    pub w: V3,
}

pub fn v3(x: i32, y: i32, z: i32) -> V3 {
    V3 { x, y, z }
}

pub fn v3_add(a: &V3, b: &V3) -> V3 {
    V3 {
        x: a.x + b.x,
        y: a.y + b.y,
        z: a.z + b.z,
    }
}

pub fn v3_sub(a: &V3, b: &V3) -> V3 {
    V3 {
        x: a.x - b.x,
        y: a.y - b.y,
        z: a.z - b.z,
    }
}

pub fn v3_scale(a: &V3, k: i32) -> V3 {
    V3 {
        x: a.x * k,
        y: a.y * k,
        z: a.z * k,
    }
}

pub fn v3_neg(a: &V3) -> V3 {
    v3_scale(a, -1)
}

pub fn v3_dot(a: &V3, b: &V3) -> i32 {
    a.x * b.x + a.y * b.y + a.z * b.z
}

pub fn v3_cross(a: &V3, b: &V3) -> V3 {
    V3 {
        x: a.y * b.z - a.z * b.y,
        y: a.z * b.x - a.x * b.z,
        z: a.x * b.y - a.y * b.x,
    }
}

pub fn v3_len2(a: &V3) -> i32 {
    v3_dot(a, a)
}

pub fn v3_dist2(a: &V3, b: &V3) -> i32 {
    let d = v3_sub(a, b);
    v3_len2(&d)
}

pub fn v3_add_in_place(a: &mut V3, b: &V3) {
    a.x = a.x + b.x;
    a.y = a.y + b.y;
    a.z = a.z + b.z;
}

pub fn v3_scale_in_place(a: &mut V3, k: i32) {
    a.x = a.x * k;
    a.y = a.y * k;
    a.z = a.z * k;
}

/// Eight calls in one straight-line block.
pub fn v3_triple_product(a: &V3, b: &V3, c: &V3) -> i32 {
    let ab = v3_cross(a, b);
    let bc = v3_cross(b, c);
    let ca = v3_cross(c, a);
    let s1 = v3_dot(&ab, c);
    let s2 = v3_dot(&bc, a);
    let s3 = v3_dot(&ca, b);
    let l1 = v3_len2(&ab);
    let l2 = v3_len2(&bc);
    s1 + s2 + s3 + l1 - l2
}

/// Longer still: a Gram-matrix-like accumulation, nine dot products, no branch.
pub fn basis_gram_trace(b: &Basis) -> i32 {
    let uu = v3_dot(&b.u, &b.u);
    let uv = v3_dot(&b.u, &b.v);
    let uw = v3_dot(&b.u, &b.w);
    let vu = v3_dot(&b.v, &b.u);
    let vv = v3_dot(&b.v, &b.v);
    let vw = v3_dot(&b.v, &b.w);
    let wu = v3_dot(&b.w, &b.u);
    let wv = v3_dot(&b.w, &b.v);
    let ww = v3_dot(&b.w, &b.w);
    uu + vv + ww + (uv - vu) + (uw - wu) + (vw - wv)
}

pub fn basis_det(b: &Basis) -> i32 {
    let c = v3_cross(&b.v, &b.w);
    v3_dot(&b.u, &c)
}

pub fn basis_is_degenerate(b: &Basis) -> bool {
    basis_det(b) == 0
}

pub fn basis_scale(b: &mut Basis, k: i32) {
    v3_scale_in_place(&mut b.u, k);
    v3_scale_in_place(&mut b.v, k);
    v3_scale_in_place(&mut b.w, k);
}

pub fn basis_shift(b: &mut Basis, d: &V3) {
    v3_add_in_place(&mut b.u, d);
    v3_add_in_place(&mut b.v, d);
    v3_add_in_place(&mut b.w, d);
}

/// One branch over a long straight-line body, so the two arms both carry a big
/// accumulated block behind them.
pub fn basis_orient(b: &Basis) -> V3 {
    let d = basis_det(b);
    if d < 0 {
        let n = v3_cross(&b.w, &b.v);
        let s = v3_scale(&n, 2);
        v3_add(&s, &b.u)
    } else {
        let n = v3_cross(&b.v, &b.w);
        let s = v3_scale(&n, 2);
        v3_add(&s, &b.u)
    }
}

pub fn v3_reflect(a: &V3, normal: &V3) -> V3 {
    let d = v3_dot(a, normal);
    let s = v3_scale(normal, 2 * d);
    v3_sub(a, &s)
}

pub fn v3_project_scaled(a: &V3, onto: &V3) -> V3 {
    let num = v3_dot(a, onto);
    let den = v3_len2(onto);
    if den == 0 {
        v3(0, 0, 0)
    } else {
        v3_scale(onto, num / den)
    }
}
