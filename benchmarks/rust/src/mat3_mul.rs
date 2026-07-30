//! Benchmark input: **block length**.
//!
//! Unannotated Rust — Prusti emits the core obligations (framing, fold/unfold of
//! type predicates) without user specs. Unrolled 3x3 integer linear algebra, so
//! every function body is one long straight-line block with no branching: the
//! shape that stresses how much a single block accumulates before a proof
//! obligation is raised.
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 mat3_mul.rs

pub struct Mat3 {
    pub a00: i32,
    pub a01: i32,
    pub a02: i32,
    pub a10: i32,
    pub a11: i32,
    pub a12: i32,
    pub a20: i32,
    pub a21: i32,
    pub a22: i32,
}

pub struct Vec3 {
    pub x: i32,
    pub y: i32,
    pub z: i32,
}

pub fn mat3_zero() -> Mat3 {
    Mat3 {
        a00: 0,
        a01: 0,
        a02: 0,
        a10: 0,
        a11: 0,
        a12: 0,
        a20: 0,
        a21: 0,
        a22: 0,
    }
}

pub fn mat3_identity() -> Mat3 {
    Mat3 {
        a00: 1,
        a01: 0,
        a02: 0,
        a10: 0,
        a11: 1,
        a12: 0,
        a20: 0,
        a21: 0,
        a22: 1,
    }
}

pub fn mat3_transpose(m: &Mat3) -> Mat3 {
    Mat3 {
        a00: m.a00,
        a01: m.a10,
        a02: m.a20,
        a10: m.a01,
        a11: m.a11,
        a12: m.a21,
        a20: m.a02,
        a21: m.a12,
        a22: m.a22,
    }
}

pub fn mat3_transpose_in_place(m: &mut Mat3) {
    let t01 = m.a01;
    let t02 = m.a02;
    let t12 = m.a12;
    m.a01 = m.a10;
    m.a02 = m.a20;
    m.a12 = m.a21;
    m.a10 = t01;
    m.a20 = t02;
    m.a21 = t12;
}

pub fn mat3_trace(m: &Mat3) -> i32 {
    m.a00 + m.a11 + m.a22
}

pub fn mat3_add(p: &Mat3, q: &Mat3) -> Mat3 {
    Mat3 {
        a00: p.a00 + q.a00,
        a01: p.a01 + q.a01,
        a02: p.a02 + q.a02,
        a10: p.a10 + q.a10,
        a11: p.a11 + q.a11,
        a12: p.a12 + q.a12,
        a20: p.a20 + q.a20,
        a21: p.a21 + q.a21,
        a22: p.a22 + q.a22,
    }
}

pub fn mat3_scale(m: &mut Mat3, k: i32) {
    m.a00 = m.a00 * k;
    m.a01 = m.a01 * k;
    m.a02 = m.a02 * k;
    m.a10 = m.a10 * k;
    m.a11 = m.a11 * k;
    m.a12 = m.a12 * k;
    m.a20 = m.a20 * k;
    m.a21 = m.a21 * k;
    m.a22 = m.a22 * k;
}

pub fn mat3_mul(p: &Mat3, q: &Mat3) -> Mat3 {
    let c00 = p.a00 * q.a00 + p.a01 * q.a10 + p.a02 * q.a20;
    let c01 = p.a00 * q.a01 + p.a01 * q.a11 + p.a02 * q.a21;
    let c02 = p.a00 * q.a02 + p.a01 * q.a12 + p.a02 * q.a22;
    let c10 = p.a10 * q.a00 + p.a11 * q.a10 + p.a12 * q.a20;
    let c11 = p.a10 * q.a01 + p.a11 * q.a11 + p.a12 * q.a21;
    let c12 = p.a10 * q.a02 + p.a11 * q.a12 + p.a12 * q.a22;
    let c20 = p.a20 * q.a00 + p.a21 * q.a10 + p.a22 * q.a20;
    let c21 = p.a20 * q.a01 + p.a21 * q.a11 + p.a22 * q.a21;
    let c22 = p.a20 * q.a02 + p.a21 * q.a12 + p.a22 * q.a22;
    Mat3 {
        a00: c00,
        a01: c01,
        a02: c02,
        a10: c10,
        a11: c11,
        a12: c12,
        a20: c20,
        a21: c21,
        a22: c22,
    }
}

pub fn mat3_det(m: &Mat3) -> i32 {
    let m0 = m.a11 * m.a22 - m.a12 * m.a21;
    let m1 = m.a10 * m.a22 - m.a12 * m.a20;
    let m2 = m.a10 * m.a21 - m.a11 * m.a20;
    m.a00 * m0 - m.a01 * m1 + m.a02 * m2
}

pub fn mat3_apply(m: &Mat3, v: &Vec3) -> Vec3 {
    Vec3 {
        x: m.a00 * v.x + m.a01 * v.y + m.a02 * v.z,
        y: m.a10 * v.x + m.a11 * v.y + m.a12 * v.z,
        z: m.a20 * v.x + m.a21 * v.y + m.a22 * v.z,
    }
}

pub fn mat3_apply_in_place(m: &Mat3, v: &mut Vec3) {
    let nx = m.a00 * v.x + m.a01 * v.y + m.a02 * v.z;
    let ny = m.a10 * v.x + m.a11 * v.y + m.a12 * v.z;
    let nz = m.a20 * v.x + m.a21 * v.y + m.a22 * v.z;
    v.x = nx;
    v.y = ny;
    v.z = nz;
}

/// Longest straight-line block in the file: three products threaded through the
/// same accumulator matrix, no branch anywhere.
pub fn mat3_cube_trace(m: &Mat3) -> i32 {
    let sq = mat3_mul(m, m);
    let cb = mat3_mul(&sq, m);
    let t1 = mat3_trace(m);
    let t2 = mat3_trace(&sq);
    let t3 = mat3_trace(&cb);
    let d1 = mat3_det(m);
    let d2 = mat3_det(&sq);
    t1 * t1 * t1 - 3 * t1 * t2 + 2 * t3 + d1 - d2
}

/// A call on a reborrowed `&mut` parameter after a join whose arm also called on it —
/// the shape that needed the full-saturation miss retry (see README).
pub fn mat3_normalize_signs(m: &mut Mat3) {
    let d = mat3_det(m);
    if d < 0 {
        mat3_scale(m, -1);
    }
    mat3_transpose_in_place(m);
}
