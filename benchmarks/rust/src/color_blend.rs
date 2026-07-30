//! Benchmark input: **branch cascades**.
//!
//! Unannotated Rust. RGBA blending with clamping written as explicit if/else chains
//! rather than library calls: many *sequential* two-way branches in one function, so
//! a member accumulates a long series of small joins — the case where each block's
//! cube is short but the block count per member is high.
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 color_blend.rs

pub struct Rgba {
    pub r: i32,
    pub g: i32,
    pub b: i32,
    pub a: i32,
}

pub fn rgba(r: i32, g: i32, b: i32, a: i32) -> Rgba {
    Rgba { r, g, b, a }
}

pub fn clamp255(v: i32) -> i32 {
    if v < 0 {
        0
    } else {
        if 255 < v {
            255
        } else {
            v
        }
    }
}

pub fn min2(a: i32, b: i32) -> i32 {
    if a < b {
        a
    } else {
        b
    }
}

pub fn max2(a: i32, b: i32) -> i32 {
    if a < b {
        b
    } else {
        a
    }
}

/// Four sequential clamps: four joins in one block chain.
pub fn rgba_clamp(c: &mut Rgba) {
    c.r = clamp255(c.r);
    c.g = clamp255(c.g);
    c.b = clamp255(c.b);
    c.a = clamp255(c.a);
}

/// The clamps inlined, so the branching is in *this* member's CFG rather than behind
/// a call — eight sequential two-way branches.
pub fn rgba_clamp_inline(c: &mut Rgba) {
    if c.r < 0 {
        c.r = 0;
    }
    if 255 < c.r {
        c.r = 255;
    }
    if c.g < 0 {
        c.g = 0;
    }
    if 255 < c.g {
        c.g = 255;
    }
    if c.b < 0 {
        c.b = 0;
    }
    if 255 < c.b {
        c.b = 255;
    }
    if c.a < 0 {
        c.a = 0;
    }
    if 255 < c.a {
        c.a = 255;
    }
}

pub fn rgba_add_saturating(p: &Rgba, q: &Rgba) -> Rgba {
    Rgba {
        r: clamp255(p.r + q.r),
        g: clamp255(p.g + q.g),
        b: clamp255(p.b + q.b),
        a: clamp255(p.a + q.a),
    }
}

pub fn rgba_lerp(p: &Rgba, q: &Rgba, t: i32) -> Rgba {
    let s = clamp255(t);
    let inv = 255 - s;
    Rgba {
        r: clamp255((p.r * inv + q.r * s) / 255),
        g: clamp255((p.g * inv + q.g * s) / 255),
        b: clamp255((p.b * inv + q.b * s) / 255),
        a: clamp255((p.a * inv + q.a * s) / 255),
    }
}

pub fn rgba_luma(c: &Rgba) -> i32 {
    (c.r * 54 + c.g * 183 + c.b * 19) / 256
}

pub fn rgba_grey(c: &Rgba) -> Rgba {
    let y = clamp255(rgba_luma(c));
    Rgba {
        r: y,
        g: y,
        b: y,
        a: c.a,
    }
}

/// Channel-wise mode selection: a branch per channel *and* a branch on the mode, so
/// the arms multiply out.
pub fn rgba_blend_mode(p: &Rgba, q: &Rgba, mode: i32) -> Rgba {
    let mut out = rgba(0, 0, 0, 255);
    if mode == 0 {
        out.r = clamp255(p.r + q.r);
        out.g = clamp255(p.g + q.g);
        out.b = clamp255(p.b + q.b);
    } else {
        if mode == 1 {
            out.r = min2(p.r, q.r);
            out.g = min2(p.g, q.g);
            out.b = min2(p.b, q.b);
        } else {
            if mode == 2 {
                out.r = max2(p.r, q.r);
                out.g = max2(p.g, q.g);
                out.b = max2(p.b, q.b);
            } else {
                out.r = clamp255((p.r * q.r) / 255);
                out.g = clamp255((p.g * q.g) / 255);
                out.b = clamp255((p.b * q.b) / 255);
            }
        }
    }
    if p.a < q.a {
        out.a = q.a;
    } else {
        out.a = p.a;
    }
    out
}

pub fn rgba_is_opaque(c: &Rgba) -> bool {
    c.a == 255
}

pub fn rgba_premultiply(c: &mut Rgba) {
    if c.a == 0 {
        c.r = 0;
        c.g = 0;
        c.b = 0;
    } else {
        c.r = clamp255((c.r * c.a) / 255);
        c.g = clamp255((c.g * c.a) / 255);
        c.b = clamp255((c.b * c.a) / 255);
    }
}

/// Sequential composition: three blends and a clamp threaded through one `&mut`.
pub fn rgba_pipeline(dst: &mut Rgba, a: &Rgba, b: &Rgba, mode: i32) {
    let m1 = rgba_blend_mode(a, b, mode);
    let m2 = rgba_lerp(&m1, b, 128);
    let m3 = rgba_add_saturating(&m2, a);
    dst.r = m3.r;
    dst.g = m3.g;
    dst.b = m3.b;
    dst.a = m3.a;
    rgba_clamp_inline(dst);
}
