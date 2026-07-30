//! Benchmark input: **composition**.
//!
//! Unannotated Rust. A world of three bodies stepped through integrate → clamp →
//! bounce, each stage built from the smaller helpers. The point is depth *through
//! calls*: a caller's block inherits obligations from several callees, so the ground
//! graph accumulates a lot before any single block's proof is raised.
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 physics_step.rs

pub struct Vec2 {
    pub x: i32,
    pub y: i32,
}

pub struct Body {
    pub pos: Vec2,
    pub vel: Vec2,
    pub mass: i32,
}

pub struct Bounds {
    pub lo: Vec2,
    pub hi: Vec2,
}

pub struct World {
    pub a: Body,
    pub b: Body,
    pub c: Body,
    pub bounds: Bounds,
    pub ticks: i32,
}

pub fn vec2(x: i32, y: i32) -> Vec2 {
    Vec2 { x, y }
}

pub fn vec2_add_in_place(v: &mut Vec2, d: &Vec2) {
    v.x = v.x + d.x;
    v.y = v.y + d.y;
}

pub fn vec2_scale_in_place(v: &mut Vec2, k: i32) {
    v.x = v.x * k;
    v.y = v.y * k;
}

pub fn vec2_dot(a: &Vec2, b: &Vec2) -> i32 {
    a.x * b.x + a.y * b.y
}

pub fn body_momentum(b: &Body) -> i32 {
    (b.vel.x + b.vel.y) * b.mass
}

pub fn body_energy(b: &Body) -> i32 {
    vec2_dot(&b.vel, &b.vel) * b.mass
}

pub fn body_integrate(b: &mut Body) {
    let dx = b.vel.x;
    let dy = b.vel.y;
    b.pos.x = b.pos.x + dx;
    b.pos.y = b.pos.y + dy;
}

pub fn body_apply_impulse(b: &mut Body, j: &Vec2) {
    if 0 < b.mass {
        b.vel.x = b.vel.x + j.x / b.mass;
        b.vel.y = b.vel.y + j.y / b.mass;
    }
}

/// Clamp with velocity reflection: branch per axis per side, four arms that write two
/// different fields each.
pub fn body_clamp(b: &mut Body, w: &Bounds) -> i32 {
    let mut hits = 0;
    if b.pos.x < w.lo.x {
        b.pos.x = w.lo.x;
        b.vel.x = -b.vel.x;
        hits = hits + 1;
    } else {
        if w.hi.x < b.pos.x {
            b.pos.x = w.hi.x;
            b.vel.x = -b.vel.x;
            hits = hits + 1;
        }
    }
    if b.pos.y < w.lo.y {
        b.pos.y = w.lo.y;
        b.vel.y = -b.vel.y;
        hits = hits + 2;
    } else {
        if w.hi.y < b.pos.y {
            b.pos.y = w.hi.y;
            b.vel.y = -b.vel.y;
            hits = hits + 2;
        }
    }
    hits
}

pub fn body_damp(b: &mut Body, num: i32, den: i32) {
    if 0 < den {
        b.vel.x = (b.vel.x * num) / den;
        b.vel.y = (b.vel.y * num) / den;
    }
}

/// One body's full stage chain: integrate, clamp, damp, plus a branch on the result.
pub fn body_step(b: &mut Body, w: &Bounds) -> i32 {
    body_integrate(b);
    let hits = body_clamp(b, w);
    if 0 < hits {
        body_damp(b, 3, 4);
    } else {
        body_damp(b, 9, 10);
    }
    hits
}

pub fn world_energy(w: &World) -> i32 {
    body_energy(&w.a) + body_energy(&w.b) + body_energy(&w.c)
}

pub fn world_momentum(w: &World) -> i32 {
    body_momentum(&w.a) + body_momentum(&w.b) + body_momentum(&w.c)
}

/// Three bodies stepped in one member: the deepest call composition in the corpus.
pub fn world_step(w: &mut World) -> i32 {
    let ha = body_step(&mut w.a, &w.bounds);
    let hb = body_step(&mut w.b, &w.bounds);
    let hc = body_step(&mut w.c, &w.bounds);
    w.ticks = w.ticks + 1;
    ha + hb + hc
}

pub fn world_kick(w: &mut World, j: &Vec2) {
    body_apply_impulse(&mut w.a, j);
    body_apply_impulse(&mut w.b, j);
    body_apply_impulse(&mut w.c, j);
}

/// Branch selecting *which* body gets the impulse, then a full step — a
/// branch-selected `&mut` target followed by a join.
pub fn world_kick_slowest(w: &mut World, j: &Vec2) -> i32 {
    let ea = body_energy(&w.a);
    let eb = body_energy(&w.b);
    let ec = body_energy(&w.c);
    let mut which = 0;
    if eb < ea {
        which = 1;
        if ec < eb {
            which = 2;
        }
    } else {
        if ec < ea {
            which = 2;
        }
    }
    if which == 0 {
        body_apply_impulse(&mut w.a, j);
    } else {
        if which == 1 {
            body_apply_impulse(&mut w.b, j);
        } else {
            body_apply_impulse(&mut w.c, j);
        }
    }
    which
}

pub fn world_settle(w: &mut World) -> i32 {
    let h1 = world_step(w);
    let e = world_energy(w);
    if e == 0 {
        w.ticks
    } else {
        let h2 = world_step(w);
        h1 + h2
    }
}

pub fn bounds_area(w: &Bounds) -> i32 {
    let dx = w.hi.x - w.lo.x;
    let dy = w.hi.y - w.lo.y;
    if dx < 0 {
        0
    } else {
        if dy < 0 {
            0
        } else {
            dx * dy
        }
    }
}

pub fn world_shrink(w: &mut World, k: i32) {
    if 0 < k {
        w.bounds.lo.x = w.bounds.lo.x + k;
        w.bounds.lo.y = w.bounds.lo.y + k;
        w.bounds.hi.x = w.bounds.hi.x - k;
        w.bounds.hi.y = w.bounds.hi.y - k;
    }
}
