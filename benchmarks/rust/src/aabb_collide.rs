//! Benchmark input: **dominator depth**.
//!
//! Unannotated Rust — obligations come from Prusti's type predicates. Axis-aligned
//! box tests written as deeply nested `if`/`else` (3-5 levels, no early return), so
//! inner blocks carry long path conditions that are strict supersets of their
//! dominators' — the shape a dominator-scoped scratch would inherit along.
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 aabb_collide.rs

pub struct P2 {
    pub x: i32,
    pub y: i32,
}

pub struct Aabb {
    pub lo: P2,
    pub hi: P2,
}

pub struct Hit {
    pub touched: bool,
    pub depth: i32,
    pub axis: i32,
}

pub fn p2_new(x: i32, y: i32) -> P2 {
    P2 { x, y }
}

pub fn aabb_new(lo: P2, hi: P2) -> Aabb {
    Aabb { lo, hi }
}

pub fn aabb_width(b: &Aabb) -> i32 {
    b.hi.x - b.lo.x
}

pub fn aabb_height(b: &Aabb) -> i32 {
    b.hi.y - b.lo.y
}

/// Depth 2: outer axis test, inner ordering test.
pub fn aabb_normalize(b: &mut Aabb) {
    if b.hi.x < b.lo.x {
        let t = b.lo.x;
        b.lo.x = b.hi.x;
        b.hi.x = t;
    }
    if b.hi.y < b.lo.y {
        let t = b.lo.y;
        b.lo.y = b.hi.y;
        b.hi.y = t;
    }
}

/// Depth 3: x-overlap ⟹ y-overlap ⟹ strictness.
pub fn aabb_overlaps(p: &Aabb, q: &Aabb) -> bool {
    let mut res = false;
    if p.lo.x <= q.hi.x {
        if q.lo.x <= p.hi.x {
            if p.lo.y <= q.hi.y {
                if q.lo.y <= p.hi.y {
                    res = true;
                }
            }
        }
    }
    res
}

/// Depth 4: containment on both axes, each split into lo/hi.
pub fn aabb_contains_point(b: &Aabb, p: &P2) -> bool {
    let mut inside = false;
    if b.lo.x <= p.x {
        if p.x <= b.hi.x {
            if b.lo.y <= p.y {
                if p.y <= b.hi.y {
                    inside = true;
                } else {
                    inside = false;
                }
            }
        }
    }
    inside
}

/// Depth 5, and the arms do real work rather than only setting a flag: clamps a
/// point into the box, choosing the axis it was pushed along.
pub fn aabb_clamp_point(b: &Aabb, p: &mut P2) -> i32 {
    let mut axis = 0;
    if p.x < b.lo.x {
        p.x = b.lo.x;
        if p.y < b.lo.y {
            p.y = b.lo.y;
            axis = 3;
        } else {
            if b.hi.y < p.y {
                p.y = b.hi.y;
                axis = 3;
            } else {
                axis = 1;
            }
        }
    } else {
        if b.hi.x < p.x {
            p.x = b.hi.x;
            if p.y < b.lo.y {
                p.y = b.lo.y;
                axis = 3;
            } else {
                if b.hi.y < p.y {
                    p.y = b.hi.y;
                    axis = 3;
                } else {
                    axis = 1;
                }
            }
        } else {
            if p.y < b.lo.y {
                p.y = b.lo.y;
                axis = 2;
            } else {
                if b.hi.y < p.y {
                    p.y = b.hi.y;
                    axis = 2;
                } else {
                    axis = 0;
                }
            }
        }
    }
    axis
}

/// Nested branching *plus* penetration arithmetic in the innermost arm.
pub fn aabb_hit(p: &Aabb, q: &Aabb) -> Hit {
    let mut h = Hit {
        touched: false,
        depth: 0,
        axis: 0,
    };
    if p.lo.x <= q.hi.x {
        if q.lo.x <= p.hi.x {
            if p.lo.y <= q.hi.y {
                if q.lo.y <= p.hi.y {
                    let dxl = q.hi.x - p.lo.x;
                    let dxr = p.hi.x - q.lo.x;
                    let dyl = q.hi.y - p.lo.y;
                    let dyr = p.hi.y - q.lo.y;
                    let dx = if dxl < dxr { dxl } else { dxr };
                    let dy = if dyl < dyr { dyl } else { dyr };
                    h.touched = true;
                    if dx < dy {
                        h.depth = dx;
                        h.axis = 1;
                    } else {
                        h.depth = dy;
                        h.axis = 2;
                    }
                }
            }
        }
    }
    h
}

/// Depth 3 with a mutating inner arm on a `&mut` receiver.
pub fn aabb_grow_to_contain(b: &mut Aabb, p: &P2) {
    if p.x < b.lo.x {
        b.lo.x = p.x;
    } else {
        if b.hi.x < p.x {
            b.hi.x = p.x;
        }
    }
    if p.y < b.lo.y {
        b.lo.y = p.y;
    } else {
        if b.hi.y < p.y {
            b.hi.y = p.y;
        }
    }
}

pub fn aabb_area(b: &Aabb) -> i32 {
    let w = aabb_width(b);
    let h = aabb_height(b);
    if w < 0 {
        0
    } else {
        if h < 0 {
            0
        } else {
            w * h
        }
    }
}

/// Composition: the deep-nesting functions called in sequence, so the caller's
/// blocks inherit obligations from several of them. `q` is mutated by the first call
/// and read by the second — a shared reborrow of a `&mut` parameter after a mutation
/// through it.
pub fn aabb_resolve(p: &Aabb, q: &mut Aabb, probe: &mut P2) -> i32 {
    aabb_normalize(q);
    let hit = aabb_hit(p, q);
    let axis = aabb_clamp_point(p, probe);
    let mut score = 0;
    if hit.touched {
        if hit.axis == axis {
            score = hit.depth * 2;
        } else {
            score = hit.depth;
        }
    } else {
        if aabb_contains_point(p, probe) {
            score = -1;
        } else {
            score = -2;
        }
    }
    score
}
