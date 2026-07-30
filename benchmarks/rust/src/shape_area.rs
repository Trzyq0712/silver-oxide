//! Benchmark input: **payload enums**.
//!
//! Unannotated Rust. An enum whose variants carry nested structs, so each match arm
//! must unfold a payload predicate before touching its fields — the arm-local
//! fold/unfold traffic that makes a block's held permission branch-structured.
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 shape_area.rs

pub struct Pt {
    pub x: i32,
    pub y: i32,
}

pub struct Span {
    pub lo: Pt,
    pub hi: Pt,
}

pub enum Shape {
    Empty,
    Dot(Pt),
    Segment(Pt, Pt),
    Box(Span),
    Cross(Span, i32),
}

pub fn pt(x: i32, y: i32) -> Pt {
    Pt { x, y }
}

pub fn span(lo: Pt, hi: Pt) -> Span {
    Span { lo, hi }
}

pub fn span_width(s: &Span) -> i32 {
    s.hi.x - s.lo.x
}

pub fn span_height(s: &Span) -> i32 {
    s.hi.y - s.lo.y
}

pub fn span_area(s: &Span) -> i32 {
    let w = span_width(s);
    let h = span_height(s);
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

pub fn shape_tag(s: &Shape) -> i32 {
    match s {
        Shape::Empty => 0,
        Shape::Dot(_) => 1,
        Shape::Segment(_, _) => 2,
        Shape::Box(_) => 3,
        Shape::Cross(_, _) => 4,
    }
}

/// Every arm unfolds a different payload shape.
pub fn shape_area(s: &Shape) -> i32 {
    match s {
        Shape::Empty => 0,
        Shape::Dot(_) => 0,
        Shape::Segment(a, b) => {
            let dx = b.x - a.x;
            let dy = b.y - a.y;
            if dx < 0 {
                -dx + dy
            } else {
                dx + dy
            }
        }
        Shape::Box(sp) => span_area(sp),
        Shape::Cross(sp, arm) => {
            let base = span_area(sp);
            if *arm < 0 {
                base
            } else {
                base + *arm * 4
            }
        }
    }
}

pub fn shape_center(s: &Shape) -> Pt {
    match s {
        Shape::Empty => pt(0, 0),
        Shape::Dot(p) => pt(p.x, p.y),
        Shape::Segment(a, b) => pt((a.x + b.x) / 2, (a.y + b.y) / 2),
        Shape::Box(sp) => pt((sp.lo.x + sp.hi.x) / 2, (sp.lo.y + sp.hi.y) / 2),
        Shape::Cross(sp, _) => pt((sp.lo.x + sp.hi.x) / 2, (sp.lo.y + sp.hi.y) / 2),
    }
}

pub fn shape_is_degenerate(s: &Shape) -> bool {
    match s {
        Shape::Empty => true,
        Shape::Dot(_) => true,
        Shape::Segment(a, b) => a.x == b.x && a.y == b.y,
        Shape::Box(sp) => span_width(sp) == 0 || span_height(sp) == 0,
        Shape::Cross(sp, arm) => *arm == 0 && span_width(sp) == 0,
    }
}

/// Mutating match arms on a `&mut` payload enum: the arm writes through the unfolded
/// payload, which must be re-folded at the arm's exit.
pub fn shape_translate(s: &mut Shape, dx: i32, dy: i32) {
    match s {
        Shape::Empty => {}
        Shape::Dot(p) => {
            p.x = p.x + dx;
            p.y = p.y + dy;
        }
        Shape::Segment(a, b) => {
            a.x = a.x + dx;
            a.y = a.y + dy;
            b.x = b.x + dx;
            b.y = b.y + dy;
        }
        Shape::Box(sp) => {
            sp.lo.x = sp.lo.x + dx;
            sp.lo.y = sp.lo.y + dy;
            sp.hi.x = sp.hi.x + dx;
            sp.hi.y = sp.hi.y + dy;
        }
        Shape::Cross(sp, arm) => {
            sp.lo.x = sp.lo.x + dx;
            sp.lo.y = sp.lo.y + dy;
            sp.hi.x = sp.hi.x + dx;
            sp.hi.y = sp.hi.y + dy;
            if *arm < 0 {
                *arm = 0;
            }
        }
    }
}

pub fn shape_grow(s: &mut Shape, k: i32) {
    match s {
        Shape::Empty => {}
        Shape::Dot(p) => {
            p.x = p.x * k;
            p.y = p.y * k;
        }
        Shape::Segment(a, b) => {
            b.x = a.x + (b.x - a.x) * k;
            b.y = a.y + (b.y - a.y) * k;
        }
        Shape::Box(sp) => {
            sp.hi.x = sp.lo.x + span_width(sp) * k;
            sp.hi.y = sp.lo.y + span_height(sp) * k;
        }
        Shape::Cross(sp, arm) => {
            sp.hi.x = sp.lo.x + span_width(sp) * k;
            sp.hi.y = sp.lo.y + span_height(sp) * k;
            *arm = *arm * k;
        }
    }
}

/// Construction per arm: an arm that *builds* a differently-shaped payload than the
/// one it destructured.
pub fn shape_bounding_box(s: &Shape) -> Shape {
    match s {
        Shape::Empty => Shape::Empty,
        Shape::Dot(p) => Shape::Box(span(pt(p.x, p.y), pt(p.x, p.y))),
        Shape::Segment(a, b) => {
            let lox = if a.x < b.x { a.x } else { b.x };
            let loy = if a.y < b.y { a.y } else { b.y };
            let hix = if a.x < b.x { b.x } else { a.x };
            let hiy = if a.y < b.y { b.y } else { a.y };
            Shape::Box(span(pt(lox, loy), pt(hix, hiy)))
        }
        Shape::Box(sp) => Shape::Box(span(pt(sp.lo.x, sp.lo.y), pt(sp.hi.x, sp.hi.y))),
        Shape::Cross(sp, arm) => {
            let a = if *arm < 0 { 0 } else { *arm };
            Shape::Box(span(pt(sp.lo.x - a, sp.lo.y - a), pt(sp.hi.x + a, sp.hi.y + a)))
        }
    }
}

pub fn shape_compare_area(p: &Shape, q: &Shape) -> i32 {
    let ap = shape_area(p);
    let aq = shape_area(q);
    if ap < aq {
        -1
    } else {
        if aq < ap {
            1
        } else {
            0
        }
    }
}
