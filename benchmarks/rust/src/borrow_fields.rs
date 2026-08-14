//! Unannotated Rust. Structs and enums that *hold* borrows, rather than taking them
//! as parameters. Every other source in this corpus passes `&`/`&mut` at the top
//! level only, so Prusti's `p_Ref_mutable` / `p_Ref_immutable` never appears nested
//! inside another type predicate. Here it does: the struct's footprint contains a
//! borrow, so folding it drags that permission in and unfolding hands it back.
//!
//! **Prusti boundary, measured 2026-08-14.** A borrow-holding struct may be built and
//! used locally, but may *not* be a parameter: `fn f(c: &mut Cursor)` encodes to a
//! program its own Silicon run rejects with `insufficient.permission`, reported as
//! `[Prusti internal error] ... could not be backtranslated`. Nine such members were
//! dropped from this file; `borrow_fields_rejected.rs.txt` keeps them verbatim. So the
//! borrow always enters as a `&mut Point` parameter here and is packed into the struct
//! inside the body.
//!
//! Tiers:
//!   0  shared borrow in a struct field    -- read through one indirection
//!   1  mutable borrow in a struct field   -- write through a stored `&mut`
//!   2  two mutable borrows in one struct  -- permission traffic between fields
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 borrow_fields.rs

pub struct Point {
    pub x: i32,
    pub y: i32,
}

// ---------------------------------------------------------------- tier 0: shared borrow field

pub struct View<'a> {
    pub p: &'a Point,
}

pub fn view_x(v: &View) -> i32 {
    v.p.x
}

pub fn view_sum(v: &View) -> i32 {
    v.p.x + v.p.y
}

pub fn view_here(p: &Point) -> i32 {
    let v = View { p };
    v.p.x + v.p.y
}

pub fn view_pick(p: &Point, q: &Point, take_first: bool) -> i32 {
    let v = if take_first { View { p } } else { View { p: q } };
    v.p.x
}

pub fn view_nested(p: &Point) -> i32 {
    let v = View { p };
    let w = View { p: v.p };
    w.p.x + v.p.y
}

// ---------------------------------------------------------------- tier 1: mutable borrow field

pub struct Cursor<'a> {
    pub p: &'a mut Point,
}

pub fn cursor_here(p: &mut Point) {
    let c = Cursor { p };
    c.p.x = c.p.x + 1;
    c.p.y = c.p.y - 1;
}

pub fn cursor_branch(p: &mut Point, up: bool) {
    let c = Cursor { p };
    if up {
        c.p.y = c.p.y + 1;
    } else {
        c.p.y = c.p.y - 1;
    }
}

pub fn cursor_write_then_read(p: &mut Point) -> i32 {
    let c = Cursor { p };
    c.p.x = 7;
    c.p.x + c.p.y
}

pub fn cursor_guarded_write(p: &mut Point, engage: bool) {
    let c = Cursor { p };
    if engage {
        c.p.x = c.p.x + c.p.y;
    }
}

// ---------------------------------------------------------------- tier 2: two borrows, one struct

pub struct Pair<'a> {
    pub a: &'a mut Point,
    pub b: &'a mut Point,
}

pub fn pair_here(p: &mut Point, q: &mut Point) {
    let pr = Pair { a: p, b: q };
    pr.a.x = pr.a.x + 1;
    pr.b.x = pr.b.x + 1;
}

pub fn pair_copy_here(p: &mut Point, q: &mut Point) {
    let pr = Pair { a: p, b: q };
    pr.b.x = pr.a.x;
    pr.b.y = pr.a.y;
}

pub fn pair_guarded_here(p: &mut Point, q: &mut Point, to_a: bool) {
    let pr = Pair { a: p, b: q };
    if to_a {
        pr.a.y = pr.a.y + 1;
    } else {
        pr.b.y = pr.b.y + 1;
    }
}
