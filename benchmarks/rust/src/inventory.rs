//! Benchmark input: **Option/Result-shaped control flow**.
//!
//! Unannotated Rust with hand-rolled `Maybe`/`Res` enums (as `structs_enums.rs` does),
//! so error paths are ordinary enum arms: a success arm carrying a payload and a
//! failure arm carrying a code. Produces blocks whose cube is a discriminant fact and
//! whose body then reads the payload — the interplay of tag knowledge and framing.
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 inventory.rs

pub struct Item {
    pub id: i32,
    pub qty: i32,
    pub price: i32,
}

pub struct Slots {
    pub a: Item,
    pub b: Item,
    pub c: Item,
}

pub enum Maybe {
    None,
    Some(i32),
}

pub enum Res {
    Ok(i32),
    Err(i32),
}

pub fn item_new(id: i32, qty: i32, price: i32) -> Item {
    Item { id, qty, price }
}

pub fn item_value(it: &Item) -> i32 {
    it.qty * it.price
}

pub fn item_is_empty(it: &Item) -> bool {
    it.qty == 0
}

pub fn maybe_or(m: Maybe, dflt: i32) -> i32 {
    match m {
        Maybe::None => dflt,
        Maybe::Some(v) => v,
    }
}

pub fn maybe_add(p: Maybe, q: Maybe) -> Maybe {
    match p {
        Maybe::None => match q {
            Maybe::None => Maybe::None,
            Maybe::Some(b) => Maybe::Some(b),
        },
        Maybe::Some(a) => match q {
            Maybe::None => Maybe::Some(a),
            Maybe::Some(b) => Maybe::Some(a + b),
        },
    }
}

pub fn res_or(r: Res, dflt: i32) -> i32 {
    match r {
        Res::Ok(v) => v,
        Res::Err(_) => dflt,
    }
}

pub fn res_code(r: &Res) -> i32 {
    match r {
        Res::Ok(_) => 0,
        Res::Err(c) => *c,
    }
}

/// Guarded withdraw: the failure arm returns a code, the success arm mutates.
pub fn item_take(it: &mut Item, n: i32) -> Res {
    if n < 0 {
        Res::Err(1)
    } else {
        if it.qty < n {
            Res::Err(2)
        } else {
            it.qty = it.qty - n;
            Res::Ok(n * it.price)
        }
    }
}

pub fn item_put(it: &mut Item, n: i32) -> Res {
    if n < 0 {
        Res::Err(1)
    } else {
        it.qty = it.qty + n;
        Res::Ok(it.qty)
    }
}

pub fn slots_total(s: &Slots) -> i32 {
    item_value(&s.a) + item_value(&s.b) + item_value(&s.c)
}

pub fn slots_find(s: &Slots, id: i32) -> Maybe {
    if s.a.id == id {
        Maybe::Some(s.a.qty)
    } else {
        if s.b.id == id {
            Maybe::Some(s.b.qty)
        } else {
            if s.c.id == id {
                Maybe::Some(s.c.qty)
            } else {
                Maybe::None
            }
        }
    }
}

/// Dispatch to one of three `&mut` fields, then a guarded mutation inside — the
/// permission-selection shape under a discriminant-free integer cube.
pub fn slots_take(s: &mut Slots, id: i32, n: i32) -> Res {
    if s.a.id == id {
        item_take(&mut s.a, n)
    } else {
        if s.b.id == id {
            item_take(&mut s.b, n)
        } else {
            if s.c.id == id {
                item_take(&mut s.c, n)
            } else {
                Res::Err(3)
            }
        }
    }
}

/// Two results combined by matching on both — a 2x2 arm grid over enum payloads.
pub fn slots_move(s: &mut Slots, n: i32) -> Res {
    let taken = item_take(&mut s.a, n);
    match taken {
        Res::Err(c) => Res::Err(c),
        Res::Ok(v) => {
            let put = item_put(&mut s.b, n);
            match put {
                Res::Err(c) => Res::Err(c + 10),
                Res::Ok(q) => Res::Ok(v + q),
            }
        }
    }
}

pub fn slots_restock(s: &mut Slots, n: i32) {
    if item_is_empty(&s.a) {
        s.a.qty = n;
    }
    if item_is_empty(&s.b) {
        s.b.qty = n;
    }
    if item_is_empty(&s.c) {
        s.c.qty = n;
    }
}

/// Maybe-chaining: three lookups folded together, each arm carrying tag knowledge.
pub fn slots_sum_two(s: &Slots, id1: i32, id2: i32) -> i32 {
    let m1 = slots_find(s, id1);
    let m2 = slots_find(s, id2);
    let both = maybe_add(m1, m2);
    maybe_or(both, -1)
}

pub fn slots_repriced_value(s: &Slots, id: i32, price: i32) -> i32 {
    let found = slots_find(s, id);
    match found {
        Maybe::None => slots_total(s),
        Maybe::Some(q) => {
            let base = slots_total(s);
            if price < 0 {
                base
            } else {
                base + q * price
            }
        }
    }
}

pub fn slots_audit(s: &mut Slots, id: i32, n: i32) -> i32 {
    let r = slots_take(s, id, n);
    let code = res_code(&r);
    if code == 0 {
        slots_restock(s, 1);
        res_or(r, 0)
    } else {
        res_or(r, -code)
    }
}
