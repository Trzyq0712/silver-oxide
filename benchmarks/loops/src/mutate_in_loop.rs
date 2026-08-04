//! Loop corpus: a loop that writes through a `&mut` — permission must be
//! carried by the invariant across the back edge.

pub struct Counter {
    pub value: i32,
    pub bumps: i32,
}

pub fn bump_n(c: &mut Counter, n: i32) {
    let mut i = 0;
    while i < n {
        c.value += 2;
        c.bumps += 1;
        i += 1;
    }
}
