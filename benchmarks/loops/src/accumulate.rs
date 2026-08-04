//! Loop corpus: a loop that carries a second variable and reads a struct field
//! it never writes — the read-only framing case.

pub struct Config {
    pub step: i32,
    pub limit: i32,
}

pub fn accumulate(cfg: &Config) -> i32 {
    let mut total = 0;
    let mut i = 0;
    while i < cfg.limit {
        total += cfg.step;
        i += 1;
    }
    total
}
