//! Benchmark input: **permission traffic**.
//!
//! Unannotated Rust. Two `&mut` accounts in one call, guarded debits and credits, and
//! swaps — the shapes where a block's held permission becomes branch-structured and
//! consumption must be proven against a sum rather than a single chunk.
//!
//! No loops, no recursion, no returned references.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 bank_transfer.rs

pub struct Account {
    pub id: i32,
    pub balance: i32,
    pub limit: i32,
}

pub struct Ledger {
    pub from: Account,
    pub to: Account,
    pub fees: i32,
}

pub fn account_new(id: i32, balance: i32, limit: i32) -> Account {
    Account { id, balance, limit }
}

pub fn account_available(a: &Account) -> i32 {
    a.balance + a.limit
}

pub fn account_is_overdrawn(a: &Account) -> bool {
    a.balance < 0
}

pub fn account_deposit(a: &mut Account, amount: i32) {
    if 0 < amount {
        a.balance = a.balance + amount;
    }
}

/// Guarded debit: the amount only leaves the account when it is covered.
pub fn account_withdraw(a: &mut Account, amount: i32) -> bool {
    let mut ok = false;
    if 0 < amount {
        if amount <= account_available(a) {
            a.balance = a.balance - amount;
            ok = true;
        }
    }
    ok
}

/// Two distinct `&mut` accounts live at once — the non-aliasing case.
pub fn transfer(src: &mut Account, dst: &mut Account, amount: i32) -> bool {
    let mut moved = false;
    if 0 < amount {
        if amount <= account_available(src) {
            src.balance = src.balance - amount;
            dst.balance = dst.balance + amount;
            moved = true;
        }
    }
    moved
}

/// A fee split off the transferred amount, so the debit is a sum of two guarded parts.
pub fn transfer_with_fee(src: &mut Account, dst: &mut Account, amount: i32, fee: i32) -> i32 {
    let mut result = 0;
    if amount < 0 {
        result = -1;
    } else {
        if fee < 0 {
            result = -2;
        } else {
            let total = amount + fee;
            if total <= account_available(src) {
                src.balance = src.balance - total;
                dst.balance = dst.balance + amount;
                result = amount;
            } else {
                result = -3;
            }
        }
    }
    result
}

pub fn account_swap_balances(a: &mut Account, b: &mut Account) {
    let t = a.balance;
    a.balance = b.balance;
    b.balance = t;
}

/// Both fields of one struct borrowed mutably in the same call.
pub fn ledger_settle(l: &mut Ledger, amount: i32) -> bool {
    let moved = transfer(&mut l.from, &mut l.to, amount);
    if moved {
        l.fees = l.fees + 1;
    }
    moved
}

pub fn ledger_total(l: &Ledger) -> i32 {
    l.from.balance + l.to.balance + l.fees
}

/// Two sequential settles: the second block's permission state is whatever the first
/// join produced.
pub fn ledger_settle_twice(l: &mut Ledger, first: i32, second: i32) -> i32 {
    let a = ledger_settle(l, first);
    let b = ledger_settle(l, second);
    let mut n = 0;
    if a {
        n = n + 1;
    }
    if b {
        n = n + 2;
    }
    n
}

/// Rebalance: reads both accounts, then writes to whichever side is short — the
/// branch-selected write target.
pub fn ledger_rebalance(l: &mut Ledger) -> i32 {
    let fb = l.from.balance;
    let tb = l.to.balance;
    let mut moved = 0;
    if fb < tb {
        let half = (tb - fb) / 2;
        l.to.balance = l.to.balance - half;
        l.from.balance = l.from.balance + half;
        moved = half;
    } else {
        if tb < fb {
            let half = (fb - tb) / 2;
            l.from.balance = l.from.balance - half;
            l.to.balance = l.to.balance + half;
            moved = half;
        }
    }
    moved
}

pub fn ledger_apply_limits(l: &mut Ledger, limit: i32) {
    if 0 <= limit {
        l.from.limit = limit;
        l.to.limit = limit;
    }
    if account_is_overdrawn(&l.from) {
        l.fees = l.fees + 5;
    }
    if account_is_overdrawn(&l.to) {
        l.fees = l.fees + 5;
    }
}

pub fn ledger_close(l: &mut Ledger) -> i32 {
    let total = ledger_total(l);
    l.from.balance = 0;
    l.to.balance = 0;
    l.fees = 0;
    total
}
