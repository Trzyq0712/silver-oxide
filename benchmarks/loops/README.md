# Loop benchmark corpus

Spec-less Rust *with loops*, encoded to Viper by Prusti. Separate from
`../rust/` because that corpus is held to a mechanical **no-loops** rule.

    src/*.rs   sources (committed)
    vpr/*.vpr  their Prusti encodings (committed — measurement needs no Prusti)

Encode with `../../tools/prusti_encode.sh src/<name>.rs vpr/<name>.vpr`.

## What Prusti emits for a loop

Confirmed here, and it is what our lowering targets: **a goto CFG with the
invariant carried on the loop head's label**. There is no `while` in Prusti's
VIR at all.

    goto bb_1
    label bb_1
      invariant acc(p_Int_i32(_2p), write)
      invariant acc(p_Int_i32(_1p), write)

Prusti infers the *permission* part itself from the PCG (`get_loop_inv`); the
functional part would come from `body_invariant!`. None of these sources use
`prusti_contracts`, matching the `../rust/` rule, so they show the bare shape.

## Status

| file | members | ours | Silicon |
|---|---:|---|---|
| `count_up.rs` | 59 | all verify | verifies |
| `accumulate.rs` | 83 | all verify | verifies |
| `mutate_in_loop.rs` | 84 | `m_bump_n` fails | **also fails** |

`mutate_in_loop` writes through a `&mut` inside the loop. Silicon rejects the
encoding too, so this is not our incompleteness — Prusti's inferred permission
invariant is not enough to carry a written-through borrow across the back edge
without a `body_invariant!`. Kept as a known-divergence marker, not a target.
