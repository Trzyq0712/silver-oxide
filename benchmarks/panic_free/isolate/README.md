# Isolating the non-arithmetic unreachability failures

Hand-written Viper, not Prusti output. `probe_unreachable_nonarith.rs` found five
contradictions that fail with no arithmetic in them; these files rebuild those five shapes
one encoding layer at a time to find which layer is responsible. Every method in every
file must verify — the failures below are the result, not the intent.

| file | what it adds over the previous | result |
|---|---|---|
| `l0_native.vpr` | nothing — native `Int`/`Bool`, native fields | **5/5 pass** |
| `l1_boxed.vpr` | `s_Int_i32`/`s_Bool` domains, comparisons as functions returning a boxed bool, `s_Bool_value(t) == false` branch tests | **3/5** — `eq_transitive`, `two_literals` fail |
| `l1b_split.vpr` | applies L1's two changes *separately* | value boxing passes, **boolean reification fails** |
| `l2_heap.vpr` | predicates, `..._snap` functions, bodyless `..._assign` methods | the three L1 survivors still pass |
| `l3_roundtrip.vpr` | struct predicate with `fold`/`unfold`, plus the `make_generic`/`make_concrete` round trip through the erased `p_Param` | `write_then_read`, `frame_other_field` fail here |
| `l4_equality.vpr` | equality chaining through a shared term, no heap | **4/4 pass** |

## Result 1: boolean reification, confirmed (2 of 5)

`l1b_split.vpr` separates the two changes L1 made at once. Boxing the *values* and
comparing them natively passes; leaving values native and reifying the *comparison* into
`s_Bool_cons(..)` / `s_Bool_value(t) == false` fails. Same two members, both directions.

So `eq_transitive` and `eq_two_literals` fail because a boolean lives as a term to be
evaluated rather than as a fact, and value boxing is not implicated at all.

This is the same signature as the arithmetic case in the parent directory: under `0 < x`
we prove `assert !(x == 0)` but not `assert (x == 0) == false`, and asserting the former
first makes the latter go through.

## Result 2: reification refuted for the other three

`bool_after_join`, `frame_other_field`, and `write_then_read` pass at L0, L1 *and* L2 —
reification does not reproduce them. Two of the three reproduce only at L3, when the
`make_generic`/`make_concrete` round trip is added.

Within L3 the cause is narrower than "the round trip", and is **not yet pinned**. The
`r_link*` probes rule out each obvious candidate individually:

- `r_link1_inverse`, `r_link2_injective` — the erasure's mutual-inverse postconditions and
  the injectivity they give: **pass**;
- `r_link3_old_chain`, `r_link4_old_binds_to_caller` — each half of the `old`-based
  postcondition chain, including binding the callee's `old` to a value the caller read
  before the call: **pass**;
- `l4_equality.vpr` — joining two equalities through a shared term: **passes**;
- `r_link5_stepwise` — the full round trip with all three intermediates asserted: **passes**;
- `r_link6_only_erased_eq` — asserting only `make_generic(before) == make_generic(after)`:
  **passes**;
- `r_link7_only_before_term`, `r_link8_only_bridge_read` — merely *constructing* the
  relevant terms without asserting the equation: **fail**.

So every step is individually derivable and the composition still is not, while a single
asserted equation repairs it and merely materialising terms does not. That rules out
"the term is missing from the e-graph" as a complete explanation.

`bool_after_join` is not reproduced by any file here — `h_join` in `l2_heap.vpr` is its
shape and passes. The untested difference is that Prusti joins through `goto` and
`_from_bbN_to_bbM` flags rather than a structured `if`; that is a hypothesis, not a
finding.

## Running

    cargo build --release --bin verify
    ./target/release/verify benchmarks/panic_free/isolate/l0_native.vpr
