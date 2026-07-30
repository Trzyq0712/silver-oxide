# Rust benchmark corpus

Realistic spec-less Rust, encoded to Viper by Prusti, for measuring verifier cost on
programs that do more computation than a bare enum match. Built to answer whether the
lazy / sticky / dominator-scoped scratch e-graph designs have anything to work with
(`design/block-vmir/82-two-egraph-block-model.md`, `analysis/scratch_mode_2026-07-30/`).

    src/*.rs        hand-written and generated sources (committed)
    vpr/*.vpr       their Prusti encodings (committed — measurement needs no Prusti)
    encode_all.sh   src -> vpr, skipping anything already up to date
    gen_depth.py    regenerates the depth_d{D}_m{M} family

Rules for every source here, same as `../../../cases/rust/structs_enums.rs`:

- **no `prusti_contracts`** — obligations come from Prusti's own type predicates
  (framing, fold/unfold, discriminant well-formedness), so the corpus measures the
  encoding every Prusti user pays rather than hand-written specs;
- **no loops, no recursion, no returned references**; `&mut` parameters are fine;
- every member must verify — a failing member stops at its failing instruction and has
  no stable cost.

## What each file is for

| file | axis |
|---|---|
| `mat3_mul.rs` | block length: unrolled 3x3 linear algebra, 30+ statement straight-line blocks |
| `vec3_math.rs` | block length x call density: every operation built from calls to smaller ones |
| `aabb_collide.rs` | dominator depth: if/else nested 3-5 deep, arms doing real work |
| `state_machine.rs` | dominator depth x arm count: a 5x5 `State`/`Event` match grid |
| `color_blend.rs` | branch cascades: many sequential two-way branches per member |
| `shape_area.rs` | payload enums: arms that unfold nested-struct payloads and write through them |
| `inventory.rs` | Option/Result paths: hand-rolled `Maybe`/`Res`, error arms, dispatch to one of three `&mut` fields |
| `bank_transfer.rs` | permission traffic: two `&mut` accounts in one call, guarded debits, swaps |
| `physics_step.rs` | composition: three bodies through integrate -> clamp -> bounce |
| `classify_tuple.rs` | many sequential blocks, shallow cubes: an 8-element buffer classified element by element |
| `depth_d{D}_m{M}.rs` | the two axes separated and scaled: D nesting levels x M statements per block |

## Encoding

    ./encode_all.sh              # all of src/
    ./encode_all.sh mat3_mul     # one file

Needs the local Prusti checkout (`../../tools/prusti_encode.sh`, override with
`PRUSTI_RUSTC`). Roughly 1-3 minutes and ~0.5-1 MB of Viper per source, which is why
`vpr/` is committed.

## Note on the `&mut`-into-a-call gap

Every program here that calls a helper taking `&mut` — that is, most of them — failed to
verify with "insufficient permission" when the corpus was first built. The diagnosis
(`SILVER_OXIDE_TRACE_MISS`) was that the reborrow's address term meets the held chunk's
address only after a **full** saturation, while the framing-miss retry ran the
terminating reductions only. Fixed in `heap_subtract_inner` (commit "retry a framing
miss under full saturation before failing"), which is why every member verifies now.

The minimized reproducer lives in `tests/cases/passing/permissions/mut_reborrow_call.vpr`.
If a future change reintroduces the gap, that case fails first and the whole corpus
follows.
