# Benchmark: silver-oxide vs Silicon — `inhale_exhale.vpr`

> Presentation-ready summary. Single small program, single-run timings (not averaged) —
> illustrative of the "verify simple programs fast" project goal, not a full evaluation.

## What was measured

Program: `cases/inhale_exhale.vpr` — 3 methods exercising permissions, inhale/exhale,
path-conditioned assume/assert:
- `inex` — inhale `acc(x.f)`, exhale full permission. **Expected: pass.**
- `remembering` — value forgotten across an exhale/inhale. **Expected: fail** (its final
  `assert x.f == 10` is intentionally unprovable; see the source comment).
- `under_pc` — `assume (b && true) ==> x.f==10` then `assert (b && b) ==> x.f==10`. **Expected: pass.**

**Verdict was identical across all backends:** `inex` ✓, `under_pc` ✓, `remembering` ✗
(`assert.failed` at line 14). So silver-oxide agrees with Silicon on this program.

## Results

| Setup | Verification time | Wall (per file) | Peak memory |
|---|---|---|---|
| **silver-oxide** (egg backend) | **~1.2 ms** | **< 10 ms** (raw binary) | **~4 MB** |
| Silicon via **ViperServer**, warm JVM (the *fair* baseline) | **~0.52 s** | ~0.6–0.8 s | (shared JVM) |
| Silicon **standalone**, fresh JVM | ~3.75 s (self-reported) | ~4.3 s (cold-first 10.9 s) | ~340 MB (760 MB cold) |

The warm ViperServer figure is from a **from-source build of `viperproject/viperserver` master**
(ViperServer 3.1.0 `e04fd8b`, bundling Silicon master), driven with 6 back-to-back verifications of
the same file in one server. Per-job overall time warmed **1.93 s → 0.81 → 0.69 → 0.66 → 0.56 →
0.52 s** as the JVM JIT'd; warm per-method solver time was **~0.00 s** (sub-10 ms). The bundled VS
Code 3.1.0 (`bb63ef0`) gave a comparable ~0.74 s.

silver-oxide phase breakdown (release, total ~1.5 ms): parse 143 µs · typecheck 54 µs ·
translate 30 µs · analyze 10 µs · **verify (egg saturation) 1.2 ms** (≈80 % of total).

### Headline ratios (this program)
- vs **warm ViperServer** (fairest baseline, master from source): **~430× faster** verification,
  ~80× less memory.
- vs **standalone Silicon**: **~3000× faster** verification, **~400×** lower wall time.

## Why the gap (and why it's honest)

- silver-oxide discharges these structural/permission obligations by **equality saturation in an
  e-graph** — no SMT solver involved on this program (Z3 not even linked into the run).
- Silicon, even with a warm JVM (ViperServer), pays a **fixed per-job cost**: spawning a fresh
  **Z3** process and re-emitting its **background axiomatization** (heaps, permissions, sets) before
  any obligation is checked. That fixed cost — not work proportional to a 3-method file — dominates
  Silicon's ~0.52 s here. The e-graph approach sidesteps exactly that for these obligations.
- **Z3-spawn floor**: launching one do-nothing Z3 instance (spawn + a trivial `(check-sat)` + exit),
  measured *from a Rust binary* spawning the actual Z3 executable, is **~14.5 ms** (Z3 4.8.7, the
  build Silicon uses; ~10 ms for system Z3 4.15.1). So Z3 startup is only a small slice of Silicon's
  0.52 s — but note it is already **~12× silver-oxide's entire ~1.2 ms verification**. Even a single
  solver round-trip would dominate; the egg backend issues none on this program.

## Caveats (state these on the slide)

- **Tiny program**: the ratio is mostly Silicon's *fixed overhead*; it will compress on larger
  inputs where Silicon's per-obligation Z3 work grows. A size-scaling curve is the proper next step.
- **Best case for the hypothesis**: silver-oxide used only equality saturation here; the Z3
  fallback path was not exercised.
- **Single run**, one machine; not statistically averaged.
- ViperServer **result caching** can make repeat runs ≈ free; numbers above are uncached.

## Environment / versions

- silver-oxide: `backend` branch, release build (`cargo build --release`), egg 0.11.
- Silicon/ViperServer: **from-source `viperproject/viperserver` master** (ViperServer 3.1.0
  `e04fd8b`, Silicon master), built with `sbt assembly` →
  `viperserver/target/scala-2.13/viperserver.jar`. (Cross-checked against the VS Code bundled
  3.1.0 `bb63ef0`; standalone numbers used a separate Silicon 1.1-SNAPSHOT `cec06e49` checkout.)
- Z3 4.8.7; OpenJDK 17 — JDK 25 breaks the sbt/Scala build of both Silicon and ViperServer.
- Linux; timings via `/usr/bin/time` (wall/RSS) and the tools' self-reported verification time.
- `under_pc` passing in silver-oxide required two small egg rewrite rules added in this work
  (`ite(c,true,false)⇒c`, `ite(c,c,false)⇒c`), i.e. equality reasoning, no SMT.

## Reproduce

silver-oxide (avoid `cargo run` — its freshness check adds ~180 ms):
```
cargo build --release
target/release/verifier cases/inhale_exhale.vpr      # prints [TIMING] phase breakdown to stderr
```
Silicon standalone (JDK 17):
```
cd ~/Documents/ethz/thesis/silicon
env JAVA_HOME=/usr/lib/jvm/java-17-openjdk PATH=/usr/lib/jvm/java-17-openjdk/bin:$PATH \
    Z3_EXE=/usr/sbin/z3 ./silicon.sh <abs-path>/inhale_exhale.vpr
```
ViperServer from source (warm; JDK 17):
```
cd ~/Documents/ethz/thesis && git clone --recursive --depth 1 \
    https://github.com/viperproject/viperserver.git
cd viperserver && JAVA_HOME=/usr/lib/jvm/java-17-openjdk \
    PATH=$JAVA_HOME/bin:$PATH sbt assembly        # → target/scala-2.13/viperserver.jar
# start (raise -m so it accepts many jobs; default caps at 3 and returns {"id":-1} when full):
java -jar target/scala-2.13/viperserver.jar --serverMode HTTP --port 12350 -m 100 --logLevel INFO
```
Then `POST /verify {"arg":"silicon --z3Exe <z3> <file>"}` repeatedly and read the server log's
`Verification finished in Xs` lines (one per job; first is cold, later ones warm). The bundled z3
works: `.../viper-admin.viper-5.3.2-linux-x64/dependencies/ViperTools/z3/bin/z3`.
