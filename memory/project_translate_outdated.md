---
name: project-translate-outdated
description: src/translate/ is outdated; typechecking now happens at the Silver level
metadata:
  type: project
---

`src/translate/` is outdated. Type checking is being moved to the Silver (Viper) AST level (`src/silver/typecheck.rs`) and will run before any VMIR translation.

As of 2026-05-20, `src/translate/` is **unlinked from the build**: `pub mod translate;` is commented out in `src/lib.rs`, and the `#[cfg(test)] mod tests` block there (which drove `VmirTranslator::translate`) is gated off with `#[cfg(any())]`. Files kept on disk for reference — they don't compile against the new silver AST (old AST split heap/pure exprs into `HeapExp`/`PureExp`; new AST is unified `Exp { ty, kind: Box<ExpKind> }`). User wants translate reimplemented later, reusing ideas.

**Why:** The architecture decision is to typecheck on the Silver AST rather than during/after translation to VMIR. translate blocked the whole crate from compiling, which blocked running `silver/typecheck.rs` tests.

**How to apply:** Do not add new type-checking logic to `src/translate/`. New typechecking work goes in `src/silver/typecheck.rs`. Do NOT delete `src/translate/` — only unlink. To re-enable later, port it to the unified `ExpKind` API then uncomment in `lib.rs`.
