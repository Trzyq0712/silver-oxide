# Memory Index

- [src/translate/ is outdated; typechecking at Silver level](project_translate_outdated.md) — do not add type-checking logic to translate/; new work goes in silver/typecheck.rs
- [Internal Type::Real == Viper Perm](reference_real_vs_perm.md) — no Real keyword in Viper; parser maps Perm/Rational → Type::Real
- [Docs: drop speculative impl detail](feedback_docs_scope.md) — when updating CLAUDE.md, document only settled design; omit verifier impl strategy until decided
- [Minimal e-node encoding](feedback_minimal_enode_encoding.md) — fold negation into enclosing ite (acc && !v → Ite(v,false,acc)); one ite per conjunct in verify backend
