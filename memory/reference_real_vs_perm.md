---
name: reference-real-vs-perm
description: internal Type::Real corresponds to Viper's Perm; no Real keyword in Viper
metadata:
  type: reference
---

Internally the project uses `Real` for the rational/permission type; Viper source uses `Perm`.
There is **no `Real` type keyword** in Viper.

- Parser (`src/silver/peg.rs` `type_()`): `Perm` → `Type::Real`, `Rational` → `Type::Real`.
  An unknown `Real` would parse as a domain/generic type → `lower_type` `todo!()`.
- `final_ast::Type::Real` and `final_display` print `Real` (internal name), not `Perm`.
- Permission amounts (`acc(.., p)`), wildcard, epsilon, and `/` (real division) results are `Real`.
