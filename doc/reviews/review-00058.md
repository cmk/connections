# MR !58 — Plan 36: `ConnL`/`ConnR`/`ConnK` rename + README/rustdoc refactor

## Summary

- Reshapes `ViewL`/`ViewR`/`Triple` capability traits as
  `ConnL`/`ConnR`/`ConnK` with method-shape (`conn_l(&self) ->
  Conn<A, B, L>`, `conn_r(&self) -> Conn<A, B, R>`) and blanket impls
  on `Conn<A, B, L>` / `Conn<A, B, R>`. The trait names match the
  value-type spellings on purpose: a generic `T: ConnL<A, B>` bound
  accepts both triple markers and raw `Conn<A, B, L>` values
  uniformly. The old `ConnL` / `ConnR` type aliases are dropped —
  value type is `Conn<A, B>` (L is the default kind) or
  `Conn<A, B, R>` everywhere.
- Pre-1.0, no back-compat aliases ship: `ceiling`, `inner`, `ceiling1`,
  `ceiling2` removed from inherent and trait surface. Final method set
  is exactly `ceil` / `upper` (L-side) and `floor` / `lower` (R-side);
  triples and `ConnK` bounds expose all four. Macro renames:
  `triple!` → `conn_k!`, `compose!` → `compose_k!`; new `compose!`
  forwarder to `compose_l!` mirrors the `K = L` default.
- README + lib.rs preamble + module preambles reordered so everyday
  readers meet `.ceil/.floor/.upper` on a named const (the new "Get
  started in 30 seconds" block) before any trait name. New "Naming
  the methods" sidebar explains the two naming axes (direction vs
  position) and why there's no `.inner` method. New "When NOT to use
  a Conn" section drafted from feedback on runtime-parameterised
  helpers, validation wrappers, and policy-injection sites.

## Test plan

- [ ] `cargo test --workspace` — all 887 lib unit tests pass; all
      11 integration tests (`int_*`, `fixed_nz_iso_galois`,
      `compile_fail`, `macros_feature_smoke`) green; doctest count
      unchanged (44 passed, 11 ignored).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] Local pre-push hook (`RUSTDOCFLAGS="-D warnings" cargo doc
      --no-deps --features testing --document-private-items`) —
      clean.
- [ ] `scripts/check_readme_mirror.sh` — exits 0 (manifest stays
      empty by design — README narrative examples and const-site
      doctests serve distinct purposes).
- [ ] Spot check: the README "Get started in 30 seconds" block,
      Examples 1, 5, 7 all compile and pass with the new names.
