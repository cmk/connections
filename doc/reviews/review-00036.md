# MR !36 — `property` → `prop` cleanup

## Summary

- Renames `property` module to `prop`. All `crate::property::*`
  / `connections::property::*` paths become `crate::prop::*` /
  `connections::prop::*`.
- Splits `prop::laws` into `prop::conn` (Galois-connection laws,
  cast lifter laws) and `prop::lattice` (Heyting / Coheyting /
  Bi-Heyting / Boolean laws). The 700-line single-file laws.rs
  becomes two focused files.
- Renames `cast_foo` → `conn_foo` predicates. The `cast_*` prefix
  was a leftover from the `conn::cast` submodule that was folded
  into `conn` in MR !34; every predicate that exercises a `Conn`
  is now `conn_*`.
- Renames `symmetric_foo` → `biheyting_foo` predicates. The trait
  is `Symmetric`, but the laws characterize bi-Heyting algebras;
  matches the existing `biheyting_neg_le_coneg`.
- Alphabetizes all predicate definitions within `prop::conn` and
  `prop::lattice`. Drops the ad-hoc section dividers
  (Heyting / Coheyting / etc.).

Plan: `doc/plans/plan-2026-04-27-09.md`.

## Test plan

- [ ] `cargo build` (stable, default features) — clean.
- [ ] `cargo test --workspace` (stable) — all green (counts
      unchanged from main: 1119 lib + 1481 integration + 31
      doctests).
- [ ] `cargo clippy --all-targets -- -D warnings` (stable) — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `cargo doc --no-deps --features testing --document-private-items`
      with `RUSTDOCFLAGS=-D warnings` — clean.
- [ ] `cargo +nightly test --features f16` — all green.
