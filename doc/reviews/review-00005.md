# MR !5 — File tree reorg + FloatExt → ExtendedFloat

## Summary

- Move domain tier files under `src/conn/`: `float.rs`, `fixed.rs`,
  `sample.rs` via `git mv` (history preserved). Fold old
  `src/float_ext.rs` into `src/conn/float.rs` so the `ExtendedFloat`
  type lives next to the float connections that use it.
- Rename `FloatExt` → `ExtendedFloat` crate-wide (100 occurrences
  across source + docs).
- Collapse `src/order.rs` → `src/lattice.rs` with deferred
  trait stubs for `Join`, `Meet`, `Heyting`, `Coheyting`,
  `Symmetric`, `Boolean` alongside the `Ple` implementation.
- Add empty stubs: `src/property.rs` (populated in Sprint C),
  `src/conn/int.rs`, `src/conn/word.rs`.
- Sync `doc/design.md` §"Module structure" to the actual tree and
  update all `lib.rs` doc links to the new `conn::*` paths.

## Test plan

- `cargo build` — clean.
- `cargo test --workspace` — 377 passed, same as main.
- `cargo clippy --all-targets -- -D warnings` — clean.
- `ls src/` — matches target: `lib.rs`, `conn.rs`, `conn/`,
  `extended.rs`, `lattice.rs`, `property.rs`.
- `ls src/conn/` — `float.rs`, `fixed.rs`, `sample.rs`, `int.rs`,
  `word.rs`.
- `grep -r FloatExt src/` — zero hits.
- `grep -r 'crate::order' src/` — zero hits.
- `grep -r 'crate::float_ext' src/` — zero hits.

Deferred to their own sprints:
- `Join / Meet / Heyting / ...` implementations.
- `src/conn/int.rs` / `word.rs` content.
- `src/property.rs` population (Sprint C).
- `cargo fmt --all` absorbing the rustfmt drift.
