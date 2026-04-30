# MR !48 — Plan 31: Codegen-macro consolidation

## Summary

- Adds three new declaration-form macros — `iso!` (degenerate-Galois
  bijection over a `(forward, back)` pair), `prop::conn::law_battery!`
  (9-property test battery with `full`/`l_only`/`r_only`/`iso_only`
  subset arms and optional `cases: N` proptest config), and
  `connections::macros::*` (feature-gated re-exports of the seven
  internal saturating-cast / NonZero macro families) — and migrates
  every existing call site that fits.
- Folds 11 hand-written `pub struct + impl + ViewL + ViewR` blocks
  in `time/duration.rs`, `float/{f32,f16}.rs`, and `addr/ip.rs` into
  the existing `triple!` macro.
- Net: ≈800 LoC removed across `src/` and `tests/`; no behavioral
  change; full test count rose from 1198 → 1230 lib tests because
  `addr::U032IPV4` / `U128IPV6` now run the standard 9-prop battery
  instead of the prior 5-prop hand-rolled subset.

## Test plan

- [x] `cargo test --workspace` — default features, 1198+ tests pass
- [x] `cargo test --workspace --features nix` — Unix-platform Conns
- [x] `cargo test --workspace --features nix,macros,testing` — full
      stable surface
- [x] `cargo test --workspace --no-default-features` — minimal config
- [x] `cargo clippy --all-targets --features nix,macros,testing -D
      warnings` — clean
- [x] `cargo fmt --all -- --check` — clean
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
      --document-private-items --features nix,macros,testing` — no
      broken intra-doc links
- [x] `tests/macros_feature_smoke.rs` — exercises every newly-public
      macro from outside the crate (verifies `$crate::*` path hygiene)
