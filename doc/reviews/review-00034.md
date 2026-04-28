# MR !34 — Pre-publish cleanup: namespace flatten + drop `half`

## Summary

- Drops `bf16` support entirely (`B016`, `F032B016`, `F064B016`,
  `arb_bf16`, `extended_float_bf16`, the bf16 ULP machinery and
  tests). `bf16` has no std stabilization path; downstream crates
  that need bfloat16 can build it directly atop `Conn`.
- Replaces `half::f16` with std `f16` behind a new `f16` cargo
  feature. Stable rustc skips the f16 path entirely; opting into
  `--features f16` requires nightly (`#![cfg_attr(feature = "f16",
  feature(f16))]` per RFC #116909). Removes the `half` crate from
  `[dependencies]`; `half` remains transitively via `fixed`.
- Flattens `src/conn/<sub>/` up one level: `int` (formerly
  `conn::std`, renamed to avoid std-prelude shadowing), `fixed`,
  `float`, `time`. Folds `src/conn/cast.rs` into `src/conn.rs` —
  the cast helpers (`ceiling`, `floor`, `upper`, `lower`,
  `median`, `round`, `truncate`, `interval`, `midpoint`, plus
  `*1`/`*2` lifters) become free functions sibling to `Conn`.
  Crate-root re-exports unchanged (`connections::ceiling` still
  works).
- Inside `float/`, applies the RHS-wins placement rule: `F064F032`
  moves from `f64.rs` to `f32.rs`; `F032F016` / `F064F016` /
  `F016` move into a new feature-gated `f16.rs`; the empty
  `f64.rs` is deleted.
- Picks up the cast cleanup work from main MR !32 (drop
  `maximize` / `minimize`, F064F032 + π doctests, "Behavior on
  edge inputs" section) and re-applies it to the new `conn.rs`.

Plan: `doc/plans/plan-2026-04-27-08.md`.

## Test plan

- [ ] `cargo build` (stable, no features) — clean.
- [ ] `cargo test --workspace` (stable, no features) — all green.
- [ ] `cargo clippy --all-targets -- -D warnings` (stable) — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `cargo doc --no-deps` (stable) — clean.
- [ ] `cargo +nightly build --features f16` — clean.
- [ ] `cargo +nightly test --features f16` — all green
      (including gated f16 tests).
- [ ] `cargo +nightly doc --no-deps --all-features` — clean.
- [ ] `cargo tree -e normal | grep -i half` shows half only via
      fixed (transitive), not as a direct dep.
- [ ] Smoke imports of `connections::int::i16::I008I016`,
      `connections::float::f32::F064F032`, and root-level
      `connections::ceiling` compile.
