# MR !6 — Proptest audit + shared strategy harness

## Summary

- **Centralize** `arb_f32` / `arb_f64` in `src/property.rs` (gated
  `#[cfg(test)]`). Four duplicated copies collapse to one. Upgrades
  the `conn.rs` variant from a 5-boundary set to the shared
  8-boundary set (adds MIN_POSITIVE, MAX, MIN).
- **Close the six-law gap**: add `prop_closure_l`, `prop_closure_r`,
  `prop_idempotent` to the 21 fixed-ladder pairs, the 2 float↔rung
  pairs (F64F06, F64F12), the 15 rate↔rate pairs, and the 6 pico↔rate
  pairs. **+128 new proptest instances**, test count 377 → 505.
- **Three new round-trip-safe strategies** (`safe_fine(prec)`,
  `safe_fine_rate(num)`, `safe_pico_bounded()`) cap Fine-side inputs
  so `inner(ceil(_))` fits in i64 — the existing `bounded_fine` /
  `pico_bounded` only guard ceil/floor, not the round trip through
  `inner`. Adjoint/monotone tests keep the looser strategies.
- **Add `proptest.toml`**: `cases = 256`, `max_shrink_iters = 8192`.
  Float-conn macro keeps its tighter per-block 512 override.
- `arb_f64_bounded` moves from `conn/fixed.rs` to `property.rs`
  (renamed from `arb_f64_full`). `arb_f32_bounded` intentionally
  not added — no f32 saturation conn today.

## Test plan

- `cargo build` — clean.
- `cargo test --workspace` — 505 passed, up from 377.
- `cargo clippy --all-targets -- -D warnings` — clean.
- `cargo doc --no-deps` — zero warnings.
- `grep -rn 'fn arb_f\(32\|64\)' src/conn/ src/lattice.rs src/conn.rs` — zero matches.
- `rg 'prop_closure_l\|prop_closure_r\|prop_idempotent' src/conn/` — matches span all three macros (`props_for_pair!`, `float_conn_props!`, `props_for_conn!`, `props_for_pico_conn!`).
- `cargo test --release` — completes in under 5 s.

Deferred (tracked in plan Review):
- `arb_f32_bounded` (add when an F32F?? conn appears).
- Property-helper macros (`prop_adjoint!`, `prop_closure!`, …).
- Lifting `arb_extended_*` into `property.rs` (only if another tier needs them).
- `cargo fmt --all` sweep + rust-toolchain bump — good CI-hardening sprint.
