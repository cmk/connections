# MR !92 — Float → Q-format Conns

## Summary

- 136 new `Float→FixedI/U<U<frac>>` Conns across all 10 host files
  (`fixed::{i,u}{008,016,032,064,128}.rs`), parametrised on the
  source-mantissa-vs-host-bits threshold (full triple where the
  host fits in the source's mantissa, L-only where it doesn't).
- New `float_fixed!` / `float_fixed_l!` macros in `src/fixed.rs`,
  hosted next to `ext_int!` so the fixed-crate dependency stays on
  this side. New `BitsToF64Rd` and `RoundDownFromF64` sealed
  dispatch traits in `src/float.rs` for round-toward-negative-
  infinity casts, plus `scale_pow2_f64` / `_neg` const helpers.
- Carries forward the round-2 `F032` import removal from MR !91
  that missed the merge by one round; rides as the first commit
  on this branch.

## Test plan

- [x] `cargo test --workspace --quiet` — 2856 lib tests pass on
  stable (no `#[ignore]`).
- [x] `cargo build --features f16 --quiet` (nightly) — clean;
  2979 lib tests pass with f16 enabled.
- [x] `cargo clippy --all-targets --quiet -- -D warnings` — clean.
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features
  testing,macros,time --document-private-items` — clean.
- [x] `cargo fmt --all -- --check` — clean.
- [x] Per-Conn law batteries (`law_battery!` with 256 cases each)
  — 1284 generated proptests across the 136 new Conns, all pass.
  Both galois_l and galois_r covered for full-triple Conns;
  galois_l only for L-only via `subset: l_only`.

## Out of scope (deferred to follow-up MR)

- T10 f16-source Conns (62 composed via `F032F016`'s upper
  adjoint, gated on `feature = "f16"`). Trivial follow-up — every
  Conn is a one-line `compose_k!` / `compose_l!` chain. Bounded
  separately to keep this MR's review surface manageable per
  plan-02's split-fallback subsection.

## Notes

Plan: `doc/plans/plan-2026-05-09-02.md`. The plan's Review
section enumerates the design deviations (notably the
`BitsToF64Rd` trait that wasn't in the plan but landed during T9
to fix a u128-host Galois law failure detected by the law
battery).
