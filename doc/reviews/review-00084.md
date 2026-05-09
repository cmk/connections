# review-00084 — Replace 1-ns walk with chunk-bottom solver

## Summary

- Replaces the unbounded 1-ns ULP walk in float→Duration / float→Epoch
  ConnLs with a binary-search solver in `i128`-ns space (`solve_to_ceil`
  in `def_walk_helpers!`). Bounded to ⌈log₂(2 × 2⁴²)⌉ = 43 iterations
  vs. up to ~2 × 10¹² before.
- 17 affected `Conn` consts: `F064TDUR` / `F032TDUR`, `F064SDUR` /
  `F032SDUR`, `F064HDUR` / `F032HDUR`, and the 9 `F064E***` Epoch
  scales. Float-narrowing Conns (`F064F032`, `F032F016`, `F064F016`)
  are unchanged — their walks are Kani-proven ≤ 2 steps.
- Kani harnesses for the duration / epoch families retarget to
  `solve_to_ceil` with a `≤ 44` step bound; the legacy walk fns
  remain in the macro for the float-narrowing instantiations and as
  proptest cross-checks.

## Test plan

- [ ] `cargo test --workspace --features time,hifi` passes.
- [ ] `cargo clippy --all-targets -- -D warnings` clean.
- [ ] `cargo doc --no-deps --features byte,testing,macros --document-private-items`
      no broken intra-doc links.
- [ ] `f64_tdur_solve_terminates_at_max_rim` /
      `f32_tdur_solve_terminates_at_max_rim` finish (today the
      walk-based path would not terminate).
- [ ] `f64_tdur_solve_matches_walk_in_safe_range` /
      `f32_tdur_solve_matches_walk_in_safe_range` proptests pass —
      solver agrees with legacy walk on `|v| ≤ 1e6` slice.
- [ ] `cargo kani` (CI / local): `t1_*_solve_steps_le_bound` and
      `t2_*_solve_steps_unit_binade` harnesses verify the ≤ 44 bound.
      If CBMC stalls on the binary-search bodies, the harness is
      downgraded to a proptest equivalent (documented in
      plan-2026-05-08-05.md Review).
