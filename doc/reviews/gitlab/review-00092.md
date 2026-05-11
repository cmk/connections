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

## Local review (2026-05-09)

**Branch:** sprint/float-fixed-q
**Commits:** 4 (origin/main..sprint/float-fixed-q)
**Reviewer:** Claude (sonnet, independent)

---

### P1.A — Trait-claim audit

1. **`float_fixed!` → ConnK full-triple** — claims both Galois
   directions. Hosts ≤ 32 bits → max/min exactly representable in
   f64 → math exact. **Consistent.**
2. **`float_fixed_l!` → L-only** — claims `ceil ⊣ inner`. For
   hosts where `max_q.to_num::<f64>()` rounds up (`FixedI64<F0>`,
   `FixedI64<F8>`, `FixedU64<F0>`, `FixedU64<F8>`, and the
   `FixedU128` rungs at `F0/F16/F32/F64`), the strict overflow
   guard `v_f64 > max_v_f64` misses the case where `v_f64 ==
   max_v_f64` but `real_v > real_max`. The saturating cast
   produces `Finite(MAX)` while `inner(Finite(MAX))` round-down
   steps below `max_v_f64`, breaking L-Galois at
   `(Extend(max_v_f64), Finite(MAX))`. **Not consistent.**
   Signed 128-bit hosts are unaffected (saturating cast and
   round-down land on the same f64 → chain holds).
3. **`BitsToF64Rd`, `RoundDownFromF64`, `scale_pow2_f64{,_neg}`,
   `round_down_to_f64_u128`, `round_down_f64_to_{f32,f16}`** — all
   consistent with their contracts.

### P1.B — Standard review

- **Commit hygiene:** clean, atomic, conventional. F032 fix is a
  one-line carry-forward.
- **Code quality:** no `unsafe`, sealed traits correctly scoped,
  doc comments thorough.
- **Test coverage:** law batteries cover 1284 generated proptests
  across 136 Conns. Bounded generators (`arb_f32_bounded` |v|≤10,
  `arb_f64_bounded` |v|≤1e9) miss the boundary inputs that would
  trigger the L-Galois violation in audit item 2. No isolated unit
  tests for the new helpers.
- **Risks:** low; main concern is the audit-2 violation.

### P2.A — Test-exception escalation

Plan-02's "Recommendations for follow-up" calls out *Tighter
L-only saturation analysis at the plateau boundary* — the bounded
generators *sidestep* the f64-rounding-of-u128::MAX ULP ambiguity.
The plan acknowledges the gap; the type claim is unrelaxed.
**Promote audit item 2 to must-fix.**

### Plan deviations (P2.B)

- T6 implemented as direct (not composed) — better mathematically;
  plan Review didn't note this. Low stakes.
- 256-case batteries vs plan's 1024 — minor deviation.
- Plan's named spot tests absent — covered by law batteries.

### Must fix before push

**1. Boundary-saturation overflow in `__float_fix_ceil_body!`**
(confidence ~92): replace strict `v_f64 > max_v_f64` flow with a
post-saturating-cast check via `BitsToF64Rd::to_f64_rd(MAX) <
scaled.ceil()`. Affects every L-only Conn over a host where the
max-bit-pattern rounds up to f64 (4 i64-host Conns, 4 u64-host
Conns, 8 u128-host Conns, 0 i128-host Conns, 0 ≤32-bit Conns).
Mirror-issue exists in Phase 1's `__float_ext_int_ceil_body!`;
fix there is symmetric but out of scope for this MR.

### Follow-up (future work)

- Spot tests pinning boundary behavior at `f64::from_bits(2^64)`,
  `f64::from_bits(2^63)`, etc. for each affected Conn.
- Increase law-battery cases from 256 → 1024 to match plan.
- Apply the boundary fix to `__float_ext_int_ceil_body!` in a
  follow-up MR.
- Unbounded f64 generator variant for L-only plateau coverage.
- T10 f16-source Conns (separate MR).
