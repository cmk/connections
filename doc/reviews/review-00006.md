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

## Local review (2026-04-23)

**Branch:** sprint/proptest-audit
**Commits:** 7 (origin/sprint/file-tree-reorg..HEAD post-follow-ups)
**Reviewer:** Claude (sonnet, independent)

---

### Findings

Tier-1 reviewed the Sprint C delta (888 lines, 6 commits) against
plan + calibration. **Zero must-fix.** Two follow-ups, both
addressed in the subsequent `fix:` commit:

1. **[follow-up] Coverage note for `safe_fine`.** Reviewer observed
   that for large PREC (10¹² on F12F??), the cap shrinks the domain
   to ~1/PREC of i64 range. Mathematically sound (closure follows
   from adjoint, which tests the extreme range via `bounded_fine`)
   but worth documenting. Added a `**Coverage note**` block to the
   `safe_fine` docstring making the tradeoff explicit and pointing
   at `galois_upper`/`galois_lower` as the load-bearing extreme-
   domain coverage.

2. **[follow-up] Silent `i128 → i64` truncation.** `safe_fine_rate`
   and `safe_pico_bounded` cast `NUM as i64` which would truncate
   silently if a future connection had NUM > i64::MAX (not current,
   all NUM values ≤ 9_765_625). Replaced both casts with
   `i64::try_from(num).expect("NUM fits i64")` so the assumption
   documents itself and trips loudly if violated.

### Verified correct (no change needed)

- Cap derivations for all three safe strategies
  (`safe_fine`, `safe_fine_rate`, `safe_pico_bounded`).
- Property predicates match design.md §"Key properties".
- NaN equality correctly uses custom `PartialEq` on
  `ExtendedFloat<f64>` (via `once == twice`) in `float_conn_props!`
  and `prop_assert_eq!` on integer tiers.
- `#[cfg(test)] pub(crate) mod property` gates `proptest` dev-dep
  from public build.
- `proptest.toml` at crate root is picked up by cargo test;
  per-block `ProptestConfig` overrides take precedence (documented
  priority).
- 6-law contract covered across all 44 conns (21 ladder + 2
  float-conn + 15 rate↔rate + 6 pico↔rate).

### Plan Conformance

| Task | Status |
|------|--------|
| T1 property.rs populate | ✓ |
| T2 centralize + rewire | ✓ |
| T3 ladder +closure +idempotent | ✓ (+63) |
| T4 float-conn +idempotent | ✓ (+2) |
| T5 sample +closure +idempotent | ✓ (+63) |
| T6 proptest.toml + review | ✓ |

### Recommendations

**Must fix before push:** None.

**Follow-up:** Already tracked in plan Review and addressed in the
follow-up fix commit.
