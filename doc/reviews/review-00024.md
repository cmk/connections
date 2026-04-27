# MR !24 — Tighten unsigned binary-fixed regressions + document ceil bounds

## Summary

- Three small follow-ups from the post-merge review of MR !20
  (unsigned binary-fixed Conns). All advisory — no behavior
  change:
  - **u08 / u16 / u32 / u64 `ceil`:** inline comment in each
    `fix_fix_u<width>!` macro documenting why `res as u<width>`
    is lossless (`res ≤ ⌈T::MAX / 2⌉` since `RATIO ≥ 2`,
    enforced by SHIFT ≥ 1).
  - **u128 `ceil` (`Some(r)` arm):** annotate the `q + 1` step
    with the no-overflow argument (`r ∈ [2, 2^127]`, so
    `q + 1 ≤ 2^127 < u128::MAX`); add a new spot test
    `ceil_at_fine_max_no_overflow` pinning the worst-case input
    (`bits = u128::MAX`, SHIFT=1) explicitly, since the
    proptest battery's 64-cases-per-pair budget makes random
    sampling unlikely to hit this corner.
  - **u64 `spot_u064u000_degenerate`:** expand to cover `ceil`
    and `floor` at the SHIFT=64 endpoint, mirroring `u128`'s
    `degenerate_max_shift`. Pre-fix only `inner` was asserted at
    the Coarse(0) boundary; now all three adjoints walk
    `bits ∈ {0, 1, u64::MAX}`.
- Folds in the post-merge reply-mirror for `review-00020.md`
  (3 advisory bot comments + their replies). The MR !20 review
  file is an ongoing audit trail; appending here keeps it
  single-source.

## Test plan

- [ ] `cargo test --workspace` — **2823 tests** pass (1727 lib,
      including the new `ceil_at_fine_max_no_overflow` spot
      test; 1071 integration; 26 doctests), 0 failed.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
