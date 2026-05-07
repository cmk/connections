# MR !66 — Plan 44: hifi/epoch.rs §3 GNSS scales (Sprint 3)

## Summary

- Adds twelve GNSS-scale `hifitime::Epoch` Conns to `src/hifi/epoch.rs`
  §3 covering GPST, GST, BDT, and QZSST. Each scale ships an `iso!`
  HDUR Conn, an OFDTNANO-shape `conn_l!` NANO Conn, and a F064DURN-
  shape `conn_l!` F064 Conn — same template as the §1 TAI and §2 UTC
  sections from MR !64.
- Routes BDT through `to_duration_in_time_scale(TimeScale::BDT)`
  rather than `to_bdt_duration()` to dodge a hifitime asymmetry
  (`to_bdt_duration` saturates `HD::MAX + BDT_REF` at the upper bound;
  the other GNSS scales' `to_*_duration` short-circuit). Caught
  during local sprint review by `ebdthdur_laws::roundtrip_ceil` at
  `b = HD::MAX`.
- Wires four new `arb_hifi_{gpst,gst,bdt,qzsst}_nanos_in_range`
  strategies in `src/prop/arb.rs` and threads them through the
  standard ConnL law battery (~80 new tests), plus
  `egpsnano_eq_eqzsnano` and `egpshdur_eq_eqzshdur` proptests
  documenting the GPST/QZSST shared reference.

## Test plan

- [ ] `cargo test --features hifi,testing` — all new proptests + spot
      checks green; 128 tests in `hifi::epoch` pass.
- [ ] `cargo clippy --features hifi,testing --all-targets -- -D warnings`.
- [ ] `RUSTDOCFLAGS=-Dwarnings cargo doc --features hifi,testing,macros
      --no-deps --document-private-items`.
- [ ] `cargo build --no-default-features` — `feature = "hifi"` truly optional.
- [ ] Spot-check end-to-end scenario from the plan
      (`GPST_REF_EPOCH` round-trips through `EGPSF064` ↔ `EGPSNANO` ↔
      `ETAINANO`).

## Local review (2026-05-06)

**Branch:** sprint/hifi-gnss
**Commits:** 1 (origin/main..sprint/hifi-gnss)
**Reviewer:** Claude (sonnet, independent)

---

### Reviewing: commit `ee992c8` — `feat: Add hifi/epoch.rs §3 — GNSS scale Conns`

Files touched: `src/hifi/epoch.rs`, `src/hifi.rs`, `src/prop/arb.rs`, `doc/plans/plan-2026-05-06-07.md`, `doc/reviews/review-00066.md`.

### Commit Hygiene

Single commit, conventional `feat:` prefix, subject under 72 characters. Scope is large (768 lines new in `epoch.rs`) but the 12 Conns share private helpers and must ship together to satisfy the test battery; splitting would leave half the law batteries without their strategies. Atomic at this granularity is correct.

### Code Quality

**Conn-name format compliance.** All 12 names — `EGPSHDUR`, `EGPSNANO`, `EGPSF064`, `EQZSHDUR`, `EQZSNANO`, `EQZSF064`, `EGSTHDUR`, `EGSTNANO`, `EGSTF064`, `EBDTHDUR`, `EBDTNANO`, `EBDTF064` — are exactly 8 ASCII chars in two 4-char halves conforming to `A123` form on both sides. No violations.

**Conn placement.** `Epoch` is more specific than `i128`/`f64`/`HD` under CLAUDE.md's specificity rule; all 12 Conns live in `src/hifi/epoch.rs`. Correct.

**No unsafe code.** No `unsafe` blocks appear in the diff.

**BDT routing.** The `to_duration_in_time_scale(TimeScale::BDT)` detour is applied consistently across `ebdthdur_forward`, `ebdtnano_ceil`, and `epoch_to_bdt_f64`. The `ebdtf064_inner` arm correctly avoids `to_bdt_seconds()` by routing through `epoch_to_bdt_f64`. Consistent with the sprint-close review.

**Doc-to-code mismatch in `EBDTF064` doc comment.** The `crate::conn_l!` doc for `EBDTF064` says "Same shape as `[EGPSF064]` with `to_bdt_seconds` as the comparison frame." But `to_bdt_seconds` is **not** the comparison frame — it's `epoch_to_bdt_f64`, which calls `to_duration_in_time_scale(TimeScale::BDT).to_seconds()` to dodge the saturation bug documented in the §3.4 banner. A maintainer following the doc comment will be pointed at the wrong function.

**Private helper `arb_hifi_scale_nanos_in_range` not factored.** The plan's T1 said "factor the per-scale logic through a single private helper `arb_hifi_scale_nanos_in_range(offset_ns: i128)` to avoid four near-identical bodies." The four strategies in `src/prop/arb.rs` are copy-pasted with no shared helper. Plan non-conformance, low severity.

### Test Coverage

**Property tests — NANO and HDUR.** The full ConnL law battery is present for all four NANO Conns (galois_l, closure_l, kernel_l, monotone_l, idempotent, roundtrip_ceil) using the scale-specific arb strategies. The HDUR `iso_only` law_battery is wired for all four scales. The cross-scale `egpsnano_eq_eqzsnano` and `egpshdur_eq_eqzshdur` proptests are present.

**Property tests — F064.** The F064 ConnL battery (galois_l, closure_l, kernel_l, monotone_l, idempotent_l) is present for all four scales. No `roundtrip_ceil` for F064, consistent with §1–§2 (f64 → Epoch is inherently lossy).

**Missing `e{s}nano_saturation_extremes` for QZSST, GST, BDT.** The plan's Spot checks table requires all four. Only `egpsnano_saturation_extremes` exists. For the other three, neither `upper(i128::MAX) == PosInf` nor `ceil(PosInf) == max_n + 1` is exercised. A typo in `qzsst_max_nanos()` (wrong REF_EPOCH constant) would pass the existing tests.

**`egps_known_offset` — wrong test.** The plan says: `EGPSHDUR.ceil(some_2024_tai_epoch).to_seconds() == that_epoch.to_tai_seconds() - 2_524_953_619`. The implemented `egps_known_offset_at_gpst_inception` instead asserts a constant identity on hifitime that doesn't involve any Conn at all. Zero coverage of `EGPSHDUR`'s correctness at an interior point.

### Plan Conformance

- T1 (arb strategies): 4 strategies delivered; private helper not factored.
- T2–T5 (GNSS Conns): all 12 Conns present, correctly shaped.
- T6 (re-exports + module docs): all 12 constants re-exported; constants table extended; reference-epochs bullet added.
- T7 (property tests + spot checks): law batteries present for all 12 Conns and the 2 cross-scale proptests; saturation_extremes missing for QZSST/GST/BDT; egps_known_offset is the wrong test.

### Risks

`f64::NEG_INFINITY` branch in all four F064 `ceil` returns a TAI-tagged Epoch at `HD::MIN`, inherited from §1. ConnL laws hold (instant-based), but the scale tag is TAI not GPST/etc. Not a regression introduced by this sprint.

No new dependencies. No TODOs or stubs. Existing §1 and §2 Conns strictly additive — no signature or constant changes.

### Recommendations

**Must fix before push:**

1. `EBDTF064` doc comment misstates the comparison frame. Replace "with `to_bdt_seconds` as the comparison frame" with reference to `epoch_to_bdt_f64` and the §3.4 banner.

2. Add `eqzsnano_saturation_extremes`, `egstnano_saturation_extremes`, `ebdtnano_saturation_extremes` mirroring `egpsnano_saturation_extremes`.

3. Replace `egps_known_offset_at_gpst_inception` with an interior-Epoch test that actually invokes `EGPSHDUR`: construct a known TAI Epoch, call `EGPSHDUR.ceil(e).to_seconds()`, assert against `e.to_tai_seconds() - 2_524_953_619.0`.

**Follow-up (future work):**

- Factor the four `arb_hifi_*_nanos_in_range` bodies through the planned private helper to remove copy-paste drift risk.
- Note in each F064 Conn's doc that the NEG_INFINITY arm returns a TAI-tagged Epoch (consistency with the `ETAIF064` precedent).
