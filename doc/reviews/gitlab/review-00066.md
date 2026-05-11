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

<!-- glab-id: 3322850115 -->
<!-- glab-discussion: 0bb32bd4858f3b47ccdc9ef2b929264118f8f87c -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:764` (2026-05-07 06:26 UTC) [open]

**[must-fix]** The `egpsf064_ceil` branch for `f64::NEG_INFINITY` (and the identical branches in `eqzsf064_ceil`, `egstf064_ceil`, `ebdtf064_ceil`) returns `Extended::Finite(Epoch::from_tai_duration(HD::MIN))`, which is a TAI-tagged Epoch, not a GPST/QZSST/GST/BDT-tagged one. The `inner` function for each Conn calls the scale-specific `to_*_seconds()` accessor on that Epoch, so `inner(ceil(ExtendedFloat::Extend(f64::NEG_INFINITY)))` will compute a non-zero seconds value (the TAI-anchored `HD::MIN` converted to GPST seconds ≠ 0 if the scales don't align), violating the ConnL idempotent law `ceil ∘ inner ∘ ceil = ceil`. The local review also flags this but marks it a non-regression; it is structurally identical in all four F064 Conns and should be fixed before merge by returning `Epoch::from_{scale}_duration(HD::MIN)` in the NEG_INFINITY arm.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322850165 -->
<!-- glab-discussion: 6746e56377d52ca2b8565f335b23620604d92770 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:1862` (2026-05-07 06:26 UTC) [open]

**[must-fix]** The plan's Verification table and the local review's Spot-checks section both require `egps_known_offset`: "construct a known TAI Epoch, call `EGPSHDUR.ceil(e).to_seconds()`, assert against `e.to_tai_seconds() - 2_524_953_619.0`". The implemented test `egps_known_offset_at_interior_epoch` uses `SECONDS_GPS_TAI_OFFSET` (an `f64` constant) and calls `.to_tai_seconds()` on the TAI Epoch directly, but never verifies that the `EGPSHDUR.ceil` result equals the expected TAI offset subtraction — it compares `EGPSHDUR.ceil(e).to_seconds()` against `e.to_tai_seconds() - SECONDS_GPS_TAI_OFFSET`, where both sides just compute the same thing, so the assertion would pass even if the Conn were completely wrong. The test should construct `e` as a non-GPST-anchored TAI epoch and independently compute the expected GPST seconds as `e.to_tai_seconds() - 2_524_953_619.0` (the literal constant), not via a hifitime constant that the Conn itself may call internally.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322850217 -->
<!-- glab-discussion: bdd5d88c67fcfb4d003d9a246359342cdf928992 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:1020` (2026-05-07 06:26 UTC) [open]

**[follow-up]** The `ebdthdur_back` function uses `Epoch::from_bdt_duration(d)`, but the §3.4 banner explains that `to_bdt_duration` (the inverse of `from_bdt_duration`) saturates at the upper HD bound due to routing through TAI. If `from_bdt_duration` also routes through TAI internally in hifitime, then `ebdthdur_back(HD::MAX)` may produce an Epoch that, when forwarded through `ebdthdur_forward`, does not recover `HD::MAX` — breaking the iso round-trip in the `upper ∘ ceil` direction. The plan's Review section claims the workaround is applied to the forward path only; the back path should be verified or documented.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322898839 -->
<!-- glab-discussion: 0bb32bd4858f3b47ccdc9ef2b929264118f8f87c -->
#### ↳ cmk (2026-05-07 06:45 UTC) [open]

Push-back: idempotent-l holds. Trace: `ceil(Extend(NEG_INFINITY))` → `Finite(TAI_HD_MIN)` (call it e0); `inner(e0)` → `Extend(e0.to_gpst_seconds())` where `to_gpst_seconds()` routes through `to_time_scale(GPST)`, whose HD subtraction `HD::MIN − GPST_REF.tai` saturates back to `HD::MIN` — so v ≈ `HD::MIN.to_seconds()`, which is ≤ `gpst_min_secs_f64`, so the next `ceil` short-circuits to `Finite(TAI_HD_MIN)` = e0. The `egpsf064_idempotent` proptest exercises this; all 1346 lib tests pass. Epoch's `Eq` is instant-based, so the TAI scale tag is observably indistinguishable from GPST/QZSST/GST/BDT for law purposes — see the local review's Risks section noting this is an inherited §1 design choice.

<!-- glab-id: 3322899023 -->
<!-- glab-discussion: 6746e56377d52ca2b8565f335b23620604d92770 -->
#### ↳ cmk (2026-05-07 06:45 UTC) [open]

Partial: replaced `hifitime::SECONDS_GPS_TAI_OFFSET` with the literal `2_524_953_619.0` per the second half of your suggestion (commit 19aeb0f), giving the assertion test-side independence from the constant `EGPSHDUR.ceil` transitively depends on. Disagree with the first half: a wholly wrong Conn (e.g. one that forgot to subtract `GPST_REF`) would yield LHS ≈ `e.to_tai_seconds() ≈ 3e9` while RHS = `e.to_tai_seconds() − 2_524_953_619 ≈ 4.76e8`, off by ~2.5e9 — orders of magnitude beyond the 1e-6 tolerance. The test does catch a wrong Conn; the literal swap closes the secondary self-reference concern.

<!-- glab-id: 3322899233 -->
<!-- glab-discussion: bdd5d88c67fcfb4d003d9a246359342cdf928992 -->
#### ↳ cmk (2026-05-07 06:45 UTC) [open]

Push-back: `Epoch::from_bdt_duration(d)` is `Self::from_duration(d, TimeScale::BDT)` (`hifitime/src/epoch/initializers.rs:106`) — bare struct construction storing `d` as the BDT-relative duration with the BDT scale tag. No arithmetic, no TAI routing, no saturation. The §3.4 banner's workaround only addresses the `to_*_duration` direction (where the `to_bdt_duration` impl detours through `to_tai_duration`). The `back ∘ forward` round-trip at `HD::MAX` is the failing case that originally surfaced this issue; it's now covered by `ebdthdur_laws::roundtrip_ceil` and passes after the forward-side fix.

<!-- glab-id: 3322935002 -->
<!-- glab-discussion: 0277a237b509ea58fd6c73aeb53d1f44af881a3e -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:764` (2026-05-07 07:00 UTC) [open]

**[follow-up]** The `f64::NEG_INFINITY` arm in `egpsf064_ceil` (and the identical arms in `eqzsf064_ceil`, `egstf064_ceil`, `ebdtf064_ceil`) returns `Extended::Finite(Epoch::from_tai_duration(HD::MIN))`, a TAI-tagged Epoch. The CI reviewer raised this as a `must-fix` idempotent violation; cmk's reply shows the law holds because `inner` routes through `to_*_seconds()` which saturates back to the same value, and `Epoch::Eq` is instant-based. The idempotent proptest passes. However, the doc comments for all four F064 Conns are silent on this TAI-tag behaviour, which the local review also flagged as a follow-up: add a note to each F064 doc (mirroring the `ETAIF064` precedent) that the `NEG_INFINITY` arm yields a TAI-tagged Epoch, so future maintainers don't assume GPST/QZSST/GST/BDT tags throughout.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322935033 -->
<!-- glab-discussion: 3eb45d02543c44c9809808e39fa9e892f88dfa94 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/prop/arb.rs:1310` (2026-05-07 07:00 UTC) [open]

**[follow-up]** Plan T1 specifies factoring the four `arb_hifi_*_nanos_in_range` bodies through a single private helper `arb_hifi_scale_nanos_in_range(offset_ns: i128)` to eliminate copy-paste drift risk. The four functions are identical modulo the `REF_EPOCH` constant; any future change to the boundary strategy (e.g. adding a `max_n - 1` partner) must be applied in four places. Extract the shared body into a private helper as the plan required.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322964184 -->
<!-- glab-discussion: 0277a237b509ea58fd6c73aeb53d1f44af881a3e -->
#### ↳ cmk (2026-05-07 07:10 UTC) [open]

Fixed — added a NEG_INFINITY tag note to each of EGPSF064, EQZSF064, EGSTF064, EBDTF064 (commit 32442a3, round 2). The note explicitly flags that the arm yields a TAI-tagged Epoch and that the ConnL idempotent law still holds under instant-based `Epoch::Eq`.

<!-- glab-id: 3322964388 -->
<!-- glab-discussion: 3eb45d02543c44c9809808e39fa9e892f88dfa94 -->
#### ↳ cmk (2026-05-07 07:11 UTC) [open]

Fixed — extracted the shared body into a private `arb_hifi_scale_nanos_in_range(offset_ns: i128)` helper (commit 32442a3, round 2). The four public strategies are now thin shims; future boundary-strategy changes apply once.
