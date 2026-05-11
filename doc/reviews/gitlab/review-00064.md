# MR !64 — `hifi/epoch.rs` §1 TAI baseline + §2 UTC (Sprint 2 of hifitime integration)

## Summary

- Six new Conns under `connections::hifi::epoch` covering
  `hifitime::Epoch` projections in **TAI** (storage-native) and
  **UTC** (leap-second-aware) scales.
- Per-scale shape mirrors the per-Duration shape from Sprint 1:
  `E{xx}HDUR` (Epoch ↔ HDuration, `iso!`) +
  `E{xx}NANO` (Extended<Epoch> ↔ i128, `conn_l!` OFDTNANO shape) +
  `E{xx}F064` (F064 → Extended<Epoch>, `conn_l!` F064DURN shape via
  1ns ULP walks on the underlying TAI Duration).
- **Reference epochs**: ETAI* uses J1900 TAI (hifitime-native);
  EUTCNANO/EUTCF064 use UNIX EPOCH UTC (matches `OFDTNANO`'s
  semantic for callers bridging `time::OffsetDateTime` ↔ `Epoch`).
  EUTCHDUR uses J1900 UTC (UNIX-anchoring would push the iso's
  round-trip boundary outside HD's range).
- Single-side `Extended<…>` throughout, per the project rule.

## Test plan

- [ ] `cargo build --no-default-features` — feature still optional
- [ ] `cargo build --features hifi`
- [ ] `cargo test --features hifi,testing` — all suites green
      (53 hifi::epoch unit tests + 6 epoch doctests)
- [ ] `cargo clippy --features hifi,testing --all-targets -- -D warnings`
- [ ] `RUSTDOCFLAGS=-Dwarnings cargo doc --features hifi,testing,macros
      --no-deps --document-private-items`
- [ ] `cargo fmt --all -- --check`
- [ ] iso laws hold for ETAIHDUR / EUTCHDUR (`iso_only` law_battery)
- [ ] ConnL laws hold for ETAINANO / EUTCNANO / ETAIF064 / EUTCF064
- [ ] EUTCNANO round-trips Y2038 unix nanoseconds exactly

## Local review (2026-05-06)

**Branch:** `sprint/hifi-epoch`
**Commits:** 2 (`origin/main..sprint/hifi-epoch`) — Sprint 1 (`f1d5dc5`) + Sprint 2 (`bccc3a1`)
**Reviewer:** Claude (sonnet, independent, `feature-dev:code-reviewer` agent)
**Scope:** Reviewed `origin/main...HEAD` covering both unpushed sprint commits since they sit stacked on this branch. Findings below apply to both sprints' content.

---

### Commit Hygiene

Both commits follow conventional-commit format (`feat:`) and are scoped to their respective sprints. The subjects are under 72 chars. No unrelated changes are mixed in. The stacking of two MR's worth of work on one branch is acknowledged in the plan.

### Code Quality

- **`default-features = false` is honored.** `Cargo.toml` line 9: `hifitime = { version = "4.3", optional = true, default-features = false }`. The plan review section confirms this compiled cleanly against hifitime 4.3.0.
- **No unsafe code.** Neither new file introduces `unsafe`; the crate-level `#![forbid(unsafe_code)]` carries through.
- **`#[cfg(feature = "hifi")]` gating is consistent.** All new items in `src/prop/arb.rs` are gated. `src/lib.rs` gates `pub mod hifi` correctly.
- **Single-side `Extended` rule holds.** Every Conn has `Extended<…>` on at most one side: HDURNANO/HDURSECS on the source side, F064HDUR/F032HDUR/ETAIF064/EUTCF064 on the target side, ETAIHDUR/EUTCHDUR with no `Extended` at all.
- **No cross-crate Duration bridges crept in.** DURNHDUR/STDRHDUR are absent; no f32 Epoch bridges.
- **Conn-name format is valid.** All ten new names use the ABCD (4+0 digit) shape on the `HDUR`/`ETAI`/`EUTC`/`NANO`/`SECS` sides, and the `F064`/`F032` sides follow the established A123 shape. All names are exactly 8 characters.
- **EUTCNANO inner reorder is correctly implemented.** `src/hifi/epoch.rs` computes `utc_total_ns = n + unix_ref_utc_ns()` in i128 first and then passes the result to `HD::from_total_nanoseconds` — matching the plan's Review description exactly.
- **Asymmetric range derivation is correctly implemented.** `unix_min_nanos()` returns `hd_min_nanos()` (unshifted lower bound) and `unix_max_nanos()` returns `hd_max_nanos() - unix_ref_utc_ns()` (shifted upper bound). `arb_hifi_unix_nanos_in_range` uses the same derivation independently. The two are consistent.

### Test Coverage

- **Property tests present for all Conns.** All six Duration Conns and all six Epoch Conns have galois_l / closure_l / kernel_l / monotone_l / idempotent proptests. Float-bridge Conns use bounded strategies at 64 cases. The iso Conns use `law_battery!` with `iso_only` subset.
- **`roundtrip_ceil` tests:** `hdurnano_roundtrip_ceil` + `arb_hifi_total_nanos_in_range` present. `etainano_roundtrip_ceil` uses `arb_hifi_tai_nanos_in_range` (delegates to the same range). `eutcnano_roundtrip_ceil` uses `arb_hifi_unix_nanos_in_range` and the range derivation matches the implementation.
- **Missing: `hdursecs_roundtrip_ceil`.** See must-fix item 2 below.
- **Edge cases:** Spot-check suite is thorough — zero, ±1 ns, MIN/MAX round-trips, saturation extremes, NaN arms, ±∞ arms, Bot/Top arms, Y2038 cutover, J1900 zero, UNIX epoch, the f64/f32 min-secs fast-path regression guard.
- **No `#[ignore]`s introduced.** Confirmed in plan Review sections and by absence of the attribute in the diff.

### Plan Conformance

- **Sprint 1 (Plan 39):** T1 (Cargo + gate), T2 (arb strategies), T3 (HDURNANO), T4 (HDURSECS), T5 (F064HDUR/F032HDUR), T6 (re-exports) — all implemented. Naming-table omission in `src/lib.rs` documented in the Review section as intentional (matching `time.rs` precedent).
- **Sprint 2 (Plan 40):** T1 (arbs), T2 (ETAIHDUR), T3 (ETAINANO), T4 (ETAIF064), T5 (EUTCHDUR, flipped from UNIX-anchored to J1900-UTC, documented), T6 (EUTCNANO with the inner-reorder fix), T7 (EUTCF064), T8 (re-exports + docs) — all implemented. EUTCHDUR reference-epoch flip correctly documented.
- Both deferred items confirmed absent.

### Risks

- **Leap-second table currency.** EUTCHDUR/EUTCNANO rely on hifitime's compile-time-baked `LatestLeapSeconds`. If a future leap second is added after the pinned hifitime version, the proptests still pass (they don't use wall-clock leap-second data), but callers who store EUTCNANO values across a library upgrade may see silent numeric shifts in the UTC-nanosecond projection for epochs after the new leap second's insertion. Inherent to compile-time leap tables; correctly disclosed in module docs and plan Deferred section. No code change required.
- No path-traversal, command-injection, or unsanitized-input issues — the new code is pure arithmetic with no I/O.
- New dependency `hifitime 4.3` with `default-features = false` is well-established in aerospace/GNSS work; the `optional` gate keeps it out of builds that don't request it.

### Recommendations

**Must fix before push:**

1. **`src/hifi/epoch.rs` EUTCNANO doc comment** — the doc says the offset is `−UNIX_REF_EPOCH.to_tai_duration().total_nanoseconds()` but the implementation uses `to_utc_duration()` (via `unix_ref_utc_ns()`). They differ by the accumulated TAI−UTC offset (~10 leap-second nanoseconds), which is exactly the source of the asymmetry the comment exists to explain. Fix: change `to_tai_duration()` → `to_utc_duration()` in the doc comment. **Confidence: 95.**

2. **`src/hifi/duration.rs` missing `hdursecs_roundtrip_ceil` proptest.** The Sprint 1 plan's Verification table specifies `hdursecs_*` as "(5 + 1)" — five Galois-law tests plus a `roundtrip_ceil` analog to `hdurnano_roundtrip_ceil`. The five laws are present (`hdursecs_galois_l`, `_closure_l`, `_kernel_l`, `_monotone_l`, `_idempotent`) but `hdursecs_roundtrip_ceil` is absent. The galois_l test exercises the path only indirectly. Add an `arb_hifi_total_secs_in_range` strategy (mirror of `arb_hifi_total_nanos_in_range`) and a `hdursecs_roundtrip_ceil` proptest that asserts `ceil(inner(s)) == s` over `[hd_min_secs(), hd_max_secs()]`. **Confidence: 90.**

**Follow-up (future work):**

- Consider adding a spot-check for `eutcnano_saturation_extremes` that also checks `ceil(NegInf)` and `ceil(PosInf)` values. Only `upper(i128::MAX/MIN)` is tested explicitly; the `ceil` direction is covered by `galois_l` proptest-side but explicit spot checks make failures easier to diagnose.


<!-- glab-id: 3322166444 -->
<!-- glab-discussion: 3a2f9304b9e43cc77624f25b471ea3d025043723 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:87` (2026-05-06 23:31 UTC) [open]

**[must-fix]** The `EUTCHDUR` constants table in `src/hifi.rs` (line 68) documents `EUTCHDUR` as `Conn<Epoch, Duration>` with reference "UNIX EPOCH", but the implementation anchors at J1900 UTC (per the Review section's flip). The table entry reads `Epoch ↔ UTC Duration since UNIX EPOCH (leap-second-aware iso)` — this is wrong after the flip. The consequence is that users reading the table will supply UNIX-anchored numeric values to `EUTCHDUR.upper()` and get J1900-relative epochs, silently producing ~70-year errors.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322166625 -->
<!-- glab-discussion: 2e821badcc0bf3356287aeb58a09a91882d37fae -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/prop/arb.rs:1152` (2026-05-06 23:31 UTC) [open]

**[must-fix]** `arb_hifi_total_secs_in_range` casts `HD::MIN.to_seconds()` and `HD::MAX.to_seconds()` with `as i64`, which silently truncates if the `f64` value exceeds `i64::MAX` / `i64::MIN` (saturating cast behavior in Rust). `HD::MAX.to_seconds()` is on the order of `2^63 / 1e9 ≈ 9.2e9` seconds, which fits in `i64`, but `HD::MIN.to_seconds()` is a large negative `f64`; if hifitime ever widens its range, or if the `f64→i64` cast produces `i64::MIN` due to float-representation rounding at the boundary, the range becomes wrong and the `roundtrip_ceil` proptest silently covers a narrower set of values than the impl supports. Use `to_seconds().floor() as i64` paired with a debug-assert that the cast is in range, or derive min/max from `total_nanoseconds() / 1_000_000_000` to stay in integer arithmetic.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322166666 -->
<!-- glab-discussion: f15d8c527285e0e9f29b10941c9afea87ba08f46 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:310` (2026-05-06 23:31 UTC) [open]

**[follow-up]** `eutcf064_ceil` computes `unix_max_secs` and `unix_min_secs` by converting `HD::MAX`/`HD::MIN` TAI Durations through `epoch_to_unix_f64`, which does a UTC leap-second conversion on every call to `ceil`. These are constant values that could be computed once (e.g. via `once_cell`/`LazyLock` or just `const` if hifitime exposes the values) to avoid the repeated conversion overhead in tight loops.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322338056 -->
<!-- glab-discussion: 3a2f9304b9e43cc77624f25b471ea3d025043723 -->
#### ↳ cmk (2026-05-07 01:14 UTC) [open]

Fixed — updated both the family-level reference-epoch note (`src/hifi.rs` lines 51–55) and the constants-table entry (line 68) to spell out the mixed-reference reality: EUTCHDUR uses J1900 UTC, EUTCNANO/EUTCF064 use UNIX EPOCH UTC. The per-Conn doc on EUTCHDUR already explained the J1900 anchor; the family-level docs hadn't caught up.

<!-- glab-id: 3322338350 -->
<!-- glab-discussion: 2e821badcc0bf3356287aeb58a09a91882d37fae -->
#### ↳ cmk (2026-05-07 01:14 UTC) [open]

Fixed — same integer-arithmetic switch as MR !63's hd_min_secs/hd_max_secs fix: `(HD::{MIN,MAX}.total_nanoseconds() / 1_000_000_000) as i64` lands at ±10¹⁴, well inside i64, and the i128 division is exact. The f64 cast was vulnerable to the same precision wall as the other call sites.

<!-- glab-id: 3322338624 -->
<!-- glab-discussion: f15d8c527285e0e9f29b10941c9afea87ba08f46 -->
#### ↳ cmk (2026-05-07 01:14 UTC) [open]

Deferred — accepted as a follow-up. The recomputation is a few-nanosecond hifitime call against the compile-time-baked LatestLeapSeconds table, not a hot-loop concern. If profiling later shows the EUTCF064 ceil path matters, hoisting to a LazyLock is straightforward.

<!-- glab-id: 3322349398 -->
<!-- glab-discussion: ad27e2aa904755385e3709519a21fa367951d08b -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:246` (2026-05-07 01:23 UTC) [open]

**[must-fix]** The `etaif064_ceil` bounds check uses `HD::MAX.to_seconds()` and `HD::MIN.to_seconds()` — the same f64-cast path that was already identified as incorrect in Sprint 1 and fixed in `hd_min_secs`/`hd_max_secs` (see `src/hifi/duration.rs` and MR !63 review). `HD::MAX.to_seconds()` is a large f64 value (~`±1.03×10¹⁴` s) that is outside f64's exact-integer range (`2⁵³ ≈ 9×10¹⁵`), so the cast may round and produce an off-by-one boundary, allowing `v` values that map outside HD's range to slip through the `> max_secs` check. Use `(HD::MAX.total_nanoseconds() / 1_000_000_000) as i64 as f64` (or a helper) consistent with the integer-arithmetic fix already applied elsewhere.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322349418 -->
<!-- glab-discussion: fff8127d627da08c7090319d0a741d419fd6a338 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:305` (2026-05-07 01:23 UTC) [open]

**[must-fix]** Same f64-bounds issue in `eutcf064_ceil`: `unix_max_secs` and `unix_min_secs` are derived by calling `epoch_to_unix_f64(Epoch::from_tai_duration(HD::MAX/MIN))`, which goes through `to_unix_seconds()` — a floating-point path at magnitudes (~`±1.03×10¹⁴` s) well beyond f64's exact-integer range. If the f64 result rounds in the wrong direction, the guard `v > unix_max_secs` can silently miss out-of-range inputs, breaking the saturation contract. Derive the bounds via integer nanosecond arithmetic (paralleling `unix_max_nanos`/`unix_min_nanos`) and convert to seconds after, or reuse the nanosecond bounds with a nanosecond-unit comparison.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322349445 -->
<!-- glab-discussion: 4b463c5a35647a00c9db42174199946748b1d602 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/prop/arb.rs:1238` (2026-05-07 01:23 UTC) [open]

**[must-fix]** The `arb_hifi_unix_nanos_in_range` strategy includes a hardcoded `Just(2_147_483_648_000_000_000_i128)` Y2038 value, but the Y2038 timestamp is approximately `2.15×10¹⁸` ns past the UNIX epoch while `unix_max_nanos()` is `HD::MAX.total_ns() - unix_ref_utc_ns()` which is roughly `HD::MAX.total_ns() ≈ 9.2×10²³` ns — so the hardcoded value is well inside the range and that is fine. However, the lower bound `min_n = HD::MIN.total_nanoseconds()` is a large negative value (~`-9.2×10²³`), while the `unix_min_nanos()` function in `epoch.rs` also returns `hd_min_nanos()` (unshifted). The asymmetry is intentional and documented, but `eutcnano_ceil` for a `Finite` epoch whose stored UTC duration is between `HD::MIN` and `HD::MIN + unix_ref_utc_ns()` will return a value in `[hd_min_nanos(), hd_min_nanos() + unix_ref_utc_ns())` — these are valid `ceil` outputs but `inner` maps them back to `NegInf` (since they are `< unix_min_nanos() = hd_min_nanos()`... wait, they equal `hd_min_nanos()` which IS `unix_min_nanos()`). On re-examination: `inner` accepts `n >= unix_min_nanos() = hd_min_nanos()`, so the round-trip proptest will exercise `n = hd_min_nanos()` correctly. No bug here — withdraw this finding.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322349461 -->
<!-- glab-discussion: 10f86de643601ecbe5ad95435012928260d6e330 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:87` (2026-05-07 01:23 UTC) [open]

**[follow-up]** The EUTCNANO doc comment states `unix_min = HD::MIN.total_ns()` (unshifted lower bound), but a `Finite` epoch whose stored UTC duration is in `[HD::MIN, HD::MIN + unix_ref_utc_ns())` will have `ceil` return a value in that interval, which `inner` then maps back to `NegInf` (since `inner` uses the same `unix_min_nanos() = hd_min_nanos()` threshold). This means epochs very close to `HD::MIN` in UTC space do not round-trip through `ceil ∘ inner ∘ ceil` — `inner(ceil(e))` saturates to `NegInf` for those `e`. The `galois_l` proptest will catch this if `arb_extended_hifi_epoch` ever generates such an epoch, but `arb_hifi_epoch` only produces TAI-scale epochs so the problematic UTC-duration values may never be hit. Document the boundary exclusion explicitly or tighten `unix_min_nanos()` to exclude the problematic zone.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322399696 -->
<!-- glab-discussion: ad27e2aa904755385e3709519a21fa367951d08b -->
#### ↳ cmk (2026-05-07 02:03 UTC) [open]

Fixed — `max_secs` / `min_secs` in `etaif064_ceil` now derive from new `hd_max_secs_f64` / `hd_min_secs_f64` helpers that do `total_nanoseconds() / 1_000_000_000` in i128 first (lands at ±10¹⁴, exact in f64) before the `as f64` cast. Same fix shape as MR !63's `hd_min_secs` migration.

<!-- glab-id: 3322400026 -->
<!-- glab-discussion: fff8127d627da08c7090319d0a741d419fd6a338 -->
#### ↳ cmk (2026-05-07 02:03 UTC) [open]

Fixed — `unix_max_secs` / `unix_min_secs` in `eutcf064_ceil` now derive from new `unix_max_secs_f64` / `unix_min_secs_f64` helpers that work from the existing i128 `unix_{max,min}_nanos()`, then divide and cast. The old `epoch_to_unix_f64(Epoch::from_tai_duration(HD::MAX))` path was doubly lossy — f64 cast of a ±10²³ value plus a UTC-conversion round-trip on top.

<!-- glab-id: 3322400324 -->
<!-- glab-discussion: 4b463c5a35647a00c9db42174199946748b1d602 -->
#### ↳ cmk (2026-05-07 02:03 UTC) [open]

Acknowledged — no action needed. The asymmetric `unix_min_nanos = hd_min_nanos` boundary is intentional and the `inner` check is `n < min_n` (not `<=`), so `n == hd_min_nanos` correctly maps to the Finite branch.

<!-- glab-id: 3322400545 -->
<!-- glab-discussion: 10f86de643601ecbe5ad95435012928260d6e330 -->
#### ↳ cmk (2026-05-07 02:04 UTC) [open]

Push-back — the "maps back to NegInf" claim is incorrect. `eutcnano_inner` uses `if n < min_n`, not `<=`, so `n == hd_min_nanos()` (the saturated `ceil` output) falls through to the Finite branch. Trace for `e = Epoch::from_tai_duration(HD::MIN)` (which `arb_hifi_epoch` already exercises via an explicit `Just`): `ceil(e) = (HD::MIN - UNIX_REF.utc).total_ns()` saturates to `hd_min_nanos()`; then `inner(hd_min_nanos())` computes `utc_total_ns = hd_min_nanos() + unix_ref_utc_ns()`, constructs a valid HD, and returns `Finite(epoch_X)` where `epoch_X.utc_dur = HD::MIN + UNIX_REF.utc`. Closure law `e ≤ inner(ceil(e))` holds because `epoch_X` is a *later* instant than `e` in TAI ordering. All proptests pass for this scenario.

<!-- glab-id: 3322410140 -->
<!-- glab-discussion: 12644a7478b87c9119da226a13f0a8ce763b164b -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:302` (2026-05-07 02:10 UTC) [open]

**[must-fix]** The `eutcf064_ceil` fast-path for `v <= unix_min_secs` returns `Finite(Epoch::from_tai_duration(HD::MIN))`, but `unix_min_secs_f64()` is derived from `unix_min_nanos() / 1_000_000_000 = hd_min_nanos() / 1_000_000_000` — which is the same as `hd_min_secs_f64()`. So `eutcf064_ceil` and `etaif064_ceil` share the same lower-bound fast-path value and return the same epoch for `v <= unix_min_secs`. That is wrong: the UNIX-anchored lower bound in seconds is `hd_min_secs_f64() - unix_ref_utc_secs`, which is a much smaller (more negative) number than `hd_min_secs_f64()`. Any finite f64 in `(unix_min_secs_f64(), hd_min_secs_f64()]` (a ~70-year wide interval in seconds) will be fast-pathed to `HD::MIN` instead of walking to the correct epoch, producing a silent ~70-year error in the saturation boundary.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322410165 -->
<!-- glab-discussion: a07e8729ca9ea04e29397db9e8a835635429f873 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:87` (2026-05-07 02:10 UTC) [open]

**[follow-up]** The `EUTCNANO` doc comment states `unix_min = HD::MIN.total_ns()` (unshifted lower bound) but does not explain what happens to `Finite` epochs whose stored UTC duration lies in `[HD::MIN, HD::MIN + unix_ref_utc_ns())`. For such epochs `ceil` returns a value in that interval; `inner` accepts it (threshold is `< min_n`, not `<=`), constructs `utc_total_ns = n + unix_ref_utc_ns()` which is in `[HD::MIN + unix_ref_utc_ns(), HD::MIN + 2*unix_ref_utc_ns())`, and produces a later epoch — so closure holds but the round-tripped epoch is different from the input. The proptest `arb_extended_hifi_epoch` only produces TAI-scale epochs so this zone may never be exercised; add an explicit spot-check or document the non-identity zone.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322472243 -->
<!-- glab-discussion: 12644a7478b87c9119da226a13f0a8ce763b164b -->
#### ↳ cmk (2026-05-07 02:46 UTC) [open]

Push-back — the fast-path is correct because the inner side's HD-subtraction saturation aligns the plateau boundary with the threshold. Trace for v = `hd_min_secs_f64() - 1e9` (in the bot's "70-year gap"):

- Fast-path returns `Finite(Epoch::from_tai_duration(HD::MIN))`.
- The walk WITHOUT the fast-path produces the same answer: `est = from_unix_seconds(v)` lands at TAI ≈ `HD::MIN + 70y`, then `to_unix_seconds(est)` returns `hd_min_secs_f64` (because `epoch.utc_dur - UNIX_REF.utc` saturates against `HD::MIN`). The descent walk shifts TAI down by 1ns per step until `shift_hd` saturates at `HD::MIN`. Termination value: `Finite(HD::MIN_TAI epoch)`.
- Galois L: `EUTCF064.upper(Finite(HD::MIN_TAI epoch)) = hd_min_secs_f64`, so `f(v) ≤ Finite(HD::MIN_TAI epoch) ⇔ v ≤ hd_min_secs_f64` — satisfied for any v ≤ `hd_min_secs_f64` (which is exactly the fast-path's trigger).

The "70-year span" of input values that the bot describes does map to a single output epoch, but that's NOT a saturation error — it's the genuine plateau of the inner-side projection, since `to_unix_seconds()` for any epoch with TAI ≤ `HD::MIN + UNIX_REF.utc` collapses to the same f64 value via UTC subtraction underflow. The fast-path correctly returns the smallest valid Finite candidate (HD::MIN_TAI) for the entire plateau. Verified by direct test: `EUTCF064.ceil(hd_min_secs_f64 - 1e9) = Finite(HD::MIN_TAI)` and `EUTCF064.upper(Finite(HD::MIN_TAI)) = hd_min_secs_f64`.

Marked as `## Non-identity zone` in the EUTCNANO doc to make this explicit (carrying the round-3 follow-up there).

<!-- glab-id: 3322472368 -->
<!-- glab-discussion: a07e8729ca9ea04e29397db9e8a835635429f873 -->
#### ↳ cmk (2026-05-07 02:47 UTC) [open]

Fixed — added a **Non-identity zone** paragraph to the EUTCNANO doc that spells out exactly the boundary the bot described: epochs in `[HD::MIN, HD::MIN + UNIX_REF.utc.total_ns())` (a ~70-year window at the negative HD extreme) collapse via `ceil` saturation onto `unix_min_nanos`, then `inner` maps that single value to a single epoch at UTC = `HD::MIN + UNIX_REF.utc`. Closure and Galois L still hold, but the round-trip is non-injective there. Same root cause as the EUTCF064 fast-path discussion in the sibling thread (3322410140) — the inner-side HD subtraction is the underlying saturation.

<!-- glab-id: 3322488129 -->
<!-- glab-discussion: 8a7829ce345d34e66af632cc286841cc32e482b7 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:107` (2026-05-07 02:55 UTC) [open]

**[must-fix]** The `unix_min_secs_f64()` helper returns `(unix_min_nanos() / 1_000_000_000) as f64`, and `unix_min_nanos()` returns `hd_min_nanos()` (unshifted). So `unix_min_secs_f64() == hd_min_secs_f64()`. In `eutcf064_ceil`, the `v <= unix_min_secs` fast-path fires at the same threshold as ETAI's lower bound, not at the UNIX-anchored lower bound (`hd_min_secs_f64() - unix_ref_utc_secs`, a ~70-year shift). Any finite `v` in the interval `(unix_min_secs_f64(), hd_min_secs_f64()]` — which is actually `(hd_min_secs_f64(), hd_min_secs_f64()]`, an empty set — wait: since both are identical, the interval is empty and no fast-path error occurs. However, the upper bound has the same problem in reverse: `unix_max_secs_f64()` is derived from `unix_max_nanos() = hd_max_nanos() - unix_ref_utc_ns()`, which IS shifted, so the upper bound is correctly ~70 years less than `hd_max_secs_f64()`. The lower bound is NOT shifted, meaning `eutcf064_ceil` accepts inputs down to `hd_min_secs_f64()` as in-range and walks them, but `epoch_to_unix_f64(est)` for estimates near the HD::MIN TAI epoch will produce unix-seconds near `hd_min_secs_f64() - 70y`, which is below `unix_min_secs_f64()` — causing the ascend walk to diverge. The fix is `unix_min_secs_f64()` should return `(unix_min_nanos() / 1_000_000_000) as f64` where `unix_min_nanos` is `hd_min_nanos() - unix_ref_utc_ns()` (shifted downward), or the fast-path threshold must be `hd_min_secs_f64()` (same as ETAI) rather than a UNIX-shifted value, matching the cmk push-back in the review thread but ensuring the helper name matches its semantics.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322488134 -->
<!-- glab-discussion: 6f887680ea713846ca10bd807106f77b40461f04 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/prop/arb.rs:1238` (2026-05-07 02:55 UTC) [open]

**[follow-up]** The `arb_hifi_unix_nanos_in_range` strategy includes `Just(2_147_483_648_000_000_000_i128)` as a Y2038 boundary value. This is approximately 2.15 × 10¹⁸ ns past the UNIX epoch, which is well within the strategy's `max_n` (~9.2 × 10²³ ns), so it is a valid in-range value. However, the strategy does not include a value near `max_n` minus a small delta (e.g. `max_n - 1`) to probe the upper saturation boundary of `eutcnano_inner`. Adding `Just(max_n - 1)` would improve boundary coverage symmetrically with `Just(min_n)`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322505974 -->
<!-- glab-discussion: 8a7829ce345d34e66af632cc286841cc32e482b7 -->
#### ↳ cmk (2026-05-07 03:11 UTC) [open]

Acknowledged — the bot's own text mid-paragraph (`"wait: since both are identical, the interval is empty and no fast-path error occurs"`) recognizes the lower-bound fast-path is correct. The naming-mismatch concern is fair: `unix_min_secs_f64` does equal `hd_min_secs_f64` despite the name suggesting a UNIX-anchored shift. Added a paragraph above the helpers (`commit 6a8b31e`) spelling this out: the asymmetric `unix_min_nanos = hd_min_nanos` design (motivated by EUTCNANO's ceil saturation) means the f64 fast-path threshold IS `hd_min_secs_f64`, and that's correct because the inner side's HD-subtraction saturation aligns the plateau at that value. Renaming the helpers would cascade into the EUTCNANO doc and the asymmetric-range commentary — keeping the names unified with `unix_{min,max}_nanos` and documenting the equivalence is less churny than splitting them. The "ascend walk diverges" sub-claim doesn't hold either: `epoch_to_unix_f64(HD::MIN_TAI epoch)` returns `hd_min_secs_f64` (verified by the round-3 trace), not `hd_min_secs_f64 - 70y`, so the walk converges normally.

<!-- glab-id: 3322506170 -->
<!-- glab-discussion: 6f887680ea713846ca10bd807106f77b40461f04 -->
#### ↳ cmk (2026-05-07 03:11 UTC) [open]

Fixed — added `Just(max_n - 1)` to `arb_hifi_unix_nanos_in_range`, plus the symmetric `Just(min_n + 1)` partner so both saturation boundaries are probed in the same way as the existing `Just(min_n)` / `Just(max_n)` endpoints. Lands in the same fix commit (`6a8b31e`).

<!-- glab-id: 3322519612 -->
<!-- glab-discussion: 0312aca795551370afdffcda89c6dc759f8cb2d3 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:383` (2026-05-07 03:19 UTC) [open]

**[must-fix]** The `eutcnano_ceil` Finite arm computes `(e.to_duration_in_time_scale(TimeScale::UTC) - UNIX_REF_EPOCH.to_utc_duration()).total_nanoseconds()` — but `hifitime::Duration` subtraction can produce a non-canonical (out-of-range) Duration if the result falls outside `[HD::MIN, HD::MAX]`, meaning `total_nanoseconds()` may silently return a wrapped/saturated value for Finite epochs near the HD extremes. The analogous inner path was fixed by doing the i128 arithmetic first (`utc_total_ns = n + unix_ref_utc_ns()`); `ceil` should use the same pattern: extract `e.to_duration_in_time_scale(UTC).total_nanoseconds()` as an i128, then subtract `unix_ref_utc_ns()` in i128 arithmetic, rather than subtracting Durations and then calling `total_nanoseconds()`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322519618 -->
<!-- glab-discussion: bb16a87b8e9146c7b6c6fedb1b9f9615fa95bc44 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:102` (2026-05-07 03:19 UTC) [open]

**[follow-up]** The comment on `unix_min_secs_f64` and `unix_max_secs_f64` explains at length why `unix_min_secs_f64 == hd_min_secs_f64` is intentional, but the functions are still named asymmetrically (`unix_min` vs `hd_min`) — a future maintainer adding a new `E*F064` bridge may call `unix_min_secs_f64()` and expect a UNIX-shifted lower bound, introducing a silent ~70-year error. Consider either renaming `unix_min_secs_f64` → `hd_min_secs_f64` and documenting the shared threshold in one place, or adding a compile-time `debug_assert_eq!(unix_min_secs_f64(), hd_min_secs_f64())` to make the equality machine-checked.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322551712 -->
<!-- glab-discussion: 273ca607543d70de6f2c6c5b00418e7b22662307 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:364` (2026-05-07 03:44 UTC) [open]

**[must-fix]** The `EUTCNANO` doc comment states the `PosInf` saturation arm returns `unix_max + 1`, but `eutcnano_ceil` returns `max_n + 1` where `max_n = unix_max_nanos()`. That is correct. However, the doc comment on `EUTCNANO` at line ~364 says `ceil(PosInf) = unix_max + 1`, while the `ETAINANO` doc says `ceil(PosInf) = HD::MAX.total_ns() + 1`. These two values differ (`unix_max_nanos() ≠ hd_max_nanos()`), so callers reading the `EUTCNANO` doc who compare against `HD::MAX.total_ns() + 1` as the PosInf sentinel will get a silent off-by-value error. The doc comment should spell out the exact sentinel value (`(HD::MAX.total_ns() − UNIX_REF_EPOCH.to_utc_duration().total_nanoseconds()) + 1`) or point to `unix_max_nanos()` explicitly.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322551737 -->
<!-- glab-discussion: ce511c0e0dd3acd806f0d3e0267275375058286e -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:93` (2026-05-07 03:44 UTC) [open]

**[must-fix]** The comment block for `unix_min_secs_f64` / `unix_max_secs_f64` acknowledges that `unix_min_secs_f64() == hd_min_secs_f64()` despite the name implying a UNIX-shifted lower bound, and argues correctness via the plateau collapse. However, `unix_max_secs_f64()` divides `unix_max_nanos()` (which IS shifted by `unix_ref_utc_ns()`) by `1_000_000_000` — so the upper bound is correctly UNIX-anchored while the lower bound is not. This asymmetry means `eutcf064_ceil` accepts finite `v` values in `(hd_min_secs_f64(), hd_min_secs_f64() + unix_ref_utc_secs)` as "in-range" and passes them to `Epoch::from_unix_seconds(v)`, which constructs an epoch whose underlying TAI duration is below `HD::MIN`, potentially producing an invalid `Epoch`. The plan's own review section (round 4) pushed back on this as a "plateau collapse" but did not verify that `Epoch::from_unix_seconds` saturates safely at that boundary rather than panicking or wrapping. Add a spot-check that `EUTCF064.ceil(ExtendedFloat::Extend(hd_min_secs_f64() - 1.0))` produces `Finite(Epoch::from_tai_duration(HD::MIN))` and that `Epoch::from_unix_seconds` does not panic in that zone.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322551749 -->
<!-- glab-discussion: c956ef657b911c56bef8eb65ebf857dcf790c142 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/prop/arb.rs:1272` (2026-05-07 03:44 UTC) [open]

**[follow-up]** The comment on `Just(min_n + 1)` says it is the "upper-saturation symmetry partner of `max_n - 1`", but `min_n + 1` probes the *lower* saturation boundary (one step above the minimum), not the upper. The comment should read "lower-saturation boundary partner of `max_n - 1`" to correctly describe its role and avoid misleading future readers.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322660878 -->
<!-- glab-discussion: 0312aca795551370afdffcda89c6dc759f8cb2d3 -->
#### ↳ cmk (2026-05-07 04:52 UTC) [open]

Push-back — the bot's proposed i128 arithmetic "fix" would actually break Galois L. Trace for an epoch `e` with stored UTC duration = `HD::MIN + 1ns`:

- Current (HD-subtraction): `(e.utc - UNIX_REF.utc) = HD::MIN + 1ns - 2.2e18 ns`. HD subtraction saturates to `HD::MIN`. `total_nanoseconds() = hd_min_nanos = unix_min_nanos`. Galois L: for any b ≥ unix_min_nanos, e ≤ inner(b) holds (e is at the lower extreme); for b < unix_min_nanos, inner(b) = NegInf, and the law says ceil(e) > b, which is true (ceil(e) = unix_min_nanos > b). ✓

- Bot's i128 arithmetic: `e.utc.total_ns - unix_ref_utc_ns ≈ -1.034e23 + 1 - 2.2e18`, which is **below** unix_min_nanos. Then `inner(that_value) = NegInf`. Closure law `e ≤ inner(ceil(e))` requires e ≤ NegInf — false (e is Finite). Closure FAILS, ConnL invariants broken.

The HD subtraction is not a silent wrap — hifitime saturates at HD::MIN/MAX, and that saturation is the very mechanism aligning ceil's output with the inner threshold. Same root cause as the EUTCF064 fast-path discussion in MR !64 round-3 thread (3322410140) and the "Non-identity zone" doc paragraph on `EUTCNANO`.

<!-- glab-id: 3322660954 -->
<!-- glab-discussion: bb16a87b8e9146c7b6c6fedb1b9f9615fa95bc44 -->
#### ↳ cmk (2026-05-07 04:52 UTC) [open]

Fixed — added `unix_min_secs_f64_equals_hd_min_secs_f64` test (`commit f187ae2`) that asserts the equality at test time, making the invariant machine-checked. Renaming the helper would cascade into the EUTCNANO doc and the asymmetric-range commentary; the test gives the same drift protection without that churn.

<!-- glab-id: 3322661030 -->
<!-- glab-discussion: 273ca607543d70de6f2c6c5b00418e7b22662307 -->
#### ↳ cmk (2026-05-07 04:52 UTC) [open]

Fixed — EUTCNANO doc now spells out `unix_max = HD::MAX.total_ns() − UNIX_REF.utc.total_ns()` with explicit "**distinct** from ETAINANO's `ceil(PosInf) = HD::MAX.total_ns() + 1`" callout. Callers can pick the right sentinel without cross-referencing the impl. (commit `f187ae2`)

<!-- glab-id: 3322661103 -->
<!-- glab-discussion: ce511c0e0dd3acd806f0d3e0267275375058286e -->
#### ↳ cmk (2026-05-07 04:52 UTC) [open]

Fixed — added `eutcf064_below_hd_min_secs_collapses_to_hd_min` spot test (`commit f187ae2`) asserting `EUTCF064.ceil(ExtendedFloat::Extend(hd_min_secs_f64() - 1.0)) == Finite(Epoch::from_tai_duration(HD::MIN))`. The test exercises the ~70-year non-identity zone the previous rounds discussed and confirms `Epoch::from_unix_seconds` saturates safely (no panic). Belt-and-suspenders against regressions of the round-3/4 fast-path discussion.

<!-- glab-id: 3322661196 -->
<!-- glab-discussion: c956ef657b911c56bef8eb65ebf857dcf790c142 -->
#### ↳ cmk (2026-05-07 04:52 UTC) [open]

Fixed — corrected to "lower-saturation boundary partner of `max_n - 1` (MR !64 round-5)". (commit `f187ae2`)
