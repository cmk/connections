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

