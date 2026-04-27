# MR !23 — `conn::time` v2 (Phase A): DURNFD09 + OFDT*

## Summary

- Add three new `conn::time` constants:
    - **`DURNFD09`** (`duration.rs`) — `Conn<Duration, Extended<FD09>>`.
      Duration's native nanosecond resolution gives an exact `Finite ⇄
      Finite` bijection; out-of-FD09 Durations saturate the rung to
      `Extended::NegInf` / `PosInf`.
    - **`OFDTNANO`** (`offset.rs`) — `Conn<Extended<OffsetDateTime>,
      i128>`. Unix nanoseconds since `UNIX_EPOCH`, lossless on the
      UTC-representable range. Instants past UTC range (Date::MAX with
      negative offset, etc.) saturate the rung at `±UTC_NS ± 1` markers.
    - **`OFDTSECS`** (`offset.rs`) — `Conn<Extended<OffsetDateTime>,
      i64>`. Sub-second-rounding analog of `TIMESECS`.
- New `src/conn/time/offset.rs` sub-module hosts the OFDT pair plus
  the deferral note about UTCOSECS / Weekday / Month (see Out-of-scope
  below).
- **Widen `arb_duration`** from a `±10⁹ s` uniform slot (0.01% of the
  reachable nanosecond domain) to the full `i64`-second range. Add 14
  new arb strategies for OFDT, UtcOffset, Weekday, Month, FD09, and
  bounded rung values (some used by Phase A; the Weekday/Month/UTC
  ones ship pre-baked for the deferred sprints).
- README family-table row updated; Layout tree shows the new
  `offset.rs` plus the per-domain sub-module breakdown; two new
  Quick-tour examples (`DURNFD09`, `OFDTNANO`) mirrored verbatim into
  the corresponding module-level rustdoc so `cargo test --doc` keeps
  the README and rustdoc in sync.

**Out of scope / deferred** (with concrete blockers):

- `F???DURN` float-Duration bridges (Phase B follow-up MR) — need a
  `shift_duration` helper plus four `widen_f???_to_duration` helpers
  to plug into `def_walk_helpers!`, and a NaN-policy decision for
  `Extend(NaN: f???) ↦ Extended<Duration>::?`.
- `WDAYU008` / `MNTHU008` — `time::Weekday` and `time::Month` don't
  derive `PartialOrd` in v0.3.45; the orphan rule blocks a local
  impl. Future sprint introduces newtype wrappers
  (`WeekdayIso(Weekday)`, `MonthInt(Month)`).
- `UTCOSECS` — `time::UtcOffset::Ord` orders by a packed `as_u32()`
  byte representation (a hash-key implementation detail), not by
  `whole_seconds`. Future sprint introduces `UtcOffsetSecs(UtcOffset)`
  newtype with `PartialOrd` by `whole_seconds`.

## Test plan

- [ ] `cargo test --workspace` — 1757 lib tests pass (was 1626; +131
      new from preorder + Galois batteries on three new conns).
- [ ] `cargo test --doc` — 27 doctests pass (was 24; +3 new — one per
      new constant — plus the OFDTNANO module-level example).
- [ ] `cargo clippy --all-targets --no-deps -- -D warnings` — clean.
- [ ] `cargo doc --no-deps` — no new warnings.
- [ ] Pre-commit hook green on every commit.
- [ ] Manual smoke: `connections::conn::time::OFDTNANO.inner(0)`
      returns `Extended::Finite(OffsetDateTime::UNIX_EPOCH)`;
      `DURNFD09.ceil(Duration::seconds(1))` returns
      `Extended::Finite(FD09(1_000_000_000))`.

## Local review (2026-04-27)

**Branch:** sprint/time-v2
**Commits:** 4 (origin/main..sprint/time-v2)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All four commit subjects use permitted prefixes (`test:`, `feat:`,
`feat:`, `doc:`), are present-tense imperative, and stay within 72
characters. Build-sequence order matches Plan 14: strategies first,
then each conn, then documentation.

### Code Quality — Saturation arms verified Galois-correct

**DURNFD09.** `ceil`/`floor` arms at `Duration::MIN`/`MAX` follow
DURNSECS's pattern. The just-past-`i64`-nanos branches return
`Finite(FD09(i64::MIN/MAX))` for `ceil`/`floor` respectively, matching
`inf{b : d ≤ inner(b)}` and `sup{b : inner(b) ≤ d}` derivations.

**OFDTNANO / OFDTSECS.** Saturation at the **UTC range** rather than
the wider instant range is correct: `OffsetDateTime::from_unix_timestamp_nanos`
only constructs UTC OFDTs in `[Date::MIN UTC, Date::MAX UTC]`. For
`Finite(odt)` with instant past `UTC_MAX`, ceil returns `UTC_MAX + 1`
(smallest rung whose `inner` returns `PosInf`), floor returns `UTC_MAX`
(largest rung whose `inner` is still `Finite`). Symmetric for instants
below `UTC_MIN`. Verified against the Galois adjoint definitions.

**OFDTSECS exact-second-at-max edge.** The `s == max_s && nanosecond
== 0` case returns `max_s` for both ceil and floor. `inner(max_s)` is
`Finite(odt at max_s UTC)`; round-trip equals `odt` under instant-based
PartialOrd. Closure law satisfied.

### `#[cfg(test)]` gates

`ofdt_min_instant`/`ofdt_max_instant` are correctly gated — they're
used only in the test-only `bot`/`top`/`instant_extreme_saturates`
mods. `end_of_day_time()` (used by the public `utc_max_ns/s()`) is
correctly left unguarded.

### Test Coverage

Each new Conn drives the standard battery (`galois_l/r`,
`closure_l/r`, `kernel_l/r`, `monotone_l/r`, `idempotent`,
`roundtrip_ceil/floor`). `floor_le_ceil` and (for OFDTSECS)
`ulp_bound` are correctly omitted with documented reasons matching
DATEJDAY's precedent.

`*_preorder` mods exercise `lattice_{reflexive,transitive,
antisymmetric,bot,top}` against the **instant** extremes for OFDT
(via `ofdt_min_instant`/`ofdt_max_instant`), correctly tracking
OffsetDateTime's instant-based `PartialOrd`.

Spot checks cover: epoch, ±1 ns from epoch, Y2038, UTC-range extremes
round-trip, instant-extreme saturation, `Duration::MIN`/`MAX`,
just-past-`FD09::MAX`. Thorough.

### Plan Conformance

All three conns shipped per Plan 14. `arb_duration` widening per the
plan's Generators section. Three explicit deferrals
(Weekday/Month/UTCOSECS, plus Phase B float bridges) are documented
with concrete blockers in plan + MR description.

### Risks

No high-risk issues. `Duration::new` normalisation is well-established;
the `unreachable!` in `OFDTNANO`/`OFDTSECS::inner` is bounds-guarded;
saturation arms are Galois-correct on all paths verified.

### Recommendations

**Must fix before push:** none remaining (the "13 → 14 strategies"
count discrepancy that the first reviewer pass flagged was corrected
in this same commit).

**Follow-up (future work):**

1. **Cache UTC bounds** — `utc_min_ns()`/`utc_max_ns()`/`utc_min_s()`/
   `utc_max_s()` are recomputed on every `ceil`/`floor`/`inner` call.
   Acceptable now; consider `OnceLock` or compile-time constants in
   Phase B when more OFDT conns land and the pattern solidifies.
2. **Widen `arb_offset_dt`** to include `ofdt_min_instant()` and
   `ofdt_max_instant()` as explicit `Just` arms. Currently the
   instant-extreme OFDTs are exercised only by the `instant_extreme_saturates`
   spot check; adding them to the strategy gives proptest direct
   boundary coverage. Low urgency.
