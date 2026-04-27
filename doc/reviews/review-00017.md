# MR !17 — `conn::time` module (Sprint Time)

## Summary

- Add `conn::time` — five public `Conn` constants over the
  [`time`](https://crates.io/crates/time) crate's `Date` / `Time` /
  `Duration` / `PrimitiveDateTime` types: **`DATEJDAY`** (`Extended<Date>
  ↔ i32` Julian day), **`TIMENANO`** (`Extended<Time> ↔ i64` ns since
  midnight), **`TIMESECS`** (`Extended<Time> ↔ i64` whole seconds with
  sub-second rounding), **`DURNSECS`** (`Duration ↔ Extended<i64>` with
  sign-aware sub-second rounding and ±Inf overflow on the rung), and
  **`PDTMDATE`** (`PrimitiveDateTime ↔ Extended<Date>` with sub-day
  rounding).
- First module to take the `ABCDXWYZ` (4-letter halves) shape from the
  4+4 naming standard. CLAUDE.md lists it as "reserved — no current
  uses"; this module is the first user. Domain-typed sources/targets
  (`Date`, `Time`, `Duration`, `PrimitiveDateTime`) read better as
  letters than tier codes.
- Add `Ple` impls for `Date`, `Time`, `Duration`, `PrimitiveDateTime`,
  each delegating to the type's existing total `Ord`. No NaN patching
  needed.
- Extend `property::arb` with ten new strategies (`arb_date`,
  `arb_time`, `arb_duration`, `arb_primitive_dt`, `arb_extended_date`,
  `arb_extended_time`, `arb_extended_i64`, `arb_jd_in_range`,
  `arb_ns_in_range`, `arb_secs_in_range`), all biased toward
  MIN/MAX/MIDNIGHT/ZERO boundaries.
- Drive the full Galois law battery from `property::laws` for every
  Conn: `galois_l/r`, `closure_l/r`, `kernel_l/r`, `monotone_l/r`,
  `idempotent`. Plus `roundtrip_ceil/floor` (bounded), and
  `ulp_bound` for the three rounding conns. `floor_le_ceil` is
  intentionally omitted — same precedent as `conn::int::U008I016` and
  the other Extended-source conns: saturation makes `inner`
  non-injective, so the law fails at the arms.
- Update `README.md`: new row in the Connection families table, a
  Quick-tour `DURNSECS` block mirrored verbatim into the `conn::time`
  module-level doctest (so `cargo test --doc` keeps README and rustdoc
  in sync), Layout tree includes `conn/time.rs`, and the runtime-deps
  prose now cites both `fixed` and `time`.
- Add `Cargo.toml` dep on `time = "0.3"` (resolves to v0.3.45 under
  the crate's `rust-version = "1.85"` constraint; v0.3.47+ require
  1.88).

## Test plan

- [ ] `cargo test --workspace` — 1628 lib tests pass (1529 baseline +
      99 new: 20 preorder + 79 conn-law / spot).
- [ ] `cargo test --doc` — 18 doctests pass (12 baseline + 6 new: 1
      module-level + 5 per-constant).
- [ ] `cargo clippy --all-targets --no-deps -- -D warnings` — clean.
- [ ] `cargo doc --no-deps` — no new warnings (the four pre-existing
      warnings on `i16`/`i32`/`i64` module-vs-primitive shadowing and
      the `[arb]` link are out of scope).
- [ ] Pre-commit hook green on every commit.
- [ ] Manual smoke from the Quick-tour example: bracketing
      `Duration::seconds(5) + Duration::nanoseconds(1)` via `DURNSECS`
      gives `Extended::Finite(6)` for ceil and `Extended::Finite(5)`
      for floor, and `DURNSECS.inner(Extended::Finite(42)) ==
      Duration::seconds(42)`.

## Local review (2026-04-26)

**Branch:** sprint/time-module
**Commits:** 9 (origin/main..sprint/time-module)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Nine commits, all with correct conventional prefixes (`feat:`, `doc:`). The
dependency graph in the plan (T1 → T2 → T3..T7 → T8) matches the commit
sequence exactly. Each `feat:` commit adds exactly one public constant
with its test mod, leaving the test suite green by the project's rule. No
merge commits are visible. Subjects are under 72 characters. One minor
note: commit `d009fba` ("feat: Scaffold conn::time module + add time crate
dep") bundles `Cargo.toml`, `src/conn/mod.rs`, and the new
`src/conn/time.rs` scaffold — this is appropriate given that all three
are required for the crate to compile.

### Code Quality

No `unsafe` introduced. No `#[allow(clippy::...)]` overrides added.

**Saturation arm correctness — verified correct.**

All five connections with Extended-source or Extended-rung saturation
arms were checked:

- DATEJDAY: `ceil(NegInf) = i32::MIN`, `floor(NegInf) = MIN_JD - 1`,
  `ceil(PosInf) = MAX_JD + 1`, `floor(PosInf) = i32::MAX` — all
  Galois-forced and correct.
- TIMENANO: `floor(NegInf) = -1` (largest b with `inner(b) = NegInf`,
  i.e. b < 0), `ceil(PosInf) = NS_MAX + 1` — correct.
- TIMESECS: same structure as TIMENANO with SECS_MAX — correct.
- DURNSECS: `ceil(Duration::MIN) = NegInf` (forced because
  `inner(NegInf) = Duration::MIN` and no smaller rung exists),
  `floor(Duration::MAX) = PosInf` (dual) — correct.
- PDTMDATE: `ceil(PrimitiveDateTime::MIN) = NegInf` — correct.
  `floor(PrimitiveDateTime::MAX) = PosInf` — the guard is necessary;
  without it the code would return `Finite(Date::MAX)`, which is a
  weaker answer than `PosInf` and would violate the floor law (`floor(p)`
  must be the *largest* b with `inner(b) ≤ p`). Correct.

The "asymmetric edge" pair `ceil(Duration::MIN) = NegInf` vs
`floor(Duration::MIN) = NegInf` and `floor(Duration::MAX) = PosInf` vs
`ceil(Duration::MAX) = PosInf` are documented and confirmed correct by
the `extreme_durations` spot check.

**Stale "Pending" scaffold comment** in `src/conn/time.rs` `//!
# Constants` section was identified by review and has been replaced
with the actual five-constant table before push.

**Dead code / clippy-level.** No dead functions or unused imports are
visible in the diff. `arb_extended_i64` has explicit `Finite(i64::MIN)`
/ `Finite(i64::MAX)` slots in addition to the `any::<i64>()` slot —
this is appropriate given the overflow edge cases in DURNSECS.

### Test Coverage

**Property tests — plan requirements met for all five Conn constants.**

Each Conn drives: `galois_l`, `galois_r`, `closure_l`, `closure_r`,
`kernel_l`, `kernel_r`, `monotone_l`, `monotone_r`, `idempotent`.
`roundtrip_ceil` and `roundtrip_floor` are present with bounded
strategies for all five. `ulp_bound` is present for TIMESECS,
DURNSECS, and PDTMDATE (the three rounding conns). `floor_le_ceil` is
correctly omitted for all five with the same documented precedent as
the Extended-source int conns.

**Spot checks — plan requirements met.**

- DATEJDAY: epoch, MIN/MAX round-trip, saturation extremes — present.
- TIMENANO: midnight, end-of-day, noon, saturation extremes — present.
- TIMESECS: midnight, exact-second, sub-second rounding, end-of-day
  (with sub-second ceil = 86_400), saturation extremes — present.
- DURNSECS: zero, positive sub-second, negative sub-second, both
  extremes, inner saturation — present.
- PDTMDATE: midnight, 1ns past midnight, both extremes, Date::MAX
  with sub-day — present.

**One gap worth tracking: `arb_duration` under-exercises negative
nanoseconds.**

The uniform 8-weight slot in `arb_duration` produces `Duration::new(s,
n)` with `n` drawn from `0..1_000_000_000_i32` — always non-negative. A
`Duration` with negative `s` and `n = 0` has `subsec_nanoseconds() ==
0`, so the `floor`'s `n < 0` branch is only reached via the two explicit
boundary `Just` slots. The spot check
`negative_subsec_rounds_toward_zero` confirms the logic is correct;
this is a coverage density issue, not a correctness issue.

**PDTMDATE `roundtrip_ceil` excludes `Date::MIN` correctly.** The
reasoning in the test comment is sound:
`ceil(inner(Finite(Date::MIN))) = ceil(PrimitiveDateTime::MIN) = NegInf
≠ Finite(Date::MIN)`.

### Plan Conformance

T1 (scaffold), T2 (Ple impls + strategies + preorder laws), T3
(DATEJDAY), T4 (TIMENANO), T5 (TIMESECS), T6 (DURNSECS), T7 (PDTMDATE),
T8 (README + cross-link) — all present.

The plan's `## Deferred` and `## Review` sections were absent in the
first reviewer pass and have been appended before push per CLAUDE.md
step 6.

### Risks

**`time = "0.3"` dependency:** Resolves to v0.3.45 under
`rust-version = "1.85"` (v0.3.47+ require 1.88). Actively maintained
and widely used. No feature flags requested in `Cargo.toml`. No
security surface — no I/O, no network.

**No existing modules are modified** beyond `src/conn/mod.rs` (one
`pub mod time;` line) and `src/property/arb.rs` (new pub functions
appended). Both changes are additive.

**No TODOs or stubs** in the final state.

### Recommendations

**Must fix before push:** none remaining (the two flagged in the
first review pass — stale "Pending" scaffold comment and missing
plan sections — have been addressed).

**Follow-up (future work):**

1. **`arb_duration` negative-nanosecond coverage** — extend the
   8-weight uniform slot in `src/property/arb.rs` to draw from
   `(-1e9..=1e9_i64, -999_999_999..=999_999_999_i32)` (with
   appropriate `Duration::new` sign handling) so the `floor(n < 0)`
   branch receives proportional proptest coverage across the full
   law battery.
2. **`time` dep optionality** — if the crate ever wants to gate
   `conn::time` behind a Cargo feature, the `use time::{...}` at
   the bottom of `src/property/arb.rs` will need a
   `#[cfg(feature = "...")]` guard. Track when feature-gating is
   considered.
