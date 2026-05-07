# MR !69 — feat: Sprint 5 hifi/calendar.rs (Plan 46)

## Summary

- Add `MONTU008`, `MONTNZ08`, `WKDYU008` — `conn_l!` Conns wrapping
  hifitime's `MonthName` and `Weekday` calendar enums, in a new
  `src/hifi/calendar.rs` file. OFDTNANO shape (single-side `Extended`,
  bare integer rung with saturation arms): the **only** correct shape
  per Lesson 2 — `Extended<src> ↔ Extended<rung>` was the documented
  antipattern.
- Saturate, don't pretend: out-of-domain integers map to
  `Extended::NegInf` / `Extended::PosInf` rather than silently
  defaulting to January (`MonthName::from(0..) → January`) or wrapping
  to Monday (`Weekday::from(7) → Monday` via `rem_euclid`). Callers
  wanting hifitime's wrapping/defaulting use `From<u8>` directly.
- Kani SMT verification: 5 ConnL law batteries × 3 Conns + 4 saturate-
  arm theorems over the full symbolic u8 / NonZeroU8 domain — proves
  the divergence-from-`From<u8>` semantic as a theorem rather than a
  spot test. All pure match-arm logic, expected to verify cleanly
  without T-tier fallback.
- 30 new property tests (5 ConnL laws × 3 Conns + 11 spot checks +
  2 round-trip-all unit tests). All 1376 lib tests pass.

## Test plan

- [ ] `cargo build --features hifi`
- [ ] `cargo test --features hifi,testing`
- [ ] `cargo clippy --all-targets --features hifi,testing -- -D warnings`
- [ ] `cargo doc --features testing --no-deps --document-private-items`
      with `RUSTDOCFLAGS=-D warnings`
- [ ] `cargo build --no-default-features` (feature truly optional)
- [ ] `cargo kani --features hifi --harness '*mont*'` and
      `'*wkdy*'` — 19 SMT proofs verify

## Local review (2026-05-07)

**Branch:** sprint/hifi-calendar
**Commits:** 1 (origin/main..sprint/hifi-calendar)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Single commit, conventional `feat:` prefix, subject is 58 characters
— clean. The plan document and review file carry the context the
body would otherwise hold. No `#[ignore]`d tests.

### Code Quality

All three Conns use the OFDTNANO shape correctly: `Extended` only on
the enum source, bare integer rung. Saturation arms map ceil/inner
correctly; kernel law `ceil(inner(b)) ≤ b` holds for every u8 by
construction.

Naming follows §Conn-name format. `MONT`/`WKDY` are 4-letter ABCD
shapes; `U008` is 1L+3D; `NZ08` is the AB12 shape (this crate's
first AB12 use, explicitly called out in the module doc).

Module placement under `hifi/calendar.rs` is correct per §Conn
placement (hifitime side wins specificity over u8/NonZeroU8 std
primitives).

### Test Coverage

15 ConnL law proptests + 11 spot tests + 2 round-trip-all unit tests.
Boundary-biased helpers (`arb_u8_calendar`, `arb_nz_u8_calendar`)
explicitly include the saturation boundaries (0, 7, 13 for MONTU008
and WKDYU008; 13 for MONTNZ08). Kani harnesses include 4 saturate-
arm theorems (one more than the plan's 3).

### Plan Conformance

T1-T8 all delivered.

### Risks

No TODOs / stubs. No unsafe. The `unreachable!` in `montnz08_ceil`
is a soundness assertion justified by the value range [1, 13].

### Must fix before push

None.

### Follow-up (future work)

**1. Add a NegInf-collapse note to `WKDYU008`'s public doc-comment.**
The `montnz08_ceil` doc explicitly says "Because `NonZeroU8` has no
value below 1, `ceil(NegInf)` collapses onto `NonZeroU8(1)`." The
`WKDYU008` conn_l! doc does not have an equivalent sentence for its
`ceil(NegInf) = 0` collapse. The inline code comment exists but is
not surfaced in rustdoc. Low severity but the asymmetry will confuse
future readers.

**2. Add a `montnz08_round_trip_all_months` unit test** for symmetry
with the other two Conns' exhaustive round-trip checks. The proptest
battery already covers this; a dedicated loop is purely for visual
parity.

**3. `arb_u8_calendar` is shared across MONTU008 and WKDYU008
batteries despite being named for the month family.** Consider
renaming or adding a comment listing which entries target which Conn
boundary. Low priority — correctness is unaffected.
