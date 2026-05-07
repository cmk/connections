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

<!-- glab-id: 3323491448 -->
<!-- glab-discussion: 72bf8196aa59a2b5e1275b452636ae8199a6bfa4 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/calendar.rs:113` (2026-05-07 09:47 UTC) [open]

**[follow-up]** The `MONTNZ08` Kani proof (line ~155 in `hifi_calendar.rs`) verifies `n >= 13` implies `PosInf`, but the proptest `montnz08_kernel_l` battery uses `arb_nz_u8_calendar()` which caps at `u8::MAX` — so coverage is fine. However `montnz08_neg_inf_collapses_to_one` has no corresponding `kernel_l` spot assertion checking that `upper(NonZeroU8(1))` returns `Finite(January)` rather than `NegInf`. Without this, the collapse is only tested from the `ceil` direction; a future refactor inverting the NegInf arm in `montnz08_inner` would pass all existing tests while silently breaking the round-trip.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3323491492 -->
<!-- glab-discussion: f718bd6aafad808856bbd6a97d71798b70bd3366 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/kani_proofs/hifi_calendar.rs:57` (2026-05-07 09:47 UTC) [open]

**[must-fix]** The `prove_l!` macro calls `conn_laws::idempotent_l` but the proptest batteries in `hifi/calendar.rs` call `conn_laws::idempotent` (without the `_l` suffix). If the two functions have different signatures or semantics, one set of proofs is testing the wrong law. Verify that `idempotent_l` and `idempotent` are either identical or that each call site is using the correct variant for a `conn_l!`-generated Conn; a mismatch would mean the Kani harnesses silently verify a weaker or different property than the proptests.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3323491554 -->
<!-- glab-discussion: 571b07d4e596bece56f5a699c45d2bf4b6f43a6f -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/calendar.rs:211` (2026-05-07 09:47 UTC) [open]

**[follow-up]** The `arb_u8_calendar` strategy is shared between `MONTU008` and `WKDYU008` property batteries despite containing month-specific boundaries (12, 13) alongside weekday-specific ones (6, 7). The local review already flagged this, but the naming (`arb_u8_calendar`) implies it is month-specific while it is actually a union of both domains' saturation boundaries. A reader wiring up a new Conn battery for a different integer range would silently inherit wrong boundaries; consider splitting into `arb_u8_month` and `arb_u8_weekday`, or adding a comment listing which entries target which Conn.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3323522187 -->
<!-- glab-discussion: 72bf8196aa59a2b5e1275b452636ae8199a6bfa4 -->
#### ↳ cmk (2026-05-07 09:55 UTC) [open]

Added `montnz08_one_recovers_january_not_neg_inf` spot test confirming `MONTNZ08.upper(NonZeroU8(1)) == Finite(January)` — guards against the refactor scenario you described.

<!-- glab-id: 3323522896 -->
<!-- glab-discussion: f718bd6aafad808856bbd6a97d71798b70bd3366 -->
#### ↳ cmk (2026-05-07 09:55 UTC) [open]

False positive — `conn_laws::idempotent` at `src/prop/conn.rs:55` is a backwards-compat alias that calls `idempotent_l(c, a)` directly:

```rust
pub fn idempotent<A: Copy + Eq, B: Copy>(c: &Conn<A, B, L>, a: A) -> bool {
    idempotent_l(c, a)
}
```

The proptest batteries and Kani harnesses test the same property.

<!-- glab-id: 3323523547 -->
<!-- glab-discussion: 571b07d4e596bece56f5a699c45d2bf4b6f43a6f -->
#### ↳ cmk (2026-05-07 09:55 UTC) [open]

Added a clarifying comment on `arb_u8_calendar` explaining its union-of-MONT-and-WKDY scope and warning a future Conn-family contributor not to silently inherit calendar-specific boundaries.
