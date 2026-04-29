# Review 00041 — Plan 23: std-time Duration family inside `time/`

## Summary

- Adds four Galois connections bridging `std::time::Duration` to numeric
  rungs — `STDRU064` (whole seconds, `Extended<u64>`), `STDRU128` (exact
  nanoseconds, `Extended<u128>`), and the float bridges `F064STDR` /
  `F032STDR` — all hosted in `src/time/duration.rs`.
- Reframes `time/` from "the `time` crate's Conns" to "time-domain Conns
  spanning the `time` crate and `std::time`": new `STDR` prefix in the
  module's naming table, four new constants table rows, second
  README-mirrored doctest using `STDRU064` as the unsigned counterpoint
  to `DURNSECS`, and a CLAUDE.md note codifying the merged-module
  pattern that Plan 25 (`int` ⊕ `fixed`) will follow.
- Three lawfulness deviations from the plan, each captured in the plan's
  Review section: source-side `Extended` wrap on STDRU064/128 to avoid
  the Galois-forced `ceil(ZERO) = NegInf` arm; corrected F???STDR
  negative-input arms (`ceil → Finite(ZERO)`, `floor → NegInf`); and a
  rung-bounded proptest strategy for STDRU128's law battery (mirrors
  `OFDTNANO`'s `arb_unix_nanos_in_range`).

## Test plan

- [x] `cargo build` clean.
- [x] `cargo test --workspace` clean (1230 tests; the new STDR* battery
      adds 41 of them).
- [x] `cargo test --doc` clean — the new doctests on `STDRU064`,
      `STDRU128`, `F064STDR`, `F032STDR` and the second README-block
      mirror (`STDRU064` quick tour) all run.
- [x] `cargo clippy --all-targets -- -D warnings` clean.
- [x] `cargo fmt --all -- --check` clean.
- [x] `scripts/check-pii.sh` and `scripts/check_readme_mirror.sh`
      both exit 0.
- [x] STDRU064 / STDRU128 spot-check round-trip (1.5 s ↔ Finite(2) /
      Finite(1) and Finite(1_500_000_000)).
- [x] F064STDR / F032STDR negative-input asymmetry verified by both
      spot tests and a dedicated proptest
      (`f64_stdr_negative_input_ceil_to_zero`).

## Local review (2026-04-28)

**Branch:** sprint/plan-23-stdtime-duration
**Commits:** 3 (origin/main..sprint/plan-23-stdtime-duration)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Three commits, all conventional (`plan:`, `feat:`, `doc:`), subjects under 72 characters, and logically atomic. The `feat:` commit carries both the implementation and the full test battery — correct per the "each commit must leave the repo green" rule. No issues.

### Code Quality

**No unsafe code.** The new functions are pure safe Rust throughout.

**`shift_std_duration` saturation at ZERO.** `saturating_sub` handles the lower bound correctly without an explicit `if new == 0` guard. Consistent with the `shift_duration` pattern for signed `time::Duration`.

**`STDRU128.inner` boundary.** Uses `n >= max_nanos`, so `inner(Finite(MAX.as_nanos()))` takes the saturation arm and returns `Finite(MAX)` rather than the arithmetic path. The bijection document says `floor = ceil = d.as_nanos()` for any `Finite` source, and `inner(ceil(Finite(MAX)))` = `inner(Finite(MAX.as_nanos()))` = `Finite(MAX)`, which round-trips. Correct.

**`F064STDR.ceil` negative-0.0 handling.** The guard is `v <= 0.0`, which catches `-0.0` (IEEE -0.0 == 0.0 is true) and returns `Finite(ZERO)`. That matches the semantics (StdDuration of 0 seconds is the correct ceil of a non-positive input). Correct.

**T5 (`system_time.rs` deferred row).** The plan's original T5 included `system_time.rs (deferred)` in the CLAUDE.md file column. The Deferred section explicitly explains this was held back, and the CLAUDE.md diff does not add it. The note in Deferred is sufficient; no issue.

**One dead-code concern.** `arb_extended_u128` in `src/prop/arb.rs` includes `Just(Extended::Finite(u128::MAX))` — a value that `STDRU128.inner` saturates. The strategy comment says "kept for downstream use", but since the `STDRU128` law battery uses `arb_extended_stdr_nanos_in_range` exclusively, `arb_extended_u128` is exported but never called within this crate. That is fine as stated, but a `#[allow(dead_code)]` annotation or a `pub` + `doc` note confirming "downstream only" would silence future lint warnings if the exported symbol is only used transitively.

### Test Coverage

**Property tests — all four Conns have the full `conn_laws` battery** (galois_l/r, closure_l/r, kernel_l/r, monotone_l/r, idempotent). Strategies are correctly scoped:

- STDRU064 uses `arb_extended_std_duration` / `arb_extended_u64` — full range, appropriate since both sides are bounded.
- STDRU128 uses `arb_extended_stdr_nanos_in_range` for the rung argument in the laws that depend on `inner` being a full inverse — matching the deviation documentation.
- F064STDR / F032STDR use bounded strategies (`secs ≤ 1e9` / `secs ≤ 10`) consistent with the existing `F???DURN` approach to keep the walk budget small.

**`f64_stdr_plateau` property test is missing.** The Verification table (plan line 158) lists `f64_stdr_plateau` as a required property: "`def_walk_helpers!` plateau invariant: ceil-then-floor stays inside the float-precision plateau." No test with this name or this invariant exists in the diff. The `f32_stdr_one_second_brackets_plateau` spot check exercises the bracket property for `F032STDR` at 1 second, but it is a deterministic unit test, not a proptest, and there is no `f64_stdr` equivalent of it at all. Per plan verification rules, this is a gap that must be resolved before push.

**Plan spot check `STDRU064.inner(NegInf) == StdDuration::ZERO` is superseded.** The plan body says `inner(NegInf) = StdDuration::ZERO`; the deviation says the source side was wrapped, so `inner(NegInf) = Extended::NegInf`. The test at line 1303 asserts `Extended::NegInf`. That is the correct post-deviation behavior. The plan body is now inconsistent with the deviation — the plan body's spot check list (line 163: `STDRU064.inner(NegInf) == StdDuration::ZERO`) was not updated to reflect the deviation. The code and test are correct; the plan text has a stale spot check.

**`F064STDR.inner(Finite(StdDuration::from_secs(1))) ≈ F064::from(1.0)` spot check** is present via `f64_stdr_half_second` (which covers `inner(Finite(500 ms)) == 0.5`) and `f64_stdr_zero`, but the exact 1-second inner spot check is not in the test suite. Minor, but the Verification table listed it.

### Plan Conformance

**T1 (STDRU064 / STDRU128):** Fully implemented. Types match the deviation (both sides `Extended`). Spot checks present and correct.

**T2 (F064STDR / F032STDR):** Fully implemented. `shift_std_duration`, `std_duration_to_f64/f32`, `def_walk_helpers!` invocations, both Conns. Doctests show the negative-input asymmetry per the deviation.

**T3 (re-exports + docstring reframe):** `src/time.rs` and `src/time/duration.rs` docstrings updated. Prefix table in `src/time.rs` gains `STDR`. Constants table gains four rows. Second README-mirrored doctest using `STDRU064` present. Re-export at line 580 includes all four constants. Complete.

**T4 (proptest wiring):** `arb_std_duration()` and five associated strategies added to `src/prop/arb.rs`. Full law battery present for all four Conns. Gap: `f64_stdr_plateau` proptest absent (see above).

**T5 (CLAUDE.md):** `time` row updated; explanatory paragraph added. `system_time.rs (deferred)` row **not** added — consistent with the Deferred note. Plan body T5 spec and Deferred note are aligned.

**T6 (README mention):** README line 36 updated with the `std::time::Duration` family. Complete.

**Deviation 1 (Extended source wrap):** Confirmed. `STDRU064: Conn<Extended<StdDuration>, Extended<u64>>` and `STDRU128: Conn<Extended<StdDuration>, Extended<u128>>`. `inner(NegInf) = NegInf`, `inner(PosInf) = PosInf`. `ceil(Finite(ZERO)) = Finite(0)`. Correct and tested.

**Deviation 2 (F???STDR negative-input semantics):** Confirmed. `F064STDR.ceil` returns `Finite(ZERO)` for `v <= 0.0`; `F064STDR.floor` returns `NegInf` for `v < 0.0`. (Note the asymmetric guards: `<= 0.0` for ceil vs `< 0.0` for floor — intentional since `floor(0.0)` should be `Finite(ZERO)`, not `NegInf`.) Dedicated proptest `f64_stdr_negative_input_ceil_to_zero` covers the ceil arm. No symmetric `floor` proptest exists, but the unit test `f64_stdr_negative_input_asymmetric` covers both arms deterministically.

**Deviation 3 (STDRU128 in-range strategy):** Confirmed. `arb_extended_stdr_nanos_in_range` strategy used for all law tests that involve the rung-side argument (`galois_l/r`, `kernel_l/r`, `monotone_r`). `arb_extended_u128` kept in `prop::arb` for downstream. Correct.

### Risks

**`F064STDR.floor` at `v == 0.0`.** The guard `if v < 0.0` (not `<=`) means `floor(Extend(0.0))` falls through to the walk path. `from_secs_f64(0.0) = ZERO`, `ascend_to_floor` starting at ZERO and checking `widen(next) <= 0.0` will immediately return `(ZERO, 0)` since the first `shift(+1, ZERO) = 1ns` and `1ns.as_secs_f64() = 1e-9 > 0.0`. Result: `Finite(ZERO)`. Correct, and covered by `f64_stdr_zero`.

**No new dependencies.** Only `std::time::Duration` which is already in scope.

**No breaking changes to existing public API.** The diff only adds new `pub const`s and re-exports; existing constants and their signatures are unchanged.

---

### Recommendations

**Must fix before push:**

1. **`f64_stdr_plateau` property test is absent.** The Verification table at plan line 158 lists it as a required property: "ceil-then-floor stays inside the float-precision plateau." Add a proptest `f64_stdr_plateau` in `stdr_tests` that, for any `a in extended_float_f64()` where `ceil(a)` is `Finite(c)` and `floor(a)` is `Finite(f)`, asserts `c <= f` and both `inner(Finite(c))` and `inner(Finite(f))` equal `a` (i.e., they round-trip to the same float, confirming they are in the same plateau). The existing `f32_stdr_one_second_brackets_plateau` is a deterministic spot check, not a proptest covering arbitrary inputs, and there is no f64 analogue at all.

**Follow-up (future work):**

2. The plan body spot check `STDRU064.inner(NegInf) == StdDuration::ZERO` (line 163 of the plan) was not updated to reflect the deviation. It now contradicts the implemented behavior (`Extended::NegInf`). Update the plan's Spot checks section to say `STDRU064.inner(Extended::NegInf) == Extended::NegInf` so the plan is self-consistent and not confusing for future readers.

3. The `F064STDR.inner(Finite(StdDuration::from_secs(1))) ≈ F064::from(1.0)` spot check from the Verification table (plan line 168) is missing from the test suite. Add a one-liner unit test `f64_stdr_inner_one_second` asserting this. Minor.

4. `arb_extended_u64` and `arb_extended_u128` are exported from `prop::arb` but not currently used within this crate. They are documented as "for downstream use", which is fine, but adding a brief doc comment noting they are intended for downstream consumers will prevent future `dead_code` lint noise if they become crate-private later.

### Resolutions (pre-push)

- **Must-fix (1):** `f64_stdr_plateau` proptest added in commit `fb44ba4` (`test: Add f64_stdr_plateau proptest + inner_one_second spot`). Seeds a whole-second StdDuration over `[0, 10⁹]`, takes its f64 widening, and asserts ceil and floor walk to the bottom and top of the plateau respectively — both endpoints widen back to exactly `v` and bracket the seed. Battery now passes 61 STDR* tests (was 59). Same commit also adds the `f64_stdr_inner_one_second` spot test from follow-up #3.
- **Follow-up (2):** Plan body spot-check list refreshed in commit `cea4713` (`doc: Refresh plan spot-checks + arb docs post-deviation`). All seven spot-check entries now match the post-deviation behavior, with the source-side wrap and the asymmetric F???STDR negative-input arms called out inline.
- **Follow-up (3):** Folded into commit `fb44ba4` (see Must-fix resolution).
- **Follow-up (4):** Doc-comments added on `arb_extended_u64` / `arb_extended_u128` in commit `cea4713`, noting their intended driving (STDRU064 battery) and downstream-export status respectively.

<!-- glab-id: 3296990775 -->
<!-- glab-discussion: a0fdf2267b08b3f59e223207ab63dbfc86a096f7 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/time/duration.rs:600` (2026-04-29 00:35 UTC) [open]

**[must-fix]** `shift_std_duration` uses `new >= max` (strict: `>=`) as the saturation guard, so `StdDuration::MAX.as_nanos()` itself returns `StdDuration::MAX` via the early-return path — correct. But when `n` is negative the subtraction uses `saturating_sub(n.unsigned_abs() as u128)` on a `u128`, which saturates at 0, then the reconstruction path is taken for any `new < max`. When `n >= 0` and `cur.saturating_add(n as u128)` would produce exactly `max`, the `>= max` guard fires and returns `StdDuration::MAX` — also correct. However, the `def_walk_helpers!` macro drives the shift with `n = 1` to find adjacent Duration values; when `d` is already `StdDuration::MAX` and `n = 1`, `cur.saturating_add(1)` produces `max + 1`, which trips the guard and returns `StdDuration::MAX` — the walk stalls, never advancing, and the ULP loop in `ascend_to_ceil`/`ascend_to_floor` will spin forever (or until the iteration budget). The analogous `shift_duration` for signed `time::Duration` uses `checked_add` and returns `None` to signal the boundary; this function loses that signal by returning the same value as the input when already at `MAX`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3296990794 -->
<!-- glab-discussion: ecea6c99afeed98a31bf77f6fae38491826daf71 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/time/duration.rs:758` (2026-04-29 00:35 UTC) [open]

**[must-fix]** `STDRU128.inner` uses `n >= max_nanos` as the saturation guard, so `inner(Finite(max_nanos))` takes the saturation branch and returns `Finite(StdDuration::MAX)`. The docstring and the `STDRU128` description both say the mapping is a bijection and that `inner` round-trips exactly on the representable range. `ceil(Finite(StdDuration::MAX)) = Finite(max_nanos)`, then `inner(Finite(max_nanos)) = Finite(StdDuration::MAX)` — that part round-trips. But `ceil(inner(Finite(max_nanos)))` also works. The issue is the boundary `n == max_nanos` takes the saturation path (`>= max_nanos`) instead of the arithmetic path, yet `max_nanos / 1_000_000_000` and `max_nanos % 1_000_000_000` would reconstruct `StdDuration::MAX` exactly because `StdDuration::MAX.as_nanos()` is exact. So the saturation guard should be `n > max_nanos` (strict greater-than) to keep the bijection clean at the boundary; as written the bijection claim in the doc is only accidentally correct (both paths yield the same value), but the spot-test `stdru128_inner_saturates_above_max` asserts `inner(Finite(max_nanos + 1)) == Finite(MAX)` — that part is fine. This is a latent correctness / documentation mismatch that will break if `StdDuration::MAX.as_nanos()` is ever not exactly reconstructible by the arithmetic path.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3296990807 -->
<!-- glab-discussion: 7f15bf35a641e71b6d4a81cbc617d1116bdb6026 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/time/duration.rs:815` (2026-04-29 00:35 UTC) [open]

**[must-fix]** `F064STDR.ceil` handles `v == f64::NEG_INFINITY` via the `v <= 0.0` branch (returns `Finite(ZERO)`), but the plan's spot-check table (review-00041.md line 170) and the doctest both state `ceil(Extend(-0.5)) = Finite(ZERO)` — that is consistent. However the `floor` function has `if v == f64::INFINITY` returning `Finite(MAX)` but no explicit guard for `v == f64::NEG_INFINITY`: `-∞` falls through to `v < 0.0` and returns `NegInf`. The spot test `f64_stdr_infinity_arms` asserts `floor(Extend(NEG_INFINITY)) == NegInf` and `ceil(Extend(NEG_INFINITY)) == Finite(ZERO)`. `F064STDR.ceil` reaches the `v <= 0.0` guard via `f64::NEG_INFINITY <= 0.0 == true`, so ceil is correct. But in `floor`, `-∞` is a finite `Extend` value, and `v < 0.0` is true for `-∞`, so `floor` returns `NegInf`. The analogous `F064DURN.floor` returns `NegInf` for `-∞` too, so this is intentional — but the comment in the `floor` body says "Bot arm above already handled ExtendedFloat::Bot itself" while `-∞` is `Extend(NEG_INFINITY)`, not `Bot`. The comment is misleading and will cause confusion when readers check whether the `-∞` case is double-handled.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3297001199 -->
<!-- glab-discussion: a0fdf2267b08b3f59e223207ab63dbfc86a096f7 -->
#### ↳ cmk (2026-04-29 00:39 UTC) [open]

By design — `def_walk_helpers!` uses `if next <= z { return }` as its boundary signal, so a saturating shift at `MAX` (where `next == z`) terminates the loop cleanly. The same contract is documented on `shift_duration`'s rustdoc ("the macro's 'if shift didn't move, terminate' guard fires correctly at the boundaries"). No spin.

<!-- glab-id: 3297001568 -->
<!-- glab-discussion: ecea6c99afeed98a31bf77f6fae38491826daf71 -->
#### ↳ cmk (2026-04-29 00:39 UTC) [open]

Fixed in 70f228d — switched the saturation guard from `n >= max_nanos` to `n > max_nanos` so the boundary value `max_nanos` goes through the arithmetic reconstruction path instead of saturation. Both paths produce `StdDuration::MAX` at exactly that value, so behavior is unchanged, but the `>` makes the bijection-on-the-representable-range claim sharper rather than relying on accidental convergence.

<!-- glab-id: 3297001668 -->
<!-- glab-discussion: 7f15bf35a641e71b6d4a81cbc617d1116bdb6026 -->
#### ↳ cmk (2026-04-29 00:39 UTC) [open]

Fixed in 70f228d — dropped the misleading parenthetical. The branch is solely about `Extend(neg)` / `Extend(-∞)`; `Bot` is matched in the early `match x` arm above and didn't need restating.
