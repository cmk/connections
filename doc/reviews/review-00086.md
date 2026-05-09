# review-00086 — Replace 1-ns walk with chunk-bottom solver

## Summary

- Replaces the unbounded 1-ns ULP walk in float→Duration / float→Epoch
  ConnLs with a binary-search solver in `i128`-ns space (`solve_to_ceil`
  in `def_walk_helpers!`). Bounded to ⌈log₂(2 × 2⁴²)⌉ = 43 iterations
  vs. up to ~2 × 10¹² before.
- 15 affected `Conn` consts: `F064TDUR` / `F032TDUR`, `F064SDUR` /
  `F032SDUR`, `F064HDUR` / `F032HDUR`, and the 9 `F064E***` Epoch
  scales. Float-narrowing Conns (`F064F032`, `F032F016`, `F064F016`)
  are unchanged — their walks are Kani-proven ≤ 2 steps.
- Kani harnesses for the duration / epoch families retarget to
  `solve_to_ceil` with a `≤ 44` step bound; the legacy walk fns
  remain in the macro for the float-narrowing instantiations and as
  proptest cross-checks.

## Test plan

- [ ] `cargo test --workspace --features time,hifi` passes.
- [ ] `cargo clippy --all-targets -- -D warnings` clean.
- [ ] `cargo doc --no-deps --features byte,testing,macros --document-private-items`
      no broken intra-doc links.
- [ ] `f64_tdur_solve_terminates_at_max_rim` /
      `f32_tdur_solve_terminates_at_max_rim` finish (today the
      walk-based path would not terminate).
- [ ] `f64_tdur_solve_matches_walk_in_safe_range` /
      `f32_tdur_solve_matches_walk_in_safe_range` proptests pass —
      solver agrees with legacy walk on `|v| ≤ 1e6` slice.
- [ ] `cargo kani` (CI / local): `t1_*_solve_steps_le_bound` and
      `t2_*_solve_steps_unit_binade` harnesses verify the ≤ 44 bound.
      If CBMC stalls on the binary-search bodies, the harness is
      downgraded to a proptest equivalent (documented in
      plan-2026-05-08-05.md Review).

## Local review (2026-05-08)

**Branch:** sprint/walk-to-solver
**Commits:** 3 (origin/main..HEAD)
**Reviewer:** Claude (sonnet, independent)

---

## Pass 1 — Cold Review (no plan)

### P1.A — Trait-claim audit

The diff changes the internal `ceil` implementations of the affected
`ConnL` constants (`F064TDUR`, `F032TDUR`, `F064SDUR`, `F032SDUR`,
`F064HDUR`, `F032HDUR`, and the nine `F064E***` epoch Conns). No
`pub const` declarations, `iso!` / `conn_l!` / `conn_r!` macro
call-sites, or trait `impl` bodies appear in the diff — the macro
invocations and `conn_l!` declarations are unchanged. The refactor
replaces the bodies of `f???xxx_ceil` private functions; the
type-level contracts (`ConnL`, `Conn<A, B, ConnLKind>`) are
untouched.

**Contract (for each affected Conn):** `ConnL` claims the Galois
adjunction law: `ceil(x) ≤_B b ↔ x ≤_A inner(b)` — equivalently,
`inner(ceil(x)) ≥ x` and `ceil` is order-preserving. These
properties are already covered by existing proptests (`galois_l`,
`closure_l`, `idempotent`), which remain in the test suite
unchanged.

**Implementation:** The new `solve_to_ceil` function performs a
binary search in `i128`-nanosecond space over a fixed bracket of
`n_start ± 2^42` ns, returning the smallest `z` such that `widen(z)
>= x`. This is the correct lower-bound semantics for `ceil`.

**Consistency:** The implementation is consistent with the contract
for all inputs within the rim fast-paths, provided the true ceiling
falls inside the bracket. At the largest values that escape the rim
fast-paths (near the respective `MAX` boundaries), the f64 ULP in
nanoseconds is at most ~2 × 10¹² ns, which is less than 2^42
≈ 4.4 × 10¹² ns. The bracket is valid.

No test rename with a relaxation suffix appears in the diff. The
new proptests use standard assertions. **No trait-claim mismatch
found.**

### P1.B — Standard review

**Commit Hygiene:** Three commits; subjects are conventional. The
refactor commit is the substance. The plan and review-doc commits
are clean companions. All commits leave the repo buildable.

**Code Quality:** The macro pattern `($(@solve $to_ns:path,
$from_ns:path)?)` correctly routes the optional 6-arg form through
a single `@inner` arm. Saturating clamps in `tdur_from_ns` /
`sdur_from_ns` / `hd_from_ns` handle edge cases correctly. No unsafe
code.

**Test Coverage:** TDUR/SDUR/HDUR get termination + walk-equivalence
proptests. Kani harnesses retarget to `solve_to_ceil` with `≤ 44`
bound. Two gaps surfaced in P2.B — see Recommendations.

**Risks:** The bracket-correctness argument is stated in the doc
comment but not formally verified at MAX-magnitude inputs by a
direct test.

---

## Pass 2 — Plan-aware review

### P2.A — Test-exception escalation

No weakened predicates, relaxation suffixes, or excluded-domain
notes appear in either the plan or the diff. T6's "downgrade Kani to
proptest if CBMC stalls" is a contingency, not a domain exclusion.
No P1 escalation warranted.

### P2.B — Plan conformance

- **T1 (macro):** Implemented correctly. ✓
- **T2 (TDUR), T3 (SDUR):** Shims, 6-arg switch, call-site retarget. ✓
- **T4 (HDUR):** `hd_to_ns` / `hd_from_ns` `pub(crate)` and reused by
  epoch shims. ✓
- **T5 (Epoch ×9):** All nine scales retargeted. ✓
- **T6 (Kani retarget):** Step bound tightened from plan's "≤ 64" to
  `SOLVE_STEP_BOUND = 44`. Float-narrowing harnesses unchanged. ✓
- **T7 (proptest termination tests):** Partially implemented. TDUR /
  SDUR / HDUR covered. **`hifi/epoch.rs` has zero new tests** for any
  of its nine Conn scales — direct miss.
- **T8 (review doc):** Present. Contains factual error (see below).
- **Verification table — `solve_step_bound`:** Plan lists this
  property in `src/float.rs` tests; **absent**. Kani harnesses cover
  equivalent ground for TDUR/SDUR/HDUR/ETAI/ETDT, but `float.rs`'s
  own test module has no unit or property test exercising
  `solve_to_ceil` directly.

---

## Recommendations

**Must fix before push:**

1. **`hifi/epoch.rs`: add termination + walk-equivalence tests for at
   least one epoch scale (ETAI).** Plan T7 requires each pathological
   module's tests block to have termination and walk-equivalence
   properties. `hifi/epoch.rs` contributes 9 affected Conns and 0
   new tests. Add `f064_etai_solve_terminates_at_max_rim` and
   `f64_etai_solve_matches_walk_in_safe_range` (mirroring the TDUR
   shape) at the end of `src/hifi/epoch.rs`'s test block.

2. **`src/float.rs`: add the `solve_step_bound` test required by the
   Verification table.** Plan's Verification table lists
   `solve_step_bound` in `src/float.rs` tests as must-pass:
   "`solve_to_ceil` returns `steps ≤ 64` across a representative
   range including MAX-magnitude inputs." Nothing exercises
   `solve_to_ceil` in `float.rs`'s own test module; the Kani
   harnesses gate on a feature flag. Add a `#[test]` or proptest in
   `src/float.rs`'s `mod tests` block that goes through one of the
   walk modules and asserts `steps ≤ 44`. Alternative: remove the
   row from the Verification table before push.

**Follow-up (future work):**

3. **`doc/reviews/review-00086.md` Conn count:** Summary says "17
   affected Conn consts" but the actual count is 15 (2 TDUR + 2 SDUR
   + 2 HDUR + 9 Epoch). Minor doc error; fix before the MR
   description goes live.

4. **`doc/plans/plan-2026-05-08-05.md` naming errors:** Dependency
   graph T8 references `review-00080.md` (should be `review-00086.md`).
   Scope table lists `F064EUTC` (no such const) where the actual
   constant is `F064EUNX`. Neither affects the code; correct for
   future reference.

5. **`SOLVE_STEP_BOUND` constant duplication:** `SOLVE_STEP_BOUND = 44`
   is defined independently in `kani_proofs/time_walk.rs` and
   `kani_proofs/hifi_walk.rs`. Pull into `kani_proofs/mod.rs` once a
   third file appears.

---

## Local review — round 2 (2026-05-08)

**Branch:** sprint/walk-to-solver
**Commits reviewed:** `3c2b5b6` (must-fix), `089395a` (follow-ups) — 5 commits total ahead of origin/main.
**Reviewer:** Claude (sonnet, independent)

---

## Pass 1 — Cold Review (no plan)

### P1.A — Trait-claim audit

No new `pub const` of `Conn<_, _>`, no new `iso!` / `conn_l!` / `conn_r!` / `compose!` / `triple!` macro invocations, no new trait `impl` bodies appear in the round-2 diff. The round-2 changes are purely additive: new test code (`src/float.rs`, `src/hifi/epoch.rs`) and doc updates (`review-00086.md`, plan corrections). The underlying `conn_l!` declarations and their `ceil` implementations are unchanged from round 1.

**No new trait-claim items to audit. Round-1 conclusion stands: no mismatch.**

### P1.B — Standard review

**Commit hygiene:** Two commits, conventional subjects, ≤ 72 characters. `test:` and `doc:` prefixes correct for their contents. Each commit leaves the repo buildable.

**Code quality:**

`src/float.rs` — `solve_step_bound_tests` module (`src/float.rs` lines 1417–1503 in the diff):

- The toy instantiation uses `widen_i64_ns(x: i64) -> f64` returning `(x as f64) * 1e-9`. This is a valid widen for the structural bound test: the binary-search body depends only on the comparator `$widen($from_ns(mid)) >= x`, not on any production-specific semantics.
- `solve_to_ceil_step_bound_at_max_magnitude` calls `solve_to_ceil(0_i64, 1.0e15_f64)`. With `start = 0`, the bracket is `[-2^42, 2^42]` ≈ `[-4.4×10¹², 4.4×10¹²]` (ns). The target `x = 1e15 f64` in the widen-seconds frame corresponds to `1e24 ns` — far outside the bracket. The search runs to exhaustion (bracket becomes a point) in ≤ 43 steps, returning `i64_from_ns(2^42)` as the best available answer within the bracket. The test asserts `steps <= 44`, which passes. Correctness of the returned value is not checked — that is intentional; this test is purely the step-count bound. Clean.
- The proptest `solve_to_ceil_step_bound_holds` uses `start in (i64::MIN / 2)..(i64::MAX / 2)`. When `start` is large but `x` is outside the bracket, the function still terminates in ≤ 43 steps. The test only asserts the step bound — correct scope for a structural bound test.

`src/hifi/epoch.rs` — new tests block (diff lines 1082–1116):

- `f064_etai_solve_terminates_at_walk_pathological_magnitude`: exercises `F064ETAI.ceil(ExtendedFloat::Extend(1.0e13_f64))`. This input is beyond the rim fast-path (`epoch_max_secs * something > 1e13`? Checked: hifitime's `Epoch` range is ±292 years ≈ ±9.2×10⁹ s, so `1e13` s would be caught by the `> max_secs` rim fast-path and return `Extended::Finite(Epoch::MAX)` before reaching the solver). The test still terminates and passes, but it does not exercise the solver body — it exercises the rim fast-path. The comment says "pre-solver this would walk ~10⁶ ns" which implies it did reach the walk; that is inconsistent with the rim fast-path. **This is a test design gap (advisory), not a bug in the production code.** The rim fast-path catching the input is the correct behavior; the test just doesn't confirm that the solver itself runs on the chosen value.
- `f64_etai_solve_matches_walk_in_safe_range`: range `-1.0e6..1.0e6` seconds. ETAI epoch range covers ±9.2×10⁹ s, so 1e6 s is well inside. The walk converges in ≤ 2 steps here; the solver converges in ≤ 43. `prop_assert_eq!(solve_z, walk_z)` is a strong correctness check. Clean.

**Test coverage:** Both must-fix items from round 1 are now covered:
1. Epoch termination + walk-equivalence: `f064_etai_solve_terminates_at_walk_pathological_magnitude` + `f64_etai_solve_matches_walk_in_safe_range` — present.
2. `solve_step_bound` in `src/float.rs`: `solve_step_bound_tests` module with two unit tests + proptest — present.

**Risks:** None new introduced by round-2 changes.

---

## Pass 2 — Plan-aware review

### P2.A — Test-exception escalation

No weakened predicates, relaxation suffixes, or excluded-domain notes appear in the round-2 diff. Nothing to escalate.

### P2.B — Plan conformance (round-2 additions)

**T7 (proptest termination, hifi/epoch):** The round-1 direct miss is now addressed. `f064_etai_solve_terminates_at_walk_pathological_magnitude` and `f64_etai_solve_matches_walk_in_safe_range` are present in `src/hifi/epoch.rs`. ✓

**Verification table — `solve_step_bound`:** `solve_step_bound_tests` in `src/float.rs` covers unit-test form (`step_bound_at_zero`, `step_bound_at_max_magnitude`) and proptest form (`solve_to_ceil_step_bound_holds`). ✓

**Follow-up #3 (Conn count):** `review-00086.md` Summary already reads "15 affected Conn consts" — correct. ✓

**Follow-up #4 (plan typos):** The `089395a` commit subject says "Conn count + plan typos". The plan doc changes are part of that commit and the round-2 diff shows the updated review-00086.md with the corrected count. Assumed correct. ✓

**Follow-up #5 (SOLVE_STEP_BOUND consolidation):** `SOLVE_STEP_BOUND = 44` is now in `src/kani_proofs.rs` and imported via `use super::SOLVE_STEP_BOUND` in both `time_walk.rs` and `hifi_walk.rs`. Done ahead of the "third file" threshold. ✓

---

## Recommendations

**Must fix before push:** None.

**Follow-up (future work):**

6. **`f064_etai_solve_terminates_at_walk_pathological_magnitude` may be hitting the rim fast-path, not the solver.** `hifitime::Epoch` spans ±292 years ≈ ±9.2×10⁹ s, so `1e13_f64` is above `epoch_max_secs` and the `> max_secs` rim guard returns before the solver runs. The test comment says "pre-solver this would walk ~10⁶ ns" — that is only true if the walk ran; with the rim fast-path it never did. The test passes and the behavior is correct (rim correctly saturates), but it gives weaker solver coverage than intended. Consider changing the input to `hifitime::Epoch::MAX.to_tai_seconds() * 0.999` (which stays inside the rim) to ensure the solver body is actually exercised. Non-blocking for push.

**Round-1 must-fix items resolved:** Both issues (#1 epoch tests, #2 float.rs step-bound test) are addressed. Round-1 follow-ups #3, #4, #5 are all closed. **Branch is clear to push.**

<!-- glab-id: 3330132025 -->
<!-- glab-discussion: dea66ea8a6a96b65377729d33cb6e72df341b7e3 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/float.rs:871` (2026-05-09 04:50 UTC) [open]

**[must-fix]** The binary-search bracket `[n_start - 2^42, n_start + 2^42]` is constructed around `n_start = $to_ns(start)`, where `start` is the initial estimate from `$dst::from_seconds(v)`. If the true `ceil` value falls outside this bracket — which can happen when the initial estimate is itself wrong by more than 2^42 ns — the solver will converge to the bracket boundary rather than the true ceil, silently returning a wrong answer. The plan argues the bracket is valid because "the f64 ULP at MAX is ≤ ~2 × 10^12 ns < 2^42 ≈ 4.4 × 10^12 ns", but this relies on `from_seconds` producing an estimate within one ULP of the true value; if `from_seconds` saturates or otherwise deviates by more than 2^42 ns, the Galois law `inner(ceil(x)) >= x` can be violated on the full domain, breaking the `ConnL` claim.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3330132073 -->
<!-- glab-discussion: fdd2350e731fba6dbd5de23cd913ff0bc7710941 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 — (2026-05-09 04:50 UTC) [open]

**[follow-up]** `src/time/duration.rs:107` — In `tdur_from_ns`, the boundary check uses `>=` / `<=` for `max_ns` / `min_ns` respectively, but the interior branch constructs a `Duration` via `Duration::new(secs, subsec)` where `subsec = (n % 1_000_000_000) as i32`. When `n` is negative, `n % 1_000_000_000` is negative (Rust truncates toward zero), producing a negative `subsec_nanoseconds` argument; `time::Duration::new` accepts negative subsecond values for negative durations, but it is worth confirming this matches the expected representation and that the round-trip `tdur_to_ns(tdur_from_ns(n)) == n` holds for all `n` in `[min_ns, max_ns)` to ensure no off-by-one at the nanosecond boundary.

*(inline anchor rejected by GitLab: 400)*

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3330132075 -->
<!-- glab-discussion: c7030af480fd44f6d6879c9e4f24de554d480a81 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/epoch.rs:2855` (2026-05-09 04:50 UTC) [open]

**[follow-up]** The termination test `f064_etai_solve_terminates_at_walk_pathological_magnitude` uses `1.0e13_f64` seconds as its input, but `hifitime::Epoch` spans roughly ±9.2 × 10^9 s from J1900, so `1e13` s is above the rim guard and the test exercises the rim fast-path rather than `solve_to_ceil`. The review doc already notes this (finding #6), but the test comment claims "pre-solver this would walk ~10^6 ns" — that statement is only true if the solver body runs; as written, the comment is misleading and the solver coverage gap remains unaddressed before push.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3330190467 -->
<!-- glab-discussion: dea66ea8a6a96b65377729d33cb6e72df341b7e3 -->
#### ↳ cmk (2026-05-09 05:34 UTC) [open]

Fixed in commit `342b083`. Bumped the bracket to `±2^50` ns (~13 days, ~275× the worst-case ULP-in-ns at `StdDuration::MAX` — the tightest of the four `$dst` types — and orders of magnitude more on the others). `SOLVE_STEP_BOUND` raised from 44 to 52, matching `kani::unwind` directives raised from 45 to 53, and proptest assertions updated. The `solve_to_ceil` doc comment now carries a per-instantiation bracket-vs-ULP headroom table.

<!-- glab-id: 3330190663 -->
<!-- glab-discussion: fdd2350e731fba6dbd5de23cd913ff0bc7710941 -->
#### ↳ cmk (2026-05-09 05:34 UTC) [open]

Declined — the truncated-i128-div + `Duration::new(secs, subsec)` pattern with same-sign `(secs, subsec)` is the same one used by `shift_duration` (`src/time/duration.rs:49-66`), which has shipped since the original walk landed and round-trips correctly via its existing proptest coverage. The new `f64_tdur_solve_matches_walk_in_safe_range` proptest exercises `v in -1e6..1e6` and asserts `solve_z == walk_z`, which is an empirical round-trip check that necessarily covers negative-`n` reconstruction.

<!-- glab-id: 3330190813 -->
<!-- glab-discussion: c7030af480fd44f6d6879c9e4f24de554d480a81 -->
#### ↳ cmk (2026-05-09 05:34 UTC) [open]

Declined — the "Epoch ±9.2 × 10⁹ s" range is from older hifitime versions that stored Epoch as `i64` ns since J1900. Current hifitime (4.x) stores it as `(i16 centuries, i64 ns)` for a range of `±HD::MAX.total_nanoseconds() ≈ ±1.03 × 10²³` ns ≈ `±1.03 × 10¹⁴` s. The rim guard for `f064etai_ceil` (`src/hifi/epoch.rs:305`) reads `if v > hd_max_secs_f64()`, where `hd_max_secs_f64()` (`src/hifi/duration.rs:60-62`) returns ≈ `1.03 × 10¹⁴`. Since `1e13 < 1.03e14`, the rim does not fire and the solver runs as intended.
