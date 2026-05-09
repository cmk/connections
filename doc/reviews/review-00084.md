# review-00084 — Replace 1-ns walk with chunk-bottom solver

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

3. **`doc/reviews/review-00084.md` Conn count:** Summary says "17
   affected Conn consts" but the actual count is 15 (2 TDUR + 2 SDUR
   + 2 HDUR + 9 Epoch). Minor doc error; fix before the MR
   description goes live.

4. **`doc/plans/plan-2026-05-08-05.md` naming errors:** Dependency
   graph T8 references `review-00080.md` (should be `review-00084.md`).
   Scope table lists `F064EUTC` (no such const) where the actual
   constant is `F064EUNX`. Neither affects the code; correct for
   future reference.

5. **`SOLVE_STEP_BOUND` constant duplication:** `SOLVE_STEP_BOUND = 44`
   is defined independently in `kani_proofs/time_walk.rs` and
   `kani_proofs/hifi_walk.rs`. Pull into `kani_proofs/mod.rs` once a
   third file appears.
