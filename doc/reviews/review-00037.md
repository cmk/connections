# MR !37 — CI cost reduction + walk-perf fix + extremal coverage

## Summary

- Restructures CI: drops the 2.6 GB `target/` from the GitLab cache,
  rekeys to `Cargo.lock`, sets `CARGO_HOME=$CI_PROJECT_DIR/.cargo`,
  scopes `fmt` to no cache and `doc` to MR + `main` only. One
  pipeline now moves ~50 MB of cache traffic vs ~20 GB before.
- Switches the test job to `cargo nextest run --workspace --profile
  ci` (parallelizes individual `#[test]` fns; doctests run
  separately via `cargo test --doc`). New `.config/nextest.toml`
  with a warn-only 180s slow-timeout.
- Fixes a perf bug in `F032DURN.ceil`/`F064DURN.ceil` (mirrored on
  `floor`) where a strict `<` boundary check on `min_secs` failed to
  fast-path the round-trip value `Duration::MIN.as_seconds_f??()`,
  triggering a ~70-second nanosecond-by-nanosecond walk through the
  f-precision plateau. Per-call wall-time on the slow input
  72.7s → 84ns. Suite total 248s → 7.7s.
- Boosts extremal sampling in `src/prop/arb.rs`: float strategies go
  from 4:1/6:1 uniform-to-boundary to 1:2; Extended-wrapped
  strategies go from 1:1:8 to 1:1:3 (floats) / 1:1:2 (time types) /
  1:1:1 (finite-variant enums). New extrema added: `EPSILON`,
  smallest positive subnormal, integer-precision boundary `2^N ± 1`.
  Per-named-extremum sampling rate goes from 0.4–1.8% to >5%.

Plan: `doc/plans/plan-2026-04-27-11.md`.

## Test plan

- [ ] `cargo build` (stable, default features) — clean.
- [ ] `cargo nextest run --workspace --profile ci` — all 2728 green,
      no slow-timeout warnings >180s, total ≤10s on M1.
- [ ] `cargo test --workspace --doc` — all green.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `cargo doc --no-deps --features testing --document-private-items`
      with `RUSTDOCFLAGS=-D warnings` — clean.
- [ ] CI: confirm post-merge pipeline cache transfer ≤100 MB per job
      (vs ~2.6 GB prior) and total wall-time roughly halved.

## Local review (2026-04-28)

**Branch:** sprint/ci-cost
**Commits:** 5 (origin/main..sprint/ci-cost)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Commits #1 and #2 each leave the repo in a slow-but-buildable state.
Commit #1 (`a57eb6e`) introduces cases=8 for `f64_idempotent` and
`f32_idempotent`. Commit #2 (`d88187d`) touches only `.gitlab-ci.yml`
and `.config/nextest.toml`, so `src/time/duration.rs` still has
cases=8. Both compile and `cargo test` passes at those two
checkpoints. The revert to cases=64 lands in commit #3 (`66f0f19`)
alongside the root-cause fix — green both before and after. No commit
leaves a red suite.

Commit subjects follow the project's conventional-commit style. One
minor nit: `perf:` is not listed in CLAUDE.md's subject vocabulary
(`feat:`, `fix:`, `test:`, `doc:`, `task:`, `debt:`). The subject is
clear, but it is technically outside the defined set.

Commits are atomic for their purposes. The CI rewrite bundles T2, T3,
and T4 in one commit with a shared rationale — acceptable given the
tight dependency between cache policy, `CARGO_HOME`, and nextest
needing to consume that cache.

### Code Quality

**`.config/nextest.toml` — stale comment after T5b revert.** The
comment on line 15 reads "Once T5's case-cap on `f32_idempotent` /
`f64_idempotent` lands, we can lower this and add `terminate-after =
3`…" T5's cap was reverted in commit #3. The fix that made the cap
unnecessary was the walk-perf fix, not the cap itself. Leaving the
comment standing implies the 180s threshold is still provisional
pending a future cap, when in fact the suite now runs in 7.7s and the
cap is gone.

**`CARGO_HOME: $CI_PROJECT_DIR/.cargo` — CI variable expansion.**
GitLab expands `$CI_PROJECT_DIR` on the runner before the job starts,
and never contains shell metacharacters. Standard pattern; no
path-traversal risk.

**`curl | tar -xz` without hash verification.** The nextest download
mirrors the existing `cargo-deny` pattern, which also has no hash
verification. Both are pinned by version number and fetched over
HTTPS from the authoritative source. Consistent with project posture
and worth a follow-up for both downloads.

No unsafe code. No new `pub const Conn<_, _>` values introduced, so
naming-format rules are not triggered.

### Test Coverage

**The boundary case `v == min_secs` is not covered by a named
spot-check test.** The fix changes `if v < min_secs` to
`if v <= min_secs` in `F064DURN.ceil` and `F032DURN.ceil` (and
symmetrically for floor). The slow-path trigger is the round-trip
`inner(ceil(NEG_INFINITY))` producing a value equal to `min_secs`,
which then exercises the second `ceil`'s strict-`<` boundary check.

The existing `f64_infinity_arms` test only asserts
`ceil(Extend(f64::NEG_INFINITY)) == Finite(Duration::MIN)` — it stops
after the first `ceil`. No spot-check test constructs
`Extend(Duration::MIN.as_seconds_f64())` and calls `ceil` on it
directly. If this boundary check regresses, the idempotent proptest
will catch it (slowly, via cases=64 plateau-walk timeout), but no
fast spot-check will flag it immediately.

**Strategy rebalance is purely declarative — no sampling-rate
assertions.** The T6 changes increase boundary weights but there are
no tests asserting the new values are ever drawn. Acceptable for
proptest strategies.

**T6 plan item `Duration::seconds_f32(1.0)` exact-widening point is
absent from the diff.** The plan (line 367) cites it as an addition
to `arb_duration_bounded_f32`. The final `arb.rs` does not include
it. Plan-vs-implementation gap; document in Deferred.

**All proptests run at cases=64 at HEAD.** No `#[ignore]` attributes
in the diff.

### Plan Conformance

- T1 (baseline timing snapshot): implemented.
- T2 (drop target/, rekey by Cargo.lock): implemented correctly.
- T3 (fmt cache: [], doc rules): implemented.
- T4 (nextest): implemented — config + test job download + dual
  script.
- T5 (cases=8 cap, reverted): implemented then reverted in #3; plan
  documents the revert and T5b.
- T5b (walk-perf root cause fix): implemented at the four boundary
  comparisons.
- T6 (extremal coverage): partially implemented. Weighting ratios all
  updated. The `Duration::seconds_f32(1.0)` exact-widening point is
  not in the diff (see above).
- T7 (verify, sprint-review, open MR): in progress.

Verification table: all nine F064DURN laws and all nine F032DURN laws
present at cases=64. Green.

### Risks

No TODOs or stubs.

**The floor ordering of guards is asymmetric post-fix.** In
`F064DURN.ceil`: `v > max_secs` (strict), `v <= min_secs` (non-strict
— FIXED). In `F064DURN.floor`: `v >= max_secs` (non-strict — FIXED),
`v < min_secs` (strict). The strict `<` on floor's `min_secs` guard
is correct: floor of a value below the range should return `NegInf`
(not `Finite(MIN)`). The asymmetry is sound. F032DURN mirrors this.
A comment cross-referencing the asymmetric intent would help future
readers distinguish intentional from oversight.

**Downstream consumers of F032DURN/F064DURN.** The change widens the
fast-path coverage. For Galois connections this is a monotone lattice
map — the adjoint pair is unique, so widening which code path reaches
the correct answer cannot change the Galois-correct result. No
downstream breakage risk.

### Recommendations

**Must fix before push:**

1. **Add four spot-check tests for `ceil`/`floor` at the
   `v == min_secs`/`v == max_secs` boundary** in
   `src/time/duration.rs`. These are the exact inputs that triggered
   the walk-perf bug. Without them, a future regression will only be
   caught by the slow proptest battery, not by a fast named test.

2. **Update `.config/nextest.toml` comment** (lines 15–17). The text
   "Once T5's case-cap on `f32_idempotent` / `f64_idempotent` lands…"
   refers to a workaround that was reverted in the same branch.
   Replace with a concrete condition for the threshold or simply
   tighten it now (the suite is 7.7s, so 30s with `terminate-after =
   3` is immediately achievable).

**Follow-up (future work):**

- T6 gap: `Duration::seconds_f32(1.0)` exact-widening point was
  listed in the plan but not added to `arb_duration_bounded_f32`.
  Document in Deferred.
- Hash-verify the nextest binary download. Belongs on the same
  follow-up ticket as cargo-deny.
- Comment the intentional `<` / `<=` asymmetry in floor's min-secs
  guard.
- Add `terminate-after = 3` to `nextest.toml` once the threshold is
  tightened.
