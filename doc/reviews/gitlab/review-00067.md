# MR !67 — Kani SMT verification for `time` and `hifi` Conns (Plan 43)

## Summary

- Promote the `def_walk_helpers!` macro's "≤ 2 iterations" comment to a
  Kani theorem on **7 walks**: f64/f32 → `time::Duration` (DURN), f64/f32
  → `std::time::Duration` (STDR), f64/f32 → `hifitime::Duration` (HDUR),
  and f64 → `hifitime::Epoch` in TAI scale (ETAI). Mirrors the
  `F064F032` walk-bound result from MR !62.
- Add Conn-level Galois-law harnesses for the pure-arithmetic time /
  hifi Conns whose closures don't call into calendar or leap-second
  tables: `TIMENANO`, `TIMESECS`, `DURNSECS`, `STDRU064`, `STDRU128`,
  `HDURNANO`, `HDURSECS`, `ETAINANO`, plus the `ETAIHDUR` iso.
- Defer leap-second / calendar Conns (`DATEJDAY`, `PDTMDATE`,
  `OFDTNANO`/`OFDTSECS`, `EUTCNANO`/`EUTCHDUR`/`EUTCF064`) and the
  EUTC walk: their widen / inner closures consult external-crate
  tables that CBMC can't usefully symex.

## Test plan

- [x] `cargo build` — regular build unaffected (`#[cfg(kani)]` /
  `cfg(feature = "hifi")` gates skip every new harness).
- [ ] `cargo kani --harness time_walk::` — 8 walk-bound theorems
  (4 walks × T1+T2 tiers) pass.
- [ ] `cargo kani --harness time_pure::` — 35-harness Conn-level
  battery passes.
- [ ] `cargo kani --features hifi --harness hifi_walk::` — 6
  walk-bound theorems (3 walks × T1+T2) pass.
- [ ] `cargo kani --features hifi --harness hifi_pure::` — 23-harness
  Conn-level battery passes.
- [ ] `cargo kani` (full tree, no features) — existing 1154 + 8 new
  time-walk + 35 time-pure = no regressions.
- [ ] `cargo kani --features hifi` (full hifi tree) — adds 6 hifi-walk
  + 23 hifi-pure on top.
- [ ] `cargo test --workspace` and `cargo clippy --all-targets -- -D
  warnings` — green (verified locally: 1166 tests pass; clippy clean).
- [ ] CI `kani:` job script gets `--features hifi` so the hifi
  harnesses run alongside the rest on tag pushes / scheduled /
  `KANI_RUN` triggers.

## Local review (2026-05-06)

**Branch:** sprint/kani-time-hifi
**Commits:** 1 (origin/main..sprint/kani-time-hifi)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Single commit: `feat: Kani SMT verification for time and hifi Conns
(Plan 43)` — subject is 56 chars, uses `feat:` prefix, present-tense
imperative. Passes the ≤72 char rule. Repo green at HEAD (1166 tests
passing locally).

### Code Quality

All 7 walk-step exposers (`f64_durn_*`, `f32_durn_*`, `f64_stdr_*`,
`f32_stdr_*`, `f64_hdur_*`, `f32_hdur_*`, `f64_etai_*`) faithfully
mirror the corresponding production `f???_ceil` walk-entry: each
calls the same `from_seconds` / `saturating_seconds_*` constructor
and the same `as_seconds_*` / `to_seconds` widen, then dispatches
to `descend_to_ceil` / `ascend_to_ceil` based on the same
`est_widen >= v` check. The `arb_*` helpers (`arb_time`,
`arb_duration`, `arb_std_duration`, `arb_hd`, `arb_epoch`,
`arb_ext_*`) construct symbolic instances via canonical integer
storage with `kani::assume`s that exclude panic-inducing inputs
(out-of-range `Time::from_hms_nano`, sign-incoherent
`Duration::new`, etc.).

The `prove_l!` / `prove_lr!` / `prove_iso!` macros match the
`prove_ext_int!` / `prove_iso!` shape from `ext_int.rs` /
`iso_family.rs`. No new code paths introduced; the macros follow
the same `kani::any` → `assert!(conn_laws::*)` skeleton.

### Test Coverage

8 walk-bound harnesses (4 time walks × T1+T2 tiers); 6 hifi walk
harnesses (3 walks × T1+T2). Conn-level: 35 in `time_pure.rs`
(TIMENANO=5, TIMESECS=5, DURNSECS=10 full-triple, STDRU064=10
full-triple, STDRU128=5), 23 in `hifi_pure.rs` (HDURNANO=5,
HDURSECS=5, ETAINANO=5, ETAIHDUR=8 iso). Total: 72 new harnesses.

Coverage gap (deferred to follow-up): `roundtrip_ceil`,
`roundtrip_floor`, `floor_le_ceil` are listed in the plan §Tier 1
property battery but not invoked by `prove_l!` / `prove_lr!`.
These are the exact-on-rounds and rounding-sandwich properties;
provable for all 9 Conns since none has walks. A follow-up MR
should fold them into the macros.

### Plan Conformance

Tier 0 (full finite non-NaN domain) — local CBMC stalled past 25
min on `f64_durn`'s SAT solver; T0 retreated to T1+T2 throughout.
Plan §Review section (lines 281+) documents the retreat with
diagnostic. Honest deferral.

T2 assertion mismatch fix: plan §Tier 0 table previously read
`steps == 0` for T2; updated to `steps ≤ 1` to match what the
harnesses actually assert (and what the §Review section already
said).

CI deviation: plan §Verification item 4 said "No CI wiring
changes" but `.gitlab-ci.yml` was modified to pass `--features
hifi`. Plan §Review now documents this as a justified emergent
requirement (the hifi gating necessitates `--features hifi` or
the harnesses silently skip).

All 7 in-scope walks and all 9 Tier-1 Conns are represented.

### Risks

- `#[cfg(kani)]`-gated exposers do not leak into `cargo test` /
  `cargo build` (verified: cargo test --lib green, 1166 passing).
- `hifi_walk` / `hifi_pure` modules behind `#[cfg(feature = "hifi")]`
  in `kani_proofs.rs`; default build (no features) excludes them.
- No TODOs or stubs introduced.
- No new runtime dependencies.
- Local kani validation killed mid-sweep (time-crate symex per
  Conn-level harness ≈ minutes; full sweep ≈ tens of minutes).
  CI's `kani:` job is the canonical verdict; if any harness stalls,
  follow-up MR will drop to T1 input bounds.

### Recommendations

**Must fix before push:** none (the two findings from the reviewer
agent — plan T2 row stale, CI deviation undocumented — are now
fixed in this commit's amended state).

**Follow-up (future work):**
- Add `roundtrip_ceil`/`roundtrip_floor`/`floor_le_ceil` invocations
  to `prove_l!` / `prove_lr!` macros so the full Tier 1 property
  battery from the plan is exercised on all 9 Conns.
- If T1/T2 walk harnesses pass cleanly in CI, attempt a more
  aggressive T0 budget (e.g., `cargo kani --solver minisat` or
  per-harness `--default-unwind 4` retry) to upgrade the bound
  from `≤ 1` (T1/T2) to `≤ 2` (T0) on the well-behaved
  non-saturation domain.

<!-- glab-id: 3322871863 -->
<!-- glab-discussion: b56e888732e36b1b9789f0c08724c836f170ca5d -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/time/duration.rs:848` (2026-05-07 06:35 UTC) [open]

**[must-fix]** The `f64_stdr_ceil_walk_steps_for_proof` exposer calls `StdDuration::from_secs_f64(v)` which **panics** when `v` is negative (std's implementation checks `v >= 0.0`). The corresponding harness in `time_walk.rs` does apply `kani::assume(v > 0.0 …)` for `stdr`, but the f32 variant (`t1_f32_stdr_walk_steps_le_1`) applies the same assume, while the T2 `stdr` harnesses constrain `v ∈ [1.0, 2.0)` — those are safe. However, the doc-comment on the exposer says it 'deliberately omits production fast-path checks', implying callers must guard, but there is no matching guarantee at the function boundary; a future harness that forgets the negative-guard will trigger a panic rather than a verification failure. Add `assert!(v >= 0.0)` or replace with a non-panicking constructor (e.g. `StdDuration::try_from_secs_f64`) inside the `#[cfg(kani)]` exposer to make the contract self-enforcing.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322871908 -->
<!-- glab-discussion: aeccab8fbf87c0d76d25e6d728caaea88a66a338 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/kani_proofs/time_pure.rs:196` (2026-05-07 06:35 UTC) [open]

**[follow-up]** The `prove_lr!` macro for `DURNSECS` passes `arb_duration` (plain `Duration`, not `Extended<Duration>`) as the `A`-side generator, but `DURNSECS` is typed as `ConnK<Duration, Extended<i64>>` with `A = Duration`. This is intentional for a `conn_k!` triple, but the plan §Tier 1 table lists `roundtrip_ceil`, `roundtrip_floor`, and `floor_le_ceil` as required properties; the local review's 'Coverage gap' section acknowledges these are absent from `prove_l!`/`prove_lr!`. Per CLAUDE.md's convention, skipped properties must be documented in the plan's Review section with a re-enablement plan — the current plan §Review does not mention these missing properties, only the T0 tier retreat.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322871988 -->
<!-- glab-discussion: 52bca487cff6cab64c3542481d3befedab55b1f8 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/kani_proofs/hifi_pure.rs:39` (2026-05-07 06:35 UTC) [open]

**[follow-up]** `arb_epoch()` is constructed as `Epoch::from_tai_duration(arb_hd())`, which means the reachable `Epoch` space is exactly the same as `HD::MIN..=HD::MAX` in TAI. This is correct for `ETAINANO` and `ETAIHDUR`, but if any future harness in this file adds an `EUTCNANO`-style Conn whose domain is further restricted (e.g. by `hifitime`'s valid epoch range), the shared `arb_epoch` will silently assume the full TAI range; consider a note or a debug-assert inside `arb_epoch` that documents the intended domain.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322907463 -->
<!-- glab-discussion: b56e888732e36b1b9789f0c08724c836f170ca5d -->
#### ↳ cmk (2026-05-07 06:49 UTC) [open]

Fixed — both STDR walk-step exposers now mirror production's `v <= 0.0` fast-path, returning `(StdDuration::ZERO, 0)` before reaching `from_secs_f64` / `from_secs_f32`. The function boundary is panic-safe regardless of whether the harness asserts positivity.

<!-- glab-id: 3322907618 -->
<!-- glab-discussion: aeccab8fbf87c0d76d25e6d728caaea88a66a338 -->
#### ↳ cmk (2026-05-07 06:49 UTC) [open]

Fixed — plan §Review now has a section documenting that `roundtrip_ceil`, `roundtrip_floor`, and `floor_le_ceil` are deferred from the prove_l!/prove_lr! macros, with the re-enablement plan tracked in review-00067.md §Recommendations.

<!-- glab-id: 3322907831 -->
<!-- glab-discussion: 52bca487cff6cab64c3542481d3befedab55b1f8 -->
#### ↳ cmk (2026-05-07 06:49 UTC) [open]

Deferred — `arb_epoch` is intentionally typed as "any TAI epoch within HD's range" because that IS the reachable epoch domain in this crate (every Conn here is anchored to TAI or UTC-via-TAI Duration). When EUTCNANO-style Conns get Kani harnesses they'll need a separately-named generator anyway, since their valid input domain is asymmetric (the unix_min_nanos/unix_max_nanos shift). Adding domain commentary to the shared helper would tie it to a use case it doesn't cover.
