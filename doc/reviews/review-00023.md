# PR #23 - Replace ExtendedFloat with N5

## Summary

Replace the three-variant `ExtendedFloat<T>` enum with a transparent `N5<T>`
newtype over IEEE float payloads. The public `F016`, `F032`, and `F064` aliases
remain, but the float-side lattice now uses IEEE `-inf` / `+inf` as its bounds
and gives `NaN` the intended N5 ordering between them.

This keeps the existing Rust finite algorithms in place: float narrowing still
uses the ULP walk helpers, integer/fixed bridges keep their saturation guards,
and duration/epoch bridges keep their plateau solvers. The migration rewires the
old symbolic boundary plumbing to N5 boundary semantics instead of re-porting
the Haskell connection bodies wholesale.

The PR also updates docs, examples, proptest strategies, Kani harness paths, and
Try-trait behavior to match the new payload-only float type. `N5` has no
short-circuit sentinel under `Try`; `NaN` remains a payload.

Validation:

- `cargo fmt --check`
- `scripts/check_pii.sh`
- `scripts/check_readme_mirror.sh`
- `cargo check --all-targets --features fixed,time,hifi,uhlc,proptest,macros`
- `cargo test --features fixed,time,hifi,uhlc,proptest,macros`
- `cargo clippy --all-targets --features fixed,time,hifi,uhlc,proptest,macros -- -D warnings`
- `RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --features fixed,time,hifi,uhlc,proptest,macros`
- `cargo kani --features fixed --harness 'float_walk::t0_'`
- `cargo kani --features fixed --harness 'float_weaker::'`

## Local review (2026-07-08)

**Branch:** plan/2026-07-08-01
**Commits:** 6 (origin/main..plan/2026-07-08-01)
**Reviewer:** Codex (`codex review --base origin/main`)
**Prompt fingerprint:** AGENTS.md=4563f590caa7dbba5ea9eae973fa59182f1a6470 calibration=missing

---

The code changes appear consistent with the new N5 boundary semantics. The findings are documentation/comment drift only and should not break builds or tests.

Full review comments:

- [P3] Update obsolete -inf epoch caveat — src/hifi/epoch.rs:905-907
  After this patch the `f64::NEG_INFINITY` branch above returns `Extended::NegInf`, but this rustdoc still tells users it returns `Finite(Epoch::from_tai_duration(HD::MIN))`; the same caveat is then referenced by the other epoch scale docs. Users reading the public API docs will get the wrong boundary behavior, so the caveat should be updated or moved to the finite `v <= min_secs` plateau case.

- [P3] Remove stale -inf routing note — src/float.rs:1240-1243
  Now that the macro has an explicit `v == NEG_INFINITY` arm just above returning `NegInf`, this comment's `N5::new(-∞)` routing description is unreachable: `-∞` no longer falls through to `v < lo` or the cast-to-MIN path. Leaving this stale explanation next to a law-critical macro makes future edits likely to reintroduce the old boundary behavior; update it to describe finite below-min values or remove it.


<!-- gh-id: 3544170552 -->
### Copilot on [`src/float.rs:1287`](https://github.com/cmk/connections/pull/23#discussion_r3544170552) (2026-07-08 13:06 UTC)

`__float_ext_int_floor_body!` handles `+∞` explicitly but not `-∞`. When `lo` saturates to `-∞` (notably for f16 sources with wide integer targets), `v == NEG_INFINITY` falls through to the cast path and can yield `Finite(MIN)`/`Finite(0)` instead of the documented/required `Extended::NegInf`.

Add a symmetric `NEG_INFINITY` fast-path, matching the stated saturation policy (`N5(NEG_INFINITY) -> NegInf`).

<!-- gh-id: 3544170617 -->
### Copilot on [`src/fixed.rs:195`](https://github.com/cmk/connections/pull/23#discussion_r3544170617) (2026-07-08 13:06 UTC)

`__float_fix_floor_body!` handles `+∞` explicitly but not `-∞`. For some fixed-point ranges where `min_q.to_num::<f64>()` saturates to `-∞`, `v == NEG_INFINITY` can fall through to the scaling/cast path, producing an incorrect finite value instead of `Extended::NegInf`.

Add an explicit `NEG_INFINITY` arm for symmetry with `__float_fix_ceil_body!` and to preserve the documented saturation policy (`N5(NEG_INFINITY) -> NegInf`).

<!-- gh-id: 3544170664 -->
### Copilot on [`src/hifi/epoch.rs:2030`](https://github.com/cmk/connections/pull/23#discussion_r3544170664) (2026-07-08 13:06 UTC)

This test block asserts the `+∞` arm twice, which is redundant and makes it easier for future edits to accidentally diverge (e.g., one line updated, the other missed).

<!-- gh-id: 3544170691 -->
### Copilot on [`src/hifi/epoch.rs:2202`](https://github.com/cmk/connections/pull/23#discussion_r3544170691) (2026-07-08 13:06 UTC)

This test block asserts the `+∞` arm twice, which is redundant and increases the chance of drift during future edits.

<!-- gh-id: 3544170720 -->
### Copilot on [`src/hifi/epoch.rs:2572`](https://github.com/cmk/connections/pull/23#discussion_r3544170720) (2026-07-08 13:06 UTC)

This test block asserts the `+∞` arm twice, which is redundant and can cause noisy diffs or drift later.

<!-- gh-id: 4654386466 -->
### copilot-pull-request-reviewer[bot] — COMMENTED ([2026-07-08 13:06 UTC](https://github.com/cmk/connections/pull/23#pullrequestreview-4654386466))

## Pull request overview

This pull request migrates the crate’s float endpoint wrapper from the synthetic-endpoint `ExtendedFloat<T>` enum to a transparent `N5<T>` newtype that encodes the intended N5 preorder (`-∞ < NaN < +∞`, NaN incomparable with finite values) while keeping `F016/F032/F064` as public aliases.

**Changes:**
- Replace `ExtendedFloat<T>` with `N5<T>` across core float Conns, float↔int/fixed macros, and time/hifitime bridges (including boundary semantics).
- Update property strategies, integration tests, doctests, and Kani harnesses to construct/compare `N5` values (including reflexive NaN).
- Adjust `try_trait` behavior: `N5` is infallible under `Try` and never short-circuits.

### Reviewed changes

Copilot reviewed 31 out of 31 changed files in this pull request and generated 5 comments.

<details>
<summary>Show a summary per file</summary>

| File | Description |
| ---- | ----------- |
| tests/try_impls.rs | Updates `Try`/`?` behavior tests from `ExtendedFloat` short-circuiting to infallible `N5`. |
| tests/trait_method_api.rs | Updates proptest strategies and API checks to use `N5` (including NaN). |
| tests/fixed/helpers.rs | Updates fixed-bridge float strategies to generate `N5` values and infinities/NaN. |
| tests/fixed/helpers_f16.rs | Updates f16 fixed-bridge strategies to `N5<f16>`. |
| tests/core/surface.rs | Updates surface/prelude usage to construct `N5` values. |
| src/time/duration.rs | Rewrites duration bridges to unwrap `N5` payloads and map bounds via IEEE infinities. |
| src/prop/arb.rs | Rebuilds float strategies to generate `N5` with NaN and infinities as key cases. |
| src/prop.rs | Updates examples to use `N5::new(...)` in property docs. |
| src/lib.rs | Updates crate-level docs and feature notes from `ExtendedFloat` to `N5`. |
| src/lattice.rs | Updates lattice documentation/tests to use N5 ordering with IEEE infinities as bounds. |
| src/kani/float_weaker.rs | Updates Kani harnesses to use `core::f064` paths and `N5` payload wrappers. |
| src/kani/float_walk.rs | Updates Kani harness imports/doc links to `core::f064`. |
| src/hifi/epoch.rs | Rewrites epoch bridges for `N5` semantics and updates rustdoc/tests accordingly. |
| src/hifi/duration.rs | Rewrites hifitime duration bridges for `N5` semantics and updates tests/docs. |
| src/float.rs | Introduces `N5<T>` newtype, N5 `PartialOrd`/`Eq`, infallible `Try`, and rewires macros to IEEE infinities. |
| src/fixed/u128.rs | Updates fixed tests to construct float inputs via `N5::new`. |
| src/fixed/u064.rs | Updates fixed tests to construct float inputs via `N5::new`. |
| src/fixed/i064.rs | Updates fixed tests to construct float inputs via `N5::new`. |
| src/fixed.rs | Updates float↔fixed macros and docs to `N5` + IEEE infinity bound semantics. |
| src/extended.rs | Updates docs to point NaN-handling to `N5`. |
| src/core/f064.rs | Rewrites f64-hosted Conns to unwrap/rewrap `N5` and treat infinities as bounds. |
| src/core/f032.rs | Rewrites f32-hosted Conns similarly and updates boundary tests. |
| src/core/f016.rs | Rewrites f16 module docs/tests to the `N5` wrapper. |
| src/core.rs | Updates core module docs to reference `N5<T>`. |
| src/conn.rs | Updates Conn docs/examples to construct float endpoints via `N5`. |
| README.md | Updates public documentation for N5 semantics and `try_trait` behavior. |
| EXAMPLES.md | Updates examples to use `N5` and correct N5-boundary explanation. |
| doc/reviews/review-00023.md | Review log added/updated for this PR (audit trail). |
| doc/plans/plan-2026-07-08-01.md | Sprint plan documenting intended semantic shift and verification. |
| doc/design.md | Updates design rationale from `ExtendedFloat` synthetic endpoints to `N5` IEEE bounds. |
| Cargo.toml | Updates `try_trait` feature documentation to reflect `N5` infallible `Try`. |
</details>







<!-- gh-id: 3544302921 -->
#### ↳ cmk ([2026-07-08 13:24 UTC](https://github.com/cmk/connections/pull/23#discussion_r3544302921))

Fixed. `__float_ext_int_floor_body!` now handles `NEG_INFINITY` explicitly as `Extended::NegInf`, matching the documented N5 saturation policy. I also added a helper-level regression test for the expansion body.

Validation: `cargo test --features fixed,time,hifi,uhlc,proptest,macros`, clippy, and rustdoc all pass locally.

<!-- gh-id: 3544304054 -->
#### ↳ cmk ([2026-07-08 13:24 UTC](https://github.com/cmk/connections/pull/23#discussion_r3544304054))

Fixed. `__float_fix_floor_body!` now has the same explicit `NEG_INFINITY -> Extended::NegInf` arm as the ceil-side policy. I added a helper regression test alongside the macro body.

Validation: `cargo test --features fixed,time,hifi,uhlc,proptest,macros`, clippy, and rustdoc all pass locally.

<!-- gh-id: 3544305240 -->
#### ↳ cmk ([2026-07-08 13:24 UTC](https://github.com/cmk/connections/pull/23#discussion_r3544305240))

Fixed. Removed the duplicate `+∞` assertion; the test still covers NaN, `+∞`, and `-∞` once each.

Validation: the targeted `f064eunx_nan_inf_bounds` test and the broader feature test run pass locally.

<!-- gh-id: 3544306260 -->
#### ↳ cmk ([2026-07-08 13:25 UTC](https://github.com/cmk/connections/pull/23#discussion_r3544306260))

Fixed. Removed the duplicate `+∞` assertion; the test still covers NaN, `+∞`, and `-∞` once each.

Validation: the targeted `f064egps_nan_inf_bounds` test and the broader feature test run pass locally.

<!-- gh-id: 3544307300 -->
#### ↳ cmk ([2026-07-08 13:25 UTC](https://github.com/cmk/connections/pull/23#discussion_r3544307300))

Fixed. Removed the duplicate `+∞` assertion; the test still covers NaN, `+∞`, and `-∞` once each.

Validation: the targeted `f064etdt_nan_inf_bounds` test and the broader feature test run pass locally.
