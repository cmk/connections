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

