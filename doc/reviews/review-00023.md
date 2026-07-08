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
