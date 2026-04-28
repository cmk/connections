# MR !35 — `ExtendedFloat<f32|f64>` numerical-trait expansion + Newton-step doctests

## Summary

- Expands the `ExtendedFloat<f32|f64>` numeric surface to a fuller
  std-shaped API: adds `Mul`, `Neg`, `Rem` with the existing
  conservative Bot/Top semantics, the five `*Assign` siblings, plus
  inherent transcendental methods (`sin`/`cos`/`tan` and their
  inverses, `sqrt`/`cbrt`/`exp`/`exp2`/`ln`/`log2`/`log10`,
  `abs`/`signum`/`recip`, `powi`/`powf`/`mul_add`, `atan2`),
  inherent constants (`PI`/`TAU`/`E`/`FRAC_PI_2`/`NAN`/`INFINITY`/
  `NEG_INFINITY`/`ZERO`/`ONE`), and predicates (`is_nan`/
  `is_finite`/`is_infinite`). Plus broader `From<integer>`
  conversions: `i8`/`i16`/`u16` for both, `i32`/`u32` for f64 only
  (lossless), and the obvious `From<T>` wrappers.
- Demonstrates the new surface end-to-end with a Newton-step doctest
  on `round1` (`|a| a - a.tan()` starting from
  `std::f32::consts::PI` — converges to true π_f64 in f64-precision,
  rounds back to f32) and a shared "between-grid-points" probe for
  `truncate1` / `floor1` / `ceiling1` that produces an f64 result
  strictly between two f32 endpoints, so the three rounding modes
  pick observably different f32 values side-by-side.
- Tightens every loose `assert!(x >= y)` / tautological
  `assert_eq!(round(c, x), c.ceil(x))` doctest in `src/conn.rs` to
  illustrative `assert_eq!`s against concrete literals (the
  Haskell-style `pi - midpoint == 3.1786509424591713e-8`, the
  catastrophic-cancellation `(2^24-1+2)-(2^24-1)` round2 example,
  etc.). Binds a recurring `pi32_err = pi32 - pi64` constant in
  `upper`/`ceiling`/`round` so the f32 rounding error reads as a
  *named* magnitude rather than three opaque digit strings.
- Lifts the Haskell `Cast.hs` laws into rustdoc `# Laws` sections
  on every helper that has one, citing the corresponding
  `property::laws` predicate when it exists. Adds the missing
  `cast_median_associative` predicate plus its proptest. Adds a
  faithful `median` NaN doctest demonstrating that N5's lub of an
  incomparable pair escalates to `Top`, reproducing Haskell's
  `median f32f32 1.0 9.0 (0.0/0.0) == 9.0` from the same lattice
  law (no port-specific NaN-as-Top hack).

## Test plan

- [x] `cargo build` — clean.
- [x] `cargo test --workspace` — 1142 lib tests + 34 doctests pass.
      Six new property tests in `float::tests` for the arithmetic
      Bot/Top semantics, ten more for the inherent transcendental
      endpoints, four for `From<integer>`, plus the
      `median_associative_ordered` proptest in `conn::tests`.
- [x] `cargo clippy --all-targets -- -D warnings` — clean.
- [x] `cargo doc --no-deps` — clean (modulo two pre-existing
      `property::arb` warnings unrelated to this branch).
- [x] All four T4 + T6 numeric literals (Newton-step result, the
      shared probe's two distinct f32 endpoints, the median NaN
      9.0 result) confirmed via a one-shot probe binary deleted
      before commit. The asserted constants match real impl output
      exactly.
