# MR !54 — Plan 34: Catamorphism extractors for Extended and ExtendedFloat

## Summary

- Adds `fold` and `fold_with` inherent methods to `Extended<T>` and
  `ExtendedFloat<T>` — the Rust analogue of Haskell's `maybe` /
  `either` extractors generalised to the three-arm shape
  `Bot/NegInf | mid | Top/PosInf`. Argument order is closure-last
  (`receiver, eager_endpoints, closure`) per the Rust convention
  shared by `Iterator::fold`, `Option::map_or`, and
  `Result::map_or_else`. `fold_with` defers all three arms behind
  `FnOnce` for callers whose endpoint defaults are expensive.
- Both methods sit on generic `impl<T> _ { … }` blocks, so they work
  for any inner `T` — not just the `f32` / `f64` arithmetic-bearing
  instantiations of `ExtendedFloat`.
- Tests: per-variant unit tests, a `Cell`-flag check that `fold_with`
  does not evaluate unselected arms, and a proptest asserting
  `fold_with` with const closures agrees with eager `fold` on
  `Extended<i64>` and `ExtendedFloat<f64>` (codomain via `to_bits`
  so `PartialEq` on the result doesn't trip over NaN).

## Test plan

- [ ] `cargo test --workspace` — all green; new `extended::tests`
      (4 unit + 1 proptest) and `float::tests` (4 unit + 1 proptest)
      visible.
- [ ] `cargo test --doc` — definition-site doctests on
      `Extended::fold` and `ExtendedFloat::fold` pass.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] Local pre-push hook (`RUSTDOCFLAGS="-D warnings" cargo doc
      --no-deps --features testing --document-private-items`) —
      clean.
