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

## Local review (2026-05-02)

**Branch:** `sprint/extended-fold`
**Commits:** 2 (origin/main..sprint/extended-fold) before fix; 3 after
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Two commits at review time: `feat:` (implementation) and `doc:`
(plan/review skeleton). Each atomic, conventional, ≤72 char subject.
Tree green at every commit.

### Code Quality

- Generic `impl<T>` placement on `ExtendedFloat<T>` correct — methods
  don't touch inner-T arithmetic.
- Argument order (`receiver, eager_endpoints, closure`) matches Rust
  idiom (`Iterator::fold`, `Option::map_or`).
- Doctests at both `fold` definition sites; intra-doc links to
  `fold_with` resolve.
- **One issue:** `fold_with` doc comments said "Mirrors
  `Option::map_or_else`" — technically accurate (`map_or_else` is
  also fully lazy in both arms, both `D` and `F` are `FnOnce`) but
  ambiguous to a reader who reads `map_or_else` as "default is lazy,
  transformation is eager." Replaced with explicit "all three arms
  are wrapped in `FnOnce` closures and only the matched arm is
  called" on both `Extended::fold_with` and
  `ExtendedFloat::fold_with`. Fixed in the round-0 fix commit.

### Test Coverage

- Per-variant unit tests present for both enums (3 each).
- `Cell`-flag laziness tests prove unselected arms aren't invoked.
- Proptests assert lazy-vs-strict equivalence on `Extended<i64>`
  and `ExtendedFloat<f64>`. Codomain via `to_bits` for the float
  case, sound — `to_bits()` is total over all `f64` bit patterns
  (NaN included), and the resulting `i64` has exact `PartialEq`.

### Plan Conformance

T1, T2, T3 all delivered. Both Verification-table properties
(`extended_fold_with_const_agrees_with_fold`,
`extfloat_fold_with_const_agrees_with_fold`) present. No
`#[ignore]`. Nothing in the diff outside the plan's scope.

### Risks

- Future `Fold` trait collision: low-probability, name kept
  deliberately (catamorphism is the established meaning of `fold`
  in Rust).
- Generic `impl<T>` block alongside macro-generated impls: addressed
  by the placement comment added in the round-0 fix commit.
- Proptest tautology: acknowledged; value is divergence-guard against
  future arm reordering.

### Recommendations

**Must fix before push:**
1. ~~`fold_with` doc comments — `map_or_else` analogy ambiguous.~~
   Fixed in the round-0 fix commit.

**Follow-up:**
2. ~~Add a comment above the generic `impl<T>` block in `float.rs`
   explaining placement.~~ Done in the round-0 fix commit.
3. Note about potential future `Fold` trait collision — skipped;
   too hypothetical to warrant doc/code real estate now.
