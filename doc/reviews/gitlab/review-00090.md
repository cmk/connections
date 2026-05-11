# review-00090 - Source-orient fixed/std iso names

## Summary

- Renames the fixed/std cross-crate iso family from `Q000I###` /
  `Q000U###` to primitive-left `I###Q000` / `U###Q000`.
- Flips each iso declaration so the public source side matches the new
  marker name: `{i,u}N => Fixed{I,U}N<Q0>`.
- Updates inline tests, integration proptests, Kani harness references,
  lifted-Conn examples/tests, and public naming docs to use the new
  LHS-oriented names.

## Test plan

- [x] `cargo test --workspace --quiet`
- [x] `cargo fmt --all -- --check`
- [x] `cargo clippy --all-targets --quiet -- -D warnings`
- [x] `git diff --check`
