# Review of MR !98 — Fixed feature split, Q000 renames, and skinny CI

## Summary

- Make the `fixed` crate an optional dependency behind the `fixed`
  feature, including crate module gating, fixed-only integration-test
  gating, and docs that build in a skinny default configuration.
- Rename the cross-crate Q.0 bit isos from `I###Q000` / `U###Q000` to
  `Q000I###` / `Q000U###`, with no compatibility aliases.
- Add signed normalized fixed bit isos for the primitive-width
  `[-1, 1)` fixed domains: `Q007I008`, `Q015I016`, `Q031I032`,
  `Q063I064`, and `Q127I128`.
- Change CI so the default doc job is skinny, add a scheduled/flagged
  nightly all-features doc job, and add conservative diff-aware test
  selection that still escalates to the full stable feature set for
  shared or broad changes.

## Test plan

- `cargo check --no-default-features`
- `cargo check --no-default-features --features fixed`
- `cargo test --no-default-features --no-run`
- `cargo test --no-default-features --features fixed --no-run`
- `cargo fmt --all -- --check`
- `cargo clippy --all-targets -- -D warnings`
- `cargo clippy --all-targets --features fixed,time,hifi,testing,macros -- -D warnings`
- `cargo test --workspace --doc`
- `cargo test --workspace --doc --features fixed,time,hifi,testing,macros`
- `RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --document-private-items`
- `RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --features fixed,testing,macros,time --document-private-items`
- `RUSTDOCFLAGS='-D warnings' cargo +nightly doc --no-deps --all-features --document-private-items`
- `cargo test --features fixed q000 --lib`
- `cargo test --features fixed --test fixed_nz_iso_galois`
- `cargo test --features fixed lift_k_q000i016 --lib`
- `cargo nextest run --workspace --profile ci --features fixed --test fixed_nz_iso_galois`
- `cargo nextest run --workspace --profile ci --lib --test compile_fail`
- `CI_MERGE_REQUEST_DIFF_BASE_SHA=HEAD bash scripts/ci-select-tests.sh`

## Review Notes

### P2 — Run fixed lib tests for fixed-only changes

**Comment**

> When a diff only touches `src/fixed.rs` or `src/fixed/*`, this branch
> runs only the `tests/fixed_*` integration tests with the fixed
> feature. The earlier `run_nextest --lib --test compile_fail` is
> executed without `--features fixed`, so all unit tests embedded under
> `src/fixed/*` are skipped for exactly the changes that need them. Add
> a `run_nextest --features fixed --lib` in this branch so fixed-module
> spot/unit tests continue to gate fixed-only MRs.

**Response**

Fixed. The fixed-family branch in `scripts/ci-select-tests.sh` now runs
`run_nextest --features fixed --lib` before `run_family --features fixed
'fixed_*'`, so fixed-only diffs gate both embedded fixed module unit
tests and fixed integration tests.

Verified with:

- `bash -n scripts/ci-select-tests.sh`
- `cargo nextest run --workspace --profile ci --features fixed --lib`
  (1361 tests passed)
