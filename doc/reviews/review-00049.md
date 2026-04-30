# MR !49 — Drop `#[allow(unused_imports)]` shims for `Extended` in `fixed/i*.rs`

## Summary

- Plan 31 T4 switched the saturating-cast macros to fully-qualified
  `$crate::extended::Extended::*` paths, which made the parent-module
  `use crate::extended::Extended;` unused at the module level. Spot
  tests inside `mod tests` still need the import (via `use super::*;`),
  so it was kept with `#[allow(unused_imports)]` as a tactical shim
  documented as a follow-up.
- This MR pushes the import down into each `mod tests { ... }` block
  and drops the parent-level allow.
- One additional cleanup: `fixed/i16.rs` had a parent-level
  `use crate::conn::Conn;` solely to make the module-level rustdoc
  link `[`Conn`]` resolve. Switched to `[`Conn`](crate::conn::Conn)`
  so the import can also go.
- 5 files touched (`fixed/i16.rs`, `i32.rs`, `i64.rs`, `i128.rs`,
  plus `.gitignore`); ≈11 lines removed, ≈6 added.

## Test plan

- [x] `cargo test --workspace --features nix,macros,testing` — all 1230+ tests pass
- [x] `cargo clippy --all-targets --features nix,macros,testing -D warnings` — clean
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features
      testing,macros --document-private-items` — no broken intra-doc links
- [x] `cargo fmt --all -- --check` — clean
