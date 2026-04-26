# MR !12 — Reparent fixed module: decimal becomes `fixed::decimal`

## Summary

- Move `src/conn/fixed.rs` (decimal SI-prefix ladder) into
  `src/conn/fixed/decimal.rs` verbatim, replace `src/conn/fixed.rs`
  with a thin module root, so the `conn::fixed::*` namespace can host
  upcoming `fixed`-crate-native binary sub-modules
  (`fixed::{i08,i16,i32,i64}`) in a follow-up MR.
- Mechanical import-path updates in 5 other files (sample, arb,
  conn, lib, property/mod). No content changes inside the moved
  module; const names (`F03F00`, `F12F06`, `F64F06`, etc.) preserved.
- **Breaking change** for downstream callers: `connections::conn::fixed::Pico`
  → `connections::conn::fixed::decimal::Pico` (and the same path
  shift for every other decimal-tier name).

## Test plan

- [ ] `cargo test --workspace` — 651 + 3 doctests pass; no
      regressions vs `origin/main` baseline.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo doc --no-deps` — clean (one pre-existing warning on
      `src/property/mod.rs:8` about `[arb]` link gating; not
      introduced by this MR).
- [ ] Pre-commit hook green (cargo fmt check, PII check, cargo test,
      cargo clippy).
- [ ] Manual smoke: a downstream `use connections::conn::fixed::decimal::Pico;`
      compiles and the existing decimal const constants are reachable
      through the new path.

## Local review (2026-04-26)

**Branch:** sprint/fixed-conns
**Commits:** 2 (origin/main..sprint/fixed-conns)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Two commits, correctly ordered: `b42d1a0 task: Reparent fixed module — decimal becomes fixed::decimal` carries all source changes, `6dafe28 doc: Plan 06 + MR !12 description for fixed-module reparent` carries docs only. Both subjects are conventional and within 72 chars. Commit `b42d1a0` collapses T1+T2+T3 into one as explicitly justified in the plan ("the import updates are mechanical fall-out of the move and have to be in the same commit to keep the build green") — that reasoning is sound and the commit is atomic for the same reason. No merge commits; no unrelated changes mixed in.

### Code Quality

All changed files follow repo conventions. No stale references to `crate::conn::fixed::{...}` (decimal items) survive in the diff: `src/conn.rs`, `src/conn/sample.rs`, `src/lib.rs`, `src/property/arb.rs`, and `src/property/mod.rs` are all updated to `::decimal::`.

The new `src/conn/fixed.rs` module root is 10 lines: a doc comment plus `pub mod decimal;`. The doc comment accurately describes what is present (`decimal` — SI-prefix ladder) and what is coming (binary `FixedI*<Frac>` sub-modules). No clippy issues are visible; the diff introduces no new items that could attract dead-code warnings. Comment drift: the test comment in `src/conn/fixed/decimal.rs` correctly says the `compose!` tests live in `crate::conn` — that remains accurate.

One minor observation: the new `fixed.rs` module root does not carry `#![forbid(unsafe_code)]`. The file is too small to need it (it contains no code at all, only `pub mod decimal;`), so this is not a defect — but the follow-up sprint that adds `fixed::{i08,i16,i32,i64}` should add the attribute there before the module gains any implementation.

### Test Coverage

All 21 `props_for_pair!` invocations and both `float_conn_props!` invocations are present in `src/conn/fixed/decimal.rs`, identical to the removed content from the old `fixed.rs`. No `#[ignore]` was added, no test function was removed. The `use super::*;` inside the `#[cfg(test)]` block resolves to `decimal`'s own items, which is correct. Doctests in `lib.rs` (`no_run` block), `conn.rs` (`no_run` block), and `property/mod.rs` are all updated to the new path.

### Plan Conformance

- **T1** (move `fixed.rs` → `fixed/decimal.rs`): Done. Git reports the file as a rename via similarity heuristic; content is verbatim.
- **T2** (new `fixed.rs` module root + import-path updates): Done. All five files in the plan's table are updated; the new root matches the spec (`pub mod decimal;` plus doc comment).
- **T3** (verify + commit as a single task commit): Done. Single `task:` commit for all source changes.
- **Deferred items** (`fixed::{i08,i16,i32,i64}`, `doc/design.md` section): Correctly scoped out; noted in the plan's Deferred section.

The plan's Verification table said "no new properties; existing proptests keep passing unchanged." The diff bears that out — no properties were added or removed.

### Risks

**Breaking change coverage**: The only public-API break is the path shift `connections::conn::fixed::{Pico, …}` → `connections::conn::fixed::decimal::{Pico, …}`. This is documented in `review-00012.md` and the plan's build-gates section. No re-export of the old flat path (`pub use decimal::*;` in `fixed.rs`) is present — that is the correct choice for a clean rename, but it means any downstream consumer not watching the changelog will get a hard compile error with no compatibility shim. This is the stated intent; just confirm the MR title/description makes the breaking-change classification prominent.

**Scripts and generated files**: A grep of the diff shows no CI scripts, build scripts, or generated files reference the old `conn::fixed` path. `scripts/` are not touched by this MR.

**Module-root thinness**: `src/conn/fixed.rs` at ~10 lines is intentionally thin and correctly structured. No concern here; it is standard Rust module-directory pattern.

### Recommendations

**Must fix before push:** None. The diff is mechanically correct, all import paths are updated, all tests are present, and the commit messages and structure conform to conventions.

**Follow-up (future work):**

1. `src/conn/fixed.rs` does not yet carry `#![forbid(unsafe_code)]`. Add it in the follow-up sprint when `fixed::{i08,i16,i32,i64}` are introduced, before that module gains any implementation.
2. Consider whether a `pub use self::decimal::*;` compatibility re-export (behind a `#[deprecated]` note) belongs here to soften the breaking change for downstream users. The plan explicitly chose not to add one — that is defensible — but if the crate has external consumers already on the old path, a one-sprint deprecation window would reduce the upgrade cliff. This is a product-level call, not a convention violation.

