# PR #6 — Pre-publish blockers, ergonomics, test-tree mirror

## Summary

Pre-publish polish ahead of the `connections` crate's first
crates.io release (`0.1.0`). The work lands the publish-blocker and
high-leverage-ergonomics findings from the four-agent code-health
audit in `doc/plans/plan-2026-05-19-01.md`, plus reorganises the
integration test tree to mirror `src/` and renames `kani_proofs` →
`kani`.

### Blockers (would break or visibly degrade publish)

- **`docs.rs` build would have failed.** `#[doc(cfg(...))]` is a
  nightly-only attribute behind `feature(doc_cfg)`. The crate uses
  it in three places but never declared
  `#![cfg_attr(docsrs, feature(doc_cfg))]`; docs.rs builds with
  `--cfg docsrs`, so the published crate would have produced E0658.
  Now declared at the top of `src/lib.rs`.

- **Internal helper-macro visibility correctly characterised.** The
  six `__float_ext_int_{ceil,floor,inner}_body!` /
  `__float_fix_{ceil,floor,inner}_body!` helpers stay
  `#[macro_export]` — their parent macros (`float_ext_int_l!` /
  `float_fixed_l!` etc.) invoke them via `$crate::__float_*_body!`
  paths from within this crate's own `src/core/{i,u}NNN.rs` and
  `src/fixed/{i,u}NNN.rs` files, regardless of the `macros` cargo
  feature. `macro_rules!` items require `#[macro_export]` for
  `$crate::name!` invocations to resolve at the crate root; gating
  it on `feature = "macros"` (an earlier attempt at this fix)
  broke `cargo check --features fixed` with 373 E0433 errors and
  was reverted on local review. The `__` prefix and
  `#[doc(hidden)]` keep these helpers out of the user-facing
  surface; the original audit conflated them with the seven public
  cast macros (`uint_uint!`, `int_uint!`, `ext_int!`, `*_narrow!`,
  `uint_int_sat!`, `nz_*_ext!`) gated by `src/lib.rs:97-99`, which
  these helpers are not part of. Inline comments at
  `src/float.rs:1432` and `src/fixed.rs:115` now document the
  constraint.

- **`Cargo.toml` v0.0.0**, weak description, `point` keyword,
  `proptest-regressions` file-rather-than-directory exclude, and the
  `testing` feature name that conflicted with `#[cfg(test)]`
  instincts. All addressed; feature renamed to `proptest` (matches
  the optional dep name), `proptest-regressions/` (with trailing
  slash) excludes the corpus, version bumped to `0.1.0`.

### Ergonomics (the day-1 user experience)

- **`Conn<A, B, K>` now derives `Debug`, `PartialEq`, `Eq`.** Today
  `dbg!(c)`, `assert_eq!(c1, c2)`, and `HashMap<_, Conn<_,_>>`
  registries all work. The hand-rolled `Debug` impl prints
  `Conn<source-tyname → target-tyname, K-tyname>` using
  `core::any::type_name`; equality is reference identity on the
  underlying `fn(A) -> B` / `fn(B) -> A` pair via
  `core::ptr::fn_addr_eq`.
- The macro-generated triple-marker unit structs (`F064F032`,
  composed markers via `compose_k!`, `nz_int_ext!` markers, lifted
  markers via `lift_k!`) all gained the standard
  `#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]`
  pack.
- **`connections::prelude`** now hosts the bare two-sided helpers
  (`round`, `truncate`, `median`, `interval`, the `1`/`2` lifters)
  alongside the capability traits and `Interval`. The same names
  are gone from the crate root — no pre-1.0 aliases. Downstream
  callers use `use connections::prelude::*` or the canonical module
  paths (`connections::core::B2`, `connections::interval::Interval`,
  etc.).

### Renames + reorg

- `src/kani_proofs/` → `src/kani/`, `mod kani_proofs;` → `mod kani;`.
  Inline references in `src/hifi/{epoch,duration}.rs` and the kani
  submodules updated.
- `tests/` flat layout → `tests/core/*.rs` + `tests/fixed/*.rs`
  mirroring `src/core/` and `src/fixed/`.
- Filenames lose the redundant `galois` suffix and use the same
  zero-padded `iNNN.rs` / `uNNN.rs` spelling as `src/`.
- `tests/common/{mod,f16}.rs` → `tests/fixed/helpers{,_f16}.rs`.
- New aggregator binaries `tests/core.rs` and `tests/fixed.rs` use
  `#[path]` attributes (Cargo doesn't auto-discover subdirectory
  `main.rs` as integration-test crate roots).
- `#![cfg(feature = "fixed")]` / `#![cfg_attr(feature = "f16",
  feature(f16))]` hoisted out of each per-host test file onto the
  aggregator crate root, with `#[cfg(feature = "f16")]` on the f16
  submodule declarations.
- `tests/core/surface.rs` adds the `Conn` PartialEq / Debug /
  prelude spot tests called out in the plan's Verification table.

### Docs / README

- README header: added docs.rs / crates.io / MSRV shields. MSRV
  table corrected (1.85 → 1.88). Feature column renamed `testing` →
  `proptest`. Quick-start doctest now uses `connections::prelude::*`
  and `connections::core::B2`.
- `src/lib.rs`: extended the codegen-macros table with `lift_l!` /
  `lift_r!` / `lift_k!` rows. Dropped the dangling references to
  `doc/design.md` (excluded from the published crate) and the
  fictional `src/macros.rs`.
- `AGENTS.md` (=`CLAUDE.md`): reconciled the canonical Conn-name
  examples — the shipped consts are `TDURSECS` and `ODTMNANO`, not
  the doc's `DURNSECS` / `OFDTNANO`.

## Test plan

- `cargo test --features "fixed,time,hifi,macros,proptest"` —
  4895 passing, 0 failing, 14 ignored (existing IGNORE harness).
- `cargo clippy --all-targets --features "fixed,time,hifi,macros,
  proptest" -- -D warnings` — clean.
- `RUSTDOCFLAGS="--cfg docsrs -D warnings" cargo +nightly doc
  --no-deps --features "fixed,proptest,macros,time"` — clean,
  reproduces the docs.rs target.
- `cargo package --list --allow-dirty` — 138 files; no
  `proptest-regressions/`, `doc/`, `.claude/`, `.github/`, or
  `scripts/` leaks.
- New spot tests in `tests/core/surface.rs`:
  `conn_eq_reflexive`, `conn_debug_non_empty`,
  `prelude_glob_brings_traits`. All passing.

## Deferred

See `doc/plans/plan-2026-05-19-01.md § Review`.

## Local review (2026-05-19)

**Branch:** plan/2026-05-19-01
**Commits:** 4 (origin/main..plan/2026-05-19-01)
**Reviewer:** Codex (`codex review --base origin/main`)
**Prompt fingerprint:** AGENTS.md=b5f7584f2875c10abb637c9b483b4c7e0cb37891 calibration=missing

---

The patch does not compile in default builds because helper macros are no longer reachable while still referenced through `$crate::`. The feature rename also leaves repository CI/hooks invoking a removed feature, which blocks the standard gates.

Full review comments:

- [P1] Restore helper macro visibility for default builds — src/float.rs:1431-1431
  With `macro_export` now gated behind `feature = "macros"`, the internal `float_ext_int!`/`float_fixed!` macros still expand to `$crate::__float_*_body!`. In builds without `macros` (default `cargo check` already fails; `--features fixed` does the same for the fixed helpers) those helper names are no longer in the crate root, producing E0433 before the crate compiles. Keep the helpers reachable for internal expansion, or change the macro bodies to a non-exported path that remains visible.

- [P1] Keep CI feature names in sync — Cargo.toml:68-68
  Renaming the feature to `proptest` removes the `testing` feature, but the repository's existing gates still invoke `cargo test/doc --features fixed,time,hifi,testing,macros` (for example `.github/workflows/ci.yml` and `.githooks/pre-push`). Those commands now stop immediately with `the package 'connections' does not contain this feature: testing`, so every push/PR will fail until the callers are updated or a compatibility alias is left.


<!-- gh-id: 3270121159 -->
### Copilot on [`src/float.rs:1440`](https://github.com/cmk/connections/pull/6#discussion_r3270121159) (2026-05-19 22:47 UTC)

The PR description says the internal `__float_ext_int_*_body!` helpers are feature-gated (only exported with `feature = "macros"`), but these helpers are still unconditionally `#[macro_export]`, so they remain callable as `connections::__float_ext_int_ceil_body!` etc even when `macros` is off. If the intent is to keep them out of the public macro namespace, consider making them crate-root-only without `macro_export` (e.g., import them into the root with `#[macro_use]` or move the helpers to the crate root) and/or update the PR description to match the shipped behavior.

<!-- gh-id: 4323819557 -->
### copilot-pull-request-reviewer[bot] — COMMENTED ([2026-05-19 22:47 UTC](https://github.com/cmk/connections/pull/6#pullrequestreview-4323819557))

## Pull request overview

Pre-release polish for the `connections` Rust crate ahead of its first crates.io publish, focusing on docs.rs compatibility, public API ergonomics (prelude + `Conn` traits), and a large test-tree reorganization to mirror `src/` (plus `kani_proofs` → `kani`).

**Changes:**
- Add a `connections::prelude` namespace for trait + helper imports; update docs/doctests/fixtures accordingly and tighten Interval paths.
- Add `Conn<A,B,K>` `Debug` + `PartialEq`/`Eq` (fn-pointer identity), and add “surface” smoke tests.
- Reorganize integration tests into `tests/core/*` + `tests/fixed/*` with aggregator crates; introduce/expand Kani harness modules under `src/kani/`.

### Reviewed changes

Copilot reviewed 59 out of 89 changed files in this pull request and generated 2 comments.

<details>
<summary>Show a summary per file</summary>

| File | Description |
| ---- | ----------- |
| tests/fixed.rs | Aggregates `fixed` integration tests; hoists `fixed`/`f16` gating to crate root. |
| tests/fixed/helpers.rs | Shared float strategy helpers for fixed float→Q submodules. |
| tests/fixed/helpers_f16.rs | Shared f16 strategy helper for fixed float→Q f16 submodules. |
| tests/fixed/nz_iso.rs | Fixed NonZero + cross-crate iso proptest battery, moved under new layout. |
| tests/fixed/u008.rs | Fixed u8 proptest battery under new layout (drops per-file `cfg`). |
| tests/fixed/u016.rs | Fixed u16 proptest battery under new layout (drops per-file `cfg`). |
| tests/fixed/u032.rs | Fixed u32 proptest battery under new layout (drops per-file `cfg`). |
| tests/fixed/u064.rs | Fixed u64 proptest battery under new layout (drops per-file `cfg`). |
| tests/fixed/u128.rs | Fixed u128 proptest battery under new layout (drops per-file `cfg`). |
| tests/fixed/u008_float_q.rs | Fixed u8 float→Q proptest battery updated to use shared helpers module. |
| tests/fixed/u016_float_q.rs | Fixed u16 float→Q proptest battery updated to use shared helpers module. |
| tests/fixed/u032_float_q.rs | Fixed u32 float→Q proptest battery updated to use shared helpers module. |
| tests/fixed/u064_float_q.rs | Fixed u64 float→Q proptest battery updated to use shared helpers module. |
| tests/fixed/u128_float_q.rs | Fixed u128 float→Q proptest battery updated to use shared helpers module. |
| tests/fixed/u008_float_q_f16.rs | Fixed u8 f16→Q proptest battery updated to use shared f16 helper module. |
| tests/fixed/u016_float_q_f16.rs | Fixed u16 f16→Q proptest battery updated to use shared f16 helper module. |
| tests/fixed/u032_float_q_f16.rs | Fixed u32 f16→Q proptest battery updated to use shared f16 helper module. |
| tests/fixed/u064_float_q_f16.rs | Fixed u64 f16→Q proptest battery updated to use shared f16 helper module. |
| tests/fixed/u128_float_q_f16.rs | Fixed u128 f16→Q proptest battery updated to use shared f16 helper module. |
| tests/fixed/i008_float_q.rs | Fixed i8 float→Q proptest battery updated to use shared helpers module. |
| tests/fixed/i016_float_q.rs | Fixed i16 float→Q proptest battery updated to use shared helpers module. |
| tests/fixed/i032_float_q.rs | Fixed i32 float→Q proptest battery updated to use shared helpers module. |
| tests/fixed/i064_float_q.rs | Fixed i64 float→Q proptest battery updated to use shared helpers module. |
| tests/fixed/i128_float_q.rs | Fixed i128 float→Q proptest battery updated to use shared helpers module. |
| tests/fixed/i008_float_q_f16.rs | Fixed i8 f16→Q proptest battery updated to use shared f16 helper module. |
| tests/fixed/i016_float_q_f16.rs | Fixed i16 f16→Q proptest battery updated to use shared f16 helper module. |
| tests/fixed/i032_float_q_f16.rs | Fixed i32 f16→Q proptest battery updated to use shared f16 helper module. |
| tests/fixed/i064_float_q_f16.rs | Fixed i64 f16→Q proptest battery updated to use shared f16 helper module. |
| tests/fixed/i128_float_q_f16.rs | Fixed i128 f16→Q proptest battery updated to use shared f16 helper module. |
| tests/core.rs | Aggregates `core` integration tests mirroring `src/core/`. |
| tests/core/surface.rs | Adds surface smoke tests for `Conn` `Debug`/`PartialEq` and prelude behavior. |
| tests/core/i008.rs | Core i8 proptest battery (new layout). |
| tests/core/i016.rs | Core i16 proptest battery (new layout). |
| tests/core/i032.rs | Core i32 proptest battery (new layout). |
| tests/core/i064.rs | Core i64 proptest battery (new layout). |
| tests/core/i128.rs | Core i128 proptest battery (new layout). |
| tests/core/u008.rs | Core u8 proptest battery (new layout). |
| tests/core/u016.rs | Core u16 proptest battery (new layout). |
| tests/core/u032.rs | Core u32 proptest battery (new layout). |
| tests/core/u064.rs | Core u64 proptest battery (new layout). |
| tests/core/u128.rs | Core u128 proptest battery (new layout). |
| tests/compile_fail/round_on_l_conn.rs | Updates compile-fail test to import `round` from the prelude. |
| tests/compile_fail/round_on_l_conn.stderr | Updates expected diagnostics to match new `round` path in errors. |
| src/lib.rs | Adds docsrs `doc_cfg` gate, introduces `prelude`, renames `kani_proofs` module to `kani`, updates docs. |
| src/conn.rs | Adds `Conn` `PartialEq`/`Eq` and `Debug`; switches Interval import to `crate::interval::Interval`; derives on marker macros. |
| src/interval.rs | Updates doctests to the new `connections::interval::Interval` path. |
| src/prop.rs | Renames `testing` feature references to `proptest` and updates gating/docsrs cfg. |
| src/prop/interval.rs | Fixes `Interval` doc links/imports to use the `interval` module path. |
| src/prop/conn.rs | Updates Interval references to `crate::interval::Interval`. |
| src/core.rs | Adds standard derives to macro-generated marker types (e.g., `nz_int_ext!`). |
| src/core/i008.rs | Updates doctest import to use `connections::core::B2`. |
| src/extended.rs | Adds standard derives to `lift_k!` marker structs. |
| src/float.rs | Adds docs explaining why certain helper macros are `macro_export`; keeps float helper macros for internal expansion. |
| src/fixed.rs | Adds docs explaining why certain helper macros are `macro_export`; keeps fixed helper macros for internal expansion. |
| src/time/duration.rs | Rustfmt/clippy-style formatting tweak (`{b:?}`) in test messages. |
| src/hifi/duration.rs | Updates internal references from `kani_proofs` to `kani`. |
| src/hifi/epoch.rs | Updates internal references from `kani_proofs` to `kani` and modernizes formatting in tests. |
| src/kani.rs | New `kani` module root documenting harness layout and shared step bound constant. |
| src/kani/ext_int.rs | Adds Kani harnesses for `ext_int!`-generated connections. |
| src/kani/int_narrow.rs | Adds Kani harnesses for `int_int_narrow!` connections. |
| src/kani/uint_widen.rs | Adds Kani harnesses for widening integer connections. |
| src/kani/uint_narrow.rs | Adds Kani harnesses for narrowing integer connections. |
| src/kani/uint_sat.rs | Adds Kani harnesses for saturating unsigned→signed connections (right-Galois). |
| src/kani/nz_ext.rs | Adds Kani harnesses for NonZero extension connections (signed + unsigned). |
| src/kani/iso_family.rs | Adds Kani harnesses for cross-crate iso families. |
| src/kani/fix_fix_signed.rs | Adds Kani harnesses for signed Q-format ladder connections. |
| src/kani/fix_fix_unsigned.rs | Adds Kani harnesses for unsigned Q-format ladder connections. |
| src/kani/float_walk.rs | Adds Kani proofs bounding f64→f32 ULP-walk iterations. |
| src/kani/float_weaker.rs | Adds Kani proofs for weaker, SMT-tractable float properties. |
| src/kani/time_walk.rs | Adds Kani proofs for duration walk/solver step bounds. |
| src/kani/time_pure.rs | Updates references after `kani_proofs` → `kani` rename. |
| src/kani/hifi_walk.rs | Updates references after `kani_proofs` → `kani` rename. |
| src/kani/hifi_pure.rs | Updates references after `kani_proofs` → `kani` rename. |
| src/kani/hifi_calendar.rs | Adds Kani harnesses for calendar-enum hifi-domain connections. |
| src/kani/fixed_be_one.rs | Adds Kani harnesses for 1-byte big-endian encoding isos. |
| src/kani/fixed_be_two.rs | Adds Kani harnesses for 2-byte big-endian encoding isos. |
| src/kani/fixed_be_four.rs | Adds Kani harnesses for 4-byte big-endian encoding isos. |
| src/kani/fixed_le_one.rs | Adds Kani harnesses for 1-byte little-endian encoding isos. |
| src/kani/fixed_le_two.rs | Adds Kani harnesses for 2-byte little-endian encoding isos. |
| src/kani/fixed_le_four.rs | Adds Kani harnesses for 4-byte little-endian encoding isos. |
| scripts/git_autosquash_finalize.sh | Updates feature name in local gate script (`testing` → `proptest`). |
| Cargo.toml | Bumps version to 0.1.0, refines metadata, renames `testing` feature to `proptest`, updates docs.rs features. |
| README.md | Adds badges, updates quickstart imports, fixes MSRV, and renames feature in table. |
| AGENTS.md | Updates naming examples to match shipped constants (e.g., `TDURSECS`, `ODTMNANO`). |
| .github/workflows/ci.yml | Updates CI invocations to use `proptest` feature name. |
| .github/workflows/pages.yml | Updates docs build invocation to use `proptest` feature name. |
| .githooks/pre-push | Updates hook invocations to use `proptest` feature name. |
| doc/plans/plan-2026-05-19-01.md | Adds plan/verification record describing this work and deviations. |
| doc/reviews/review-00006.md | Adds PR review audit record for this PR. |
</details>




<details>
<summary>Comments suppressed due to low confidence (1)</summary>

**tests/fixed/helpers.rs:6**
* The module-level comment says CI “doesn't pass” the `proptest` feature to integration tests, but the CI workflow runs `cargo test --features fixed,time,hifi,proptest,macros` (so `proptest` is enabled). Please update the comment to reflect the current rationale for inlining these strategies (e.g., avoiding a dependency on `connections::prop::arb` / keeping helpers local).
</details>



<!-- gh-id: 3270121215 -->
### Copilot on [`src/fixed.rs:123`](https://github.com/cmk/connections/pull/6#discussion_r3270121215) (2026-05-19 22:47 UTC)

The PR description calls out feature-gating internal helper macros to avoid leaking them at the crate root, but `__float_fix_ceil_body!` is still unconditionally `#[macro_export]` (and similarly for the other `__float_fix_*_body!` helpers). This keeps the macro names publicly callable even when `feature = "macros"` is off. Either adjust the implementation so the helpers are available to in-crate macro expansion without being exported, or update the PR description/design notes to reflect that these helpers intentionally remain exported.

<!-- gh-id: 3270252530 -->
#### ↳ cmk ([2026-05-19 23:14 UTC](https://github.com/cmk/connections/pull/6#discussion_r3270252530))

The PR description was inaccurate — corrected in this round. `#[macro_export]` is intentional: the public-facing `float_ext_int_l!` / `float_fixed_l!` macros expand to `$crate::__float_ext_int_*_body!()` invocations from this crate's own `src/core/{i,u}NNN.rs` and `src/fixed/{i,u}NNN.rs` files, and those expansions need to resolve regardless of the `macros` cargo feature. An earlier attempt to gate `#[macro_export]` on `feature = "macros"` broke `cargo check --features fixed` with 373 E0433 errors (caught by codex local review at `8c37c21`). The `__` prefix + `#[doc(hidden)]` are the public-API signal; inline comments at `src/float.rs:1432` and `src/fixed.rs:115` now document the constraint.

<!-- gh-id: 3270252840 -->
#### ↳ cmk ([2026-05-19 23:14 UTC](https://github.com/cmk/connections/pull/6#discussion_r3270252840))

Same finding as the `src/float.rs:1440` thread — see the reply there for the full reasoning. Short version: `#[macro_export]` is required for the parent macros (`float_fixed_l!` etc.) to invoke these via `$crate::` paths from inside this crate, regardless of the `macros` cargo feature. The PR description has been updated to match; inline comment at `src/fixed.rs:115` documents the constraint.
