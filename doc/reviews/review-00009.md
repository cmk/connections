# PR #9 — README badge fix, 2-kinded prose, alias uniformity

## Summary

Three small docs / naming-hygiene drift fixes landed atop sprint 2:

- **Replace the 404-rendering badges.** `crates.io` and `docs.rs`
  shields pointed at a crate that hasn't been published yet, so both
  badges rendered "not found". Swap them to static `unreleased` /
  `github.io` placeholders whose link targets stay live and auto-flip
  back to dynamic shields on the v0.1.0 publish PR (HTML-comment TODO
  marks the swap point). The docs badge repoints at the existing
  GitHub Pages build.
- **Reformat `## 2-kinded connections`.** The first paragraph was a
  dense 16-line block. Break it into three short paragraphs, a tight
  bulleted list of the three traits (`ConnL` / `ConnR` / `ConnK`), a
  `> Convention.` callout that states the const-vs-struct shape
  convention explicitly, and a closing paragraph about the
  free-function "third adjoint". A matching one-line forward-pointer
  in the earlier `## L & R kind connections` section gives the
  convention a second hit for top-down readers — same key, two
  reasonable placements as the user requested.
- **Dedup F016, document the per-host fixed alias layer.** `pub type
  F016 = ExtendedFloat<f16>` was declared in both `src/float.rs`
  (alongside F032 / F064) and `src/core/f016.rs`. Remove the
  duplicate; keep all three float aliases co-located in
  `src/float.rs`. Cross-callers (`core/f032.rs`, `core/f064.rs`)
  switch their `use super::f016::{F016, …}` to `use crate::float::F016;`.
  In `src/fixed.rs` module docs, add a `## Per-host type aliases`
  section explaining that the `pub type I###` / `U###` aliases per
  `fixed::iN`/`fixed::uN` module are a deliberately distinct
  namespace from the Conn-name convention (where `I`/`U` are
  std-primitive sides and `Q###` is the Q-format wrapper side);
  cross-link from `src/lib.rs`'s Naming section.

Drive-by typo fix: two existing `crate::float::f016::shift16_f16`
references in `src/float.rs` (lines 907, 1046) were broken on the
nightly+f16 feature build — `shift16_f16` lives in
`crate::core::f016`, not `crate::float::f016` (which is not a
module). The default-feature build skipped these lines via cfg
gating; the f16 build did not, so this was a pre-existing
nightly-only compile error caught while validating T3. Fixed
in the same `debt:` commit as the F016 dedup.

No new Conns ship in this sprint. No new proptest properties were
added. All 4950 existing tests still green
(`cargo test --features fixed,time,hifi,macros` → 1855 + 1 + 473 +
2522 + 9 + 90).

## Test plan

- [x] `cargo build --features fixed,time,hifi,macros` — clean
- [x] `cargo +nightly build --features fixed,time,hifi,macros,f16` — clean
- [x] `cargo test --features fixed,time,hifi,macros` — 4950 / 4950 pass
- [x] `cargo clippy --all-targets --features fixed,time,hifi,macros -- -D warnings` — clean
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps` (default features, no f16) — clean **(F016-link tripwire)**
- [x] `RUSTDOCFLAGS="-D warnings" cargo +nightly doc --no-deps --features fixed,time,hifi,macros,f16` — clean
- [x] `scripts/check_readme_mirror.sh` — passes
- [x] `scripts/check_pii.sh` — passes
- [x] `cargo fmt --all -- --check` — clean

## Local review (2026-05-19)

**Branch:** plan/2026-05-19-04
**Commits:** 5 (origin/main..plan/2026-05-19-04)
**Reviewer:** Codex (`codex review --base origin/main`)
**Prompt fingerprint:** AGENTS.md=b5f7584f2875c10abb637c9b483b4c7e0cb37891 calibration=missing

---

The code changes build in the checked stable feature set, but the updated README API prose documents nonexistent generic trait syntax and misidentifies `ConnK`, which would mislead users writing bounds.

Review comment:

- [P3] Use associated-type syntax for Conn traits — README.md:153-160
  In this README API explanation, the traits are shown as `ConnL<A, B>`, `ConnR<A, B>`, and `ConnK<A, B>`, and `ConnK` is described like a marker struct, but the actual API in `src/conn.rs` defines associated-type traits (`ConnK` is the super-trait implemented by generated zero-sized marker structs). Readers copying the documented `T: ConnL<A, B>` style will get compile errors; spell these as `ConnL<A = A, B = B>` / `ConnR<...>` and describe markers as structs implementing `ConnK`.


<!-- gh-id: 4325599774 -->
### copilot-pull-request-reviewer[bot] — COMMENTED ([2026-05-20 06:05 UTC](https://github.com/cmk/connections/pull/9#pullrequestreview-4325599774))

## Pull request overview

This pull request applies a small set of documentation and naming-hygiene fixes: it updates the README badges and improves the README’s explanation of 2-kinded connections, while also consolidating the `F016` alias to a single source of truth and adjusting f16-related imports/paths accordingly. It also adds documentation clarifying the intentionally separate per-host fixed-point alias namespace.

**Changes:**
- Replace README crates.io/docs badges with non-404 placeholders and tighten the 2-kinded connections prose/trait explanations.
- Deduplicate the `F016` type alias (keep it in `src/float.rs`) and update dependent modules/imports; fix f16-only `shift16_f16` call sites.
- Document the per-host `fixed::iN`/`fixed::uN` alias layer and cross-reference it from the crate-level naming docs.

### Reviewed changes

Copilot reviewed 9 out of 9 changed files in this pull request and generated 2 comments.

<details>
<summary>Show a summary per file</summary>

| File | Description |
| ---- | ----------- |
| `README.md` | Swap badge URLs and reformat/clarify the “2-kinded connections” section. |
| `src/lib.rs` | Add crate-level naming docs clarifying the fixed per-host alias namespace. |
| `src/fixed.rs` | Add module docs explaining the per-host `I###`/`U###` alias layer and its non-collision with Conn naming. |
| `src/float.rs` | Fix f16-gated call sites to reference `crate::core::f016::shift16_f16`. |
| `src/core/f032.rs` | Import `F016` from `crate::float` and update f16 Conn docs to match the alias location. |
| `src/core/f064.rs` | Import `F016` from `crate::float` instead of `super::f016`. |
| `src/core/f016.rs` | Remove the duplicate `pub type F016` and update module docs to point at `crate::float::F016`. |
| `doc/plans/plan-2026-05-19-04.md` | Add a plan document describing and verifying the intended changes. |
| `doc/reviews/review-00009.md` | Add the PR audit/review record. |
</details>







<!-- gh-id: 3271564948 -->
### Copilot on [`README.md:138`](https://github.com/cmk/connections/pull/9#discussion_r3271564948) (2026-05-20 06:05 UTC)

The inline-code example `pub const Conn<A, B, K>` reads like a constant named `Conn`, which isn’t valid Rust and may mislead readers trying to mirror the pattern. Consider spelling this as `pub const NAME: Conn<A, B, K>` (or `pub const NAME: Conn<A, B, L/R>`) to clarify that the *type* is `Conn<…>` and the constant has its own identifier.


<!-- gh-id: 3271564985 -->
### Copilot on [`src/lib.rs:51`](https://github.com/cmk/connections/pull/9#discussion_r3271564985) (2026-05-20 06:05 UTC)

The alias shape in backticks (`FixedI<host><U_frac>`) doesn’t match the actual fixed-point wrapper type names used elsewhere in the crate (e.g. `FixedI8<U4>` / `FixedU16<U8>`). As written it’s also syntactically ambiguous (missing delimiter between `host` and `U_frac`). Consider rewriting this to a concrete example (like `I004 = FixedI8<U4>`) or a more accurate schematic that matches the real type constructors.


<!-- gh-id: 3271619613 -->
#### ↳ cmk ([2026-05-20 06:18 UTC](https://github.com/cmk/connections/pull/9#discussion_r3271619613))

Fixed — switched the Note to `pub const NAME: Conn<A, B, K>` and `pub struct NAME` so it's syntactically unambiguous.

<!-- gh-id: 3271620186 -->
#### ↳ cmk ([2026-05-20 06:18 UTC](https://github.com/cmk/connections/pull/9#discussion_r3271620186))

Fixed — replaced the ambiguous `FixedI<host><U_frac>` schematic with concrete examples (`fixed::i008::I004 = FixedI8<U4>` / `fixed::u016::U008 = FixedU16<U8>`) that match the actual wrapper type-constructor shape.
