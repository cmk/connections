# PR #19 — Make `view_l`/`view_r` public; retire the double-swap view idiom

## Summary

`crate::conn` already shipped `view_l(t)` / `view_r(t)` — the named
spelling of a triple marker's direct view, defined as the marker's
polarity swaps composed into a round trip (`t.swap_l().swap_r()` /
`t.swap_r().swap_l()`). Newer predicate code used them, but they were
`pub(crate)`, so ~90 older call sites — across doctests, `tests/`, and
the exported `law_battery!` macro — still wrote the raw double swap. The
`conn.rs` module doc even called `view_l(t)` "the public spelling",
which wasn't true. This PR finishes the migration.

### What changed

- **`view_l` / `view_r` are now `pub`.** Small public-API addition that
  makes the module doc's "public spelling" claim real and lets external
  crates (and doctests) name a marker's view directly.
- **~70 marker-receiver double swaps → `view_l(&X)` / `view_r(&X)`**
  across doctests and `tests/`, keyed by an explicit skip-list so
  nothing behaviour-changing is touched; 26 doctest blocks gained a
  `use connections::conn::{view_l, view_r};`.

### What deliberately stays a double swap

Each for a concrete reason:

- the `view_l` / `view_r` **definitions** (replacing them is infinite
  recursion);
- the exported **`law_battery!` macro** — it is documented to accept
  raw one-sided `Conn` **values** (e.g. `conn_r!` output with
  `subset: r_only`), and the double swap is the *uniform* spelling that
  is a view on a marker and an identity on a raw `Conn`; `view_l` /
  `view_r` would compile only for markers, breaking documented
  downstream support (see below);
- the `swap_involutive_*` **law bodies** and the `swap_involution`
  law-battery test — they *verify* the equivalence that justifies
  `view_l`, and their receiver is a `Conn` **value** (which does not
  impl `ConnL` / `ConnR`);
- the swap round-trip **unit tests** (`Conn` value receiver);
- **const positions** in `compose_l!` / `compose_r!` / `lift_l!` /
  `lift_r!` — `view_l` is generic over the `ConnL` *trait* method and so
  cannot be `const`; the inherent `const fn swap_l` / `swap_r` can, and
  const composition needs them.

### Two value-vs-marker traps the migration surfaced

Both come from the same fact — `X.swap_l().swap_r()` is a *view* on a
marker but an *identity no-op* on a raw one-sided `Conn` value, whereas
`view_l(&X)` compiles only for markers:

1. `unsigned_nz_props` in `tests/fixed/nz_iso.rs` drives a one-sided
   `Conn` value (`U###N###` — only `galois_l` holds at the unsigned
   bottom plateau); the two sites now use the value directly. The
   compiler (E0277) caught it.
2. The exported `law_battery!` macro must keep the double swap so
   downstream `l_only` / `r_only` / `iso_only` batteries over raw
   `conn_l!` / `conn_r!` consts still compile — reverted to the double
   swap (caught in local review).

### Verification

- `cargo test --features fixed,time,hifi,uhlc,proptest,macros` — 1925
  lib + 9 + 1 integration + 90 doctests, 0 failed.
- `cargo test --doc` (default features) — 44 passed, 0 failed.
- `cargo clippy --all-targets … -D warnings` — clean (incl. the `pub`
  bump).
- `RUSTDOCFLAGS=-D warnings cargo doc …` — clean (new intra-doc links).
- `cargo fmt --check` — clean.
- Remaining `swap_l().swap_r()` / `swap_r().swap_l()` code sites: exactly
  the 12 documented keep-set entries.

### Note

Doc-prose mentions of the idiom were updated by hand (the mechanical
pass had rewritten some into nonsense like `view_l(&c)` on a `Conn`
value). A follow-up will sweep the 3 new double swaps that PR #18's
`extended.rs` `lift_k!` doctest introduces once that PR lands, since
this branch is based on `main`.

## Local review (2026-07-06)

**Branch:** plan/2026-07-06-02
**Commits:** 3 (origin/main..plan/2026-07-06-02)
**Reviewer:** Codex (`codex review --base origin/main`)
**Prompt fingerprint:** AGENTS.md=4563f590caa7dbba5ea9eae973fa59182f1a6470 calibration=missing

---

The exported law_battery! macro regresses documented downstream support for raw one-sided Conn constants in r_only/iso_only subsets. There is also a stray marker that would leak into the generated PR body.

Full review comments:

- [P2] Preserve raw Conn support in law_battery views — src/prop/conn.rs:809-809
  When downstream users pass a one-sided `Conn<A, B, R>` const, such as one emitted by `conn_r!`, to the exported `law_battery!` with `subset: r_only`, this now fails to compile because `view_r(&($c))` requires `$c: ConnR`, and `Conn` values intentionally do not implement `ConnR`. The previous `($c).swap_r().swap_l()` spelling was an identity on raw R-Conn values, matching the macro docs that advertise `Conn<_,_,K>` consts; the analogous `iso_only` `view_l` replacements have the same issue for raw L-Conn constants.

- [P3] Remove stray content marker from PR body — doc/reviews/review-00019.md:70-70
  When `scripts/pr_report.py body 19` extracts the review file's `## Summary` for `gh pr create`, it reads through EOF unless a local-review or gh-id marker appears, so this leftover `</content>` line will be published verbatim in the PR body. Remove the marker from the review file before opening the PR.


<!-- gh-id: 4634242200 -->
### copilot-pull-request-reviewer[bot] — COMMENTED ([2026-07-06 08:49 UTC](https://github.com/cmk/connections/pull/19#pullrequestreview-4634242200))

## Pull request overview

This PR makes the `connections::conn::view_l` / `view_r` helper functions publicly accessible and migrates marker-view call sites from the “double swap” idiom (`swap_*().swap_*()`) to the named helpers across doctests, tests, and documentation, while preserving double-swap usage where required (e.g., raw `Conn` values and `const` contexts).

**Changes:**
- Expose `view_l` / `view_r` as `pub` API in `src/conn.rs`.
- Replace eligible marker-receiver double-swaps with `view_l(&X)` / `view_r(&X)` across doctests and integration tests.
- Update module/docs prose to match the new public spelling.

### Reviewed changes

Copilot reviewed 17 out of 17 changed files in this pull request and generated 2 comments.

<details>
<summary>Show a summary per file</summary>

| File | Description |
| ---- | ----------- |
| tests/macros_feature_smoke.rs | Switch one marker view from double-swap to `view_r(&…)`. |
| tests/fixed/nz_iso.rs | Use `view_l`/`view_r` for marker receivers; keep raw `Conn` value sites as direct calls. |
| src/time/duration.rs | Update doctest to import/use `view_l`/`view_r` helpers. |
| src/time.rs | Update module-level example to use `view_l`/`view_r`. |
| src/prop/conn.rs | Adjust law documentation wording to refer to `view_l` as the named spelling. |
| src/prop.rs | Update downstream-usage docs/examples to use `view_l`. |
| src/lib.rs | Update crate-level docs/examples to use `view_l`. |
| src/hifi/epoch.rs | Update multiple doctests to use `view_l`. |
| src/float.rs | Update docs example to use `view_l`/`view_r`. |
| src/extended.rs | Update docs prose to reference public free functions for cross-crate usage. |
| src/core/u008.rs | Update doctest examples to use `view_l`. |
| src/core/i008.rs | Update doctest examples to use `view_l`. |
| src/core/f064.rs | Update doctest examples to use `view_l`/`view_r`. |
| src/conn.rs | Make `view_l`/`view_r` public and update docs referencing direct views. |
| src/addr/ip.rs | Update doctest examples to use `view_l`/`view_r`. |
| doc/reviews/review-00019.md | Audit-trail review record update. |
| doc/plans/plan-2026-07-06-02.md | Add sprint plan and review notes for the migration work. |
</details>







<!-- gh-id: 3527529501 -->
### Copilot on [`src/conn.rs:526`](https://github.com/cmk/connections/pull/19#discussion_r3527529501) (2026-07-06 08:49 UTC)

The `ConnR` docs suggest using the marker’s inherent `const fn view_r()` in `const` position, but the marker-generated `view_r` is `pub(crate)` (see `conn_k!`/`compose_k!` expansions), so downstream users can’t call it. For `const` usage, the public const round-trip is `M.swap_r().swap_l()` (trait methods and the free `view_r(&T)` helper aren’t const-callable).

<!-- gh-id: 3527529552 -->
### Copilot on [`doc/plans/plan-2026-07-06-02.md:155`](https://github.com/cmk/connections/pull/19#discussion_r3527529552) (2026-07-06 08:49 UTC)

Stray `</content>` marker at EOF looks like an artifact from prompt/docs tooling and shouldn’t be committed to the plan document.

<!-- gh-id: 3527703614 -->
#### ↳ cmk ([2026-07-06 09:19 UTC](https://github.com/cmk/connections/pull/19#discussion_r3527703614))

Fixed — the `ConnR` doc (and its `ConnL` twin, plus the `view_l`/`view_r` helper docs) now direct `const`-position callers to the public double swap `t.swap_r().swap_l()` / `t.swap_l().swap_r()`, and note the inherent `const fn view_r()`/`view_l()` is crate-private so downstream isn't pointed at an uncallable method.

<!-- gh-id: 3527703914 -->
#### ↳ cmk ([2026-07-06 09:19 UTC](https://github.com/cmk/connections/pull/19#discussion_r3527703914))

Fixed — removed the stray `</content>` marker from the end of the plan document.
