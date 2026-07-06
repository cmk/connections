# PR #18 — Convert `ignore` doctests to real, tested examples

## Summary

Fourteen doc examples were fenced ` ```ignore `, so rustdoc rendered each
with the crossed-circle "This example is not tested" badge on docs.rs. This
PR removes every one of them — no library code changes, docs only — by
turning the examples into real, compiled-and-run doctests where that is
possible, and into honest ` ```text ` illustrations where it is not.

CI and `pre-push` already run doctests with
`--features fixed,time,hifi,uhlc,proptest,macros`, so a converted example is
exercised on every push. All nine real conversions are additionally written
to compile under **default** features, so plain `cargo test` (a fresh
zero-setup checkout) stays green: **53 doctests pass with 0 ignored** on
default features, **99 pass with 0 ignored** on the full set.

### Nine → real doctests

- **`extended.rs`** — `lift_l!`, `lift_r!`, and the const-init
  `lift_l!`-into-`compose_l!` combo. Pure-core; they already carried
  `assert_eq!`s and just needed the `ignore` dropped.
- **`extended.rs` `lift_k!`** — rewritten onto a pure-core identity iso and
  the **public** double-swap view spelling (`M.swap_l().swap_r().ceil(…)`).
  The old example called `.ceil()` directly on the lifted marker, which has
  no such inherent method, and reached the view through the `pub(crate)`
  `view_l` — so it could never have compiled from a doctest.
- **`conn.rs`** — `compose_k!`, `conn_k!`, `iso!`, `conn_l!`, `conn_r!`.
  Hidden (`#`-prefixed) `use`/stub lines make each self-contained. The
  `compose_k!` example was moved off the nightly-only `f16` chain
  (`F064F016 = F064F032 ∘ F032F016`) onto the real, stable
  `F064U008 = F064F032 ∘ F032U008` composition.

### Two bugs the `ignore` fences were hiding (gardener rule)

- **`conn_r!`** — the example bound `inner: u_to_i, floor: i_to_u`, the
  reverse of `Conn::new_r(inner: fn(B)->A, floor: fn(A)->B)`. It would not
  compile. Corrected to `inner: i_to_u, floor: u_to_i` (names now match the
  actual `i8→u8` / `u8→i8` directions).
- **`lift_k!`** — the `.ceil()`/`.floor()`/`.upper()`-on-a-marker calls
  described above. Fixed as part of the rewrite.

### Five → ` ```text `

These cannot become in-crate doctests without either enabling a disabled
feature (which would break default `cargo test`) or reaching a crate-private
path. Rendered as `text`, they lose the false "tested" badge and syntax
highlighting but keep their illustrative content:

- **`lib.rs`** — the `fixed::iNNN` qualified-import disambiguation idiom
  (`fixed`-feature only).
- **`extended.rs`** — the marker combo that composes through the
  `pub(crate)` `view_l`; an external doctest can't call it.
- **`prop.rs` / `prop/conn.rs`** — the `proptest!` and `law_battery!`
  downstream idioms. Both need the gated `arb` module and expand to
  `#[test]` items that don't survive rustdoc's `fn main` wrapper.
- **`prop/lattice.rs`** — `heyting_adjunction` over a placeholder `MyType`.
  The crate ships the lattice *traits* with no concrete instances, so there
  is no in-crate `Heyting` type to demonstrate against.

### Verification

- `cargo test --features fixed,time,hifi,uhlc,proptest,macros` — 2664 + 9 +
  1 unit/integration + 99 doctests, 0 failed.
- `cargo test --doc` (default features) — 53 passed, 0 ignored.
- `cargo clippy --all-targets … -D warnings` — clean.
- `RUSTDOCFLAGS=-D warnings cargo doc …` — clean.
- `grep -rc '```ignore' src/` — 0.

## Local review (2026-07-06)

**Branch:** plan/2026-07-06-01
**Commits:** 3 (origin/main..plan/2026-07-06-01)
**Reviewer:** Codex (`codex review --base origin/main`)
**Prompt fingerprint:** AGENTS.md=4563f590caa7dbba5ea9eae973fa59182f1a6470 calibration=missing

---

The patch is docs-only, but several newly real doctests present compiling connections that violate the Galois laws the macros document, and the PR body file contains a leaked transcript tag. These are accuracy/workflow issues the author should address before merging.

Full review comments:

- [P2] Use a lawful triple in the `conn_k!` doctest — src/conn.rs:1088-1088
  With this doctest's `narrow` defined as an `as` cast, the documented `Demo : i8 => i16` is not an adjoint triple: for example `a = 0_i8` and `b = 128_i16` make `ceil(a) <= b` true while `a <= inner(b)` is false because `inner(128)` wraps to `-128`. Since `conn_k!` cannot enforce the laws, the public example should use a lawful pair rather than a merely type-correct one.

- [P2] Make the `conn_l!` doctest lawful at `PosInf` — src/conn.rs:1224-1227
  For the documented `Extended<i64> => i64` pair, the `PosInf` case breaks the left Galois law: with `a = Extended::PosInf` and `b = i64::MAX`, `ceil(a) <= b` is true after saturation but `a <= inner(b)` is false because `inner(b)` is finite. This example now compiles as a real doctest, so it should demonstrate a lawful L-Conn instead of a saturating collapse that cannot satisfy the advertised contract.

- [P2] Replace wrapping casts in the `conn_r!` doctest — src/conn.rs:1262-1267
  For negative `i8` inputs the hidden `i_to_u` helper wraps instead of preserving order, so the shown `u8 => i8` R-Conn violates `inner(b) <= a ⟺ b <= floor(a)`; e.g. `a = 0_u8`, `b = -1_i8` gives `b <= floor(a)` true but `inner(b) <= a` false because `inner(-1)` is `255`. Use a lawful right adjunction rather than plain `as` casts in the macro's public example.

- [P3] Remove the leaked transcript tag from the PR body — doc/reviews/review-00018.md:69-69
  `scripts/pr_report.py body` includes every line after `## Summary` until a local-review or GitHub marker, so this raw `</content>` line will be copied into the GitHub PR body. It looks like an agent transcript artifact and should be removed before the review file is used to open or update the PR.

