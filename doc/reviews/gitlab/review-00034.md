# MR !34 — Pre-publish cleanup: namespace flatten + drop `half`

## Summary

- Drops `bf16` support entirely (`B016`, `F032B016`, `F064B016`,
  `arb_bf16`, `extended_float_bf16`, the bf16 ULP machinery and
  tests). `bf16` has no std stabilization path; downstream crates
  that need bfloat16 can build it directly atop `Conn`.
- Replaces `half::f16` with std `f16` behind a new `f16` cargo
  feature. Stable rustc skips the f16 path entirely; opting into
  `--features f16` requires nightly (`#![cfg_attr(feature = "f16",
  feature(f16))]` per RFC #116909). Removes the `half` crate from
  `[dependencies]`; `half` remains transitively via `fixed`.
- Flattens `src/conn/<sub>/` up one level: `int` (formerly
  `conn::std`, renamed to avoid std-prelude shadowing), `fixed`,
  `float`, `time`. Folds `src/conn/cast.rs` into `src/conn.rs` —
  the cast helpers (`ceiling`, `floor`, `upper`, `lower`,
  `median`, `round`, `truncate`, `interval`, `midpoint`, plus
  `*1`/`*2` lifters) become free functions sibling to `Conn`.
  Crate-root re-exports unchanged (`connections::ceiling` still
  works).
- Inside `float/`, applies the RHS-wins placement rule: `F064F032`
  moves from `f64.rs` to `f32.rs`; `F032F016` / `F064F016` /
  `F016` move into a new feature-gated `f16.rs`; the empty
  `f64.rs` is deleted.
- Picks up the cast cleanup work from main MR !32 (drop
  `maximize` / `minimize`, F064F032 + π doctests, "Behavior on
  edge inputs" section) and re-applies it to the new `conn.rs`.

Plan: `doc/plans/plan-2026-04-27-08.md`.

## Test plan

- [ ] `cargo build` (stable, no features) — clean.
- [ ] `cargo test --workspace` (stable, no features) — all green.
- [ ] `cargo clippy --all-targets -- -D warnings` (stable) — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `cargo doc --no-deps` (stable) — clean.
- [ ] `cargo +nightly build --features f16` — clean.
- [ ] `cargo +nightly test --features f16` — all green
      (including gated f16 tests).
- [ ] `cargo +nightly doc --no-deps --all-features` — clean.
- [ ] `cargo tree -e normal | grep -i half` shows half only via
      fixed (transitive), not as a direct dep.
- [ ] Smoke imports of `connections::int::i16::I008I016`,
      `connections::float::f32::F064F032`, and root-level
      `connections::ceiling` compile.

## Local review (2026-04-27)

**Branch:** sprint/prepublish-cleanup
**Commits:** 5 (origin/main..sprint/prepublish-cleanup)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All five commits carry conventional prefixes. The sequencing
(T1 `feat:` → T2 `feat:` → T3 `task:` → `plan:` → `fix:`) matches
the plan. Each commit leaves the tree buildable. Two minor labels:
the T1 commit uses `feat:` for a removal (could be `task:`); the
plan commit uses a non-standard `plan:` prefix (the convention
table lists `feat/fix/doc/test/task/debt`). Low-priority.

### Code Quality

`#![forbid(unsafe_code)]` preserved at `src/lib.rs:144`. No unsafe
code added.

The `impl_float_ext!` macro in `src/float.rs` was rewritten to use
absolute paths (`$crate::float::ExtendedFloat<$T>`,
`::core::cmp::Ordering`) so the `impl_float_ext!(f16)` invocation
in the child `src/float/f16.rs` resolves correctly. Trait-impl
behavior is identical to the original — only path qualifications
changed.

### Test Coverage

Stable lib tests: 1119 passing (was 1117 on main pre-rebase; +2
from the new arithmetic-impl tests carried in by main's MR !32).
Integration tests: 1481 passing across 15 suites. Doctests: 31
passing.

Nightly + `--features f16`: 1159 lib tests passing (the +40
f16-gated tests fire on the gated path).

The cast cleanup work from main MR !32 (drop `maximize` /
`minimize`, F064F032 + π doctests, "Behavior on edge inputs"
section, Tier-1 review fixes) was preserved through the
cast.rs → conn.rs fold. The new conn.rs reflects main's final
cast.rs.

### Plan Conformance

T1 (drop bf16): complete. No bf16 references in `src/` or
`tests/`. Doc references in `lib.rs` and `README.md` updated.

T2 (gate f16, drop half): complete. `half` removed from
`[dependencies]`; transitive presence via `fixed` is documented.
`#![cfg_attr(feature = "f16", feature(f16))]` activates the
nightly path. Doctests prepend `# #![feature(f16)]` so they
compile under `--features f16`.

T3 (flatten + rename + RHS-wins): complete. `int` (renamed from
`std`), `fixed`, `float`, `time` are all top-level. `cast.rs`
folded into `conn.rs`. `F064F032` lives in `float::f32`;
`F032F016` / `F064F016` / `F016` live in feature-gated
`float::f16`; `float::f64.rs` deleted. Cross-references in
`lib.rs`, `README.md`, `CLAUDE.md` updated.

### Risks

The cast.rs → conn.rs fold preserves all the cast cleanup from
main MR !32, including the dropped `maximize` / `minimize`. The
`median` body uses `c.ceil((p, q))` / `c.floor((p, q))` directly
(per ba56793). `cast_maximize_eq_ceiling` / `cast_minimize_eq_floor`
predicates are gone from `property/laws.rs`.

The `[package.metadata.docs.rs]` config was changed from
`all-features = true` to `features = ["testing"]` (commit
`61c932f` addressing the must-fix from the original review). This
prevents docs.rs from trying to enable the nightly-gated `f16`
feature on stable rustc, at the cost of f16-gated items not
rendering on docs.rs until std `f16` stabilizes.

### Recommendations

**Must fix before push:** none remaining. The two flagged in the
original review (docs.rs config, README stale paths) are
addressed in `61c932f`.

**Follow-up (future work):**

- `#[cfg_attr(docsrs, doc(cfg(feature = "f16")))]` annotations on
  the f16-gated public items, so users browsing nightly-built
  docs see the gate badge.
- Re-export `connections::Conn` at the crate root for ergonomic
  `use connections::Conn;` (currently `connections::conn::Conn`).
- Stale `conn::std::*` / `conn::fixed::*` strings in
  `tests/{int,fixed}_*.rs` module-level `//!` doc comments — easy
  mechanical update, cosmetic only.
