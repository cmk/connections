# MR !37 — README & docs polish for 0.1 crates.io release

## Summary

- Reorder + reframe `README.md`: lift "What is a Galois connection?" to
  h2, add a new `How connections work` section walking through three
  `Ordering ↔ bool` examples (mirroring the Haskell README), inline an
  ASCII Galois diagram in place of the broken `img/` reference, fix the
  stale Layout tree, add an Installation section.
- Fill the Tier-1 doc gap: extend the macros in `src/int/` and
  `src/fixed/` to emit per-const `#[doc]` attrs, eliminating the 258
  currently-undocumented `pub const Conn<…>` declarations.
- Mirror the Laws table from README into `src/conn.rs` module doc; add
  the missing item-level doc on `Extended<T>`; add module-level
  worked-example doctests for `int::i64::I128I064` (saturation),
  `int::i16::U008I016` (synthetic-marker asymmetry), and
  `fixed::i8::I004I000` (frac-level reduction). The `round` /
  `truncate` / `median` free fns in `conn.rs` already had `# Examples`
  blocks pre-MR, so they're not re-touched here.
- Add a `pages` job + `deploy` stage to `.gitlab-ci.yml` so rustdoc
  ships to GitLab Pages on every `main` push.

## Test plan

- [ ] `RUSTDOCFLAGS=-D warnings cargo doc --no-deps --features testing` clean
- [ ] `cargo test --doc` green
- [ ] `cargo test --workspace` green
- [ ] `cargo clippy --all-targets -- -D warnings` clean
- [ ] `cargo package --no-verify` produces a clean `.crate`; spot-check that
      `img/` is excluded and `README.md` is bundled
- [ ] After merge to `main`, the `pages` CI job populates
      `https://cmk.gitlab.io/connections/connections/` successfully
- [ ] Manual render check: open the new docs locally, verify the ASCII
      diagram, the three-example walk, and per-const summaries on
      `connections::int::i32::I008I032`, `connections::fixed::u8::U008U004`,
      etc.

## Local review (2026-04-27)

**Branch:** `sprint/docs-0.1-release`
**Commits:** 6 (origin/main..sprint/docs-0.1-release)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All six commits carry conventional prefixes (`plan:`, `doc:`, `task:`),
are under 72 characters, and each touches only the concern named in
its subject. The ordering is logical: plan → README → fixed-point
macros → conn/extended/int → Pages job → Cargo.toml exclusion. No
hygiene issues.

### Code Quality

No unsafe code; `#![forbid(unsafe_code)]` intact. Fixed-point macro
doc strings emit the correct pattern (matching the int-macro shape).
`#[rustfmt::skip]` placement before the `#[doc]` inside the macro
body is the only way to suppress rustfmt there.

`Extended<T>` item doc is accurate and readable. `src/conn.rs` Laws
table cross-references all nine predicates plus `conn_floor_le_ceil`;
every name cited exists in `src/prop/conn.rs`. Intra-doc links resolve.

**Q notation in `src/fixed/i8.rs` doctest comments was wrong.**
`FixedI8<U4>` is Q3.4 (not Q0.4); `FixedI8<U0>` is Q7.0 (not Q4.0).
Fixed in this round.

### Test Coverage

The diff adds no new proptest properties — correct for a docs-only
sprint. Existing suite is unchanged.

`int/i64.rs` doctest (`I128I064` saturation): all four assertions
correct. `int/i16.rs` doctest (`U008I016` widening): mirrors the
existing spot-check tests. `fixed/i8.rs` doctest (`I004I000`):
assertions correct (only the Q labels in comments needed the fix
above).

### Plan Conformance

| Task | Status |
|------|--------|
| T1 ASCII diagram | Done |
| T2 Section reorder, three Ordering↔bool examples, Installation | Done |
| T3 Layout tree fixed | Done |
| T4 ONELINER fixed-point macros | Done — all 9 files |
| T5 `Extended<T>` item doc | Done |
| T6 Laws mirror in `src/conn.rs` | Done — 9 + 1 predicates verified in `prop/conn.rs` |
| T7 Doctests: I128I064, U008I016, I004I000 | Done (plan said `I008I004`, actually `I004I000`; same file) |
| T7 Doctests: round, truncate, median | **Dropped** — pre-existing `# Examples` already cover them |
| T8 Pages CI | Done — matches plan YAML |
| T9 Smoke test | Passed |

`pages` job uses `--features testing` as planned. `img/example.png`
stays in the repo; `/img` added to `Cargo.toml` `exclude`. Plan
Review section was a placeholder; filled in this round.

### Risks

No TODOs or stubs. The README's three Ordering↔bool doctest blocks
each define their own `ORDBIN`/`BINORD` consts in isolated harnesses;
no symbol collision risk. ASCII diagram glyphs (U+2190–U+2194,
U+21B0, U+21B3) are all in BMP — no encoding risk.

The `pages` job's `cargo doc` invocation differs from the `doc`
check job's (no `--document-private-items`, no `-D warnings`). Stage
ordering ensures `pages` won't run if `doc` fails, but the two
commands have slightly different surface areas. Logged as follow-up
in the plan's Review section; not a 0.1 blocker.

The bridge sentence after README Example 3 mentions
`interval`/`round`/`truncate` working on every `Conn<A, B>`.
`Ordering` doesn't `impl Sub`, so a reader trying these on the
example `ORDBIN` would get a trait-bound error. Not blocking,
sharpening logged as follow-up.

`cargo publish` readiness: `description`, `license`, `readme`,
`repository`, `keywords`, `categories` set; `Cargo.lock` committed;
`version = "0.1.0"`. No blockers.

### Recommendations

**Must fix before push:**

1. ~~`src/fixed/i8.rs` Q labels~~ — fixed in this round.
2. ~~`doc/plans/plan-2026-04-27-11.md` Review section~~ — filled in.
3. ~~`doc/reviews/review-00037.md` summary bullet on round/truncate/median~~ — corrected.

**Follow-up (future work):**

- Add Pages URL to README Links once the first deploy is observed working.
- Sharpen the bridge sentence after README Example 3 to scope
  `interval`/`round`/`truncate` to numeric (`A: Sub`) connections.
- Align the `pages` job's `cargo doc` invocation with the `doc`
  check job's (`--document-private-items`, `RUSTDOCFLAGS=-D warnings`).
