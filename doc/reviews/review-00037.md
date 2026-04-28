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
  the missing item-level doc on `Extended<T>`; add a handful of
  doctests where prose alone is hand-wavy (`I128I064` saturation,
  `U008I016` synthetic-marker asymmetry, `fixed::i8::I008I004` frac-level
  reduction, `round` / `truncate` / `median` bracket-picking).
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

## Local review (filled in by /sprint-review)
