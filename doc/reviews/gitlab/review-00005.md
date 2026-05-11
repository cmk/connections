# MR !5 — File tree reorg + FloatExt → ExtendedFloat

## Summary

- Move domain tier files under `src/conn/`: `float.rs`, `fixed.rs`,
  `sample.rs` via `git mv` (history preserved). Fold old
  `src/float_ext.rs` into `src/conn/float.rs` so the `ExtendedFloat`
  type lives next to the float connections that use it.
- Rename `FloatExt` → `ExtendedFloat` crate-wide (100 occurrences
  across source + docs).
- Collapse `src/order.rs` → `src/lattice.rs` with deferred
  trait stubs for `Join`, `Meet`, `Heyting`, `Coheyting`,
  `Symmetric`, `Boolean` alongside the `Ple` implementation.
- Add empty stubs: `src/property.rs` (populated in Sprint C),
  `src/conn/int.rs`, `src/conn/word.rs`.
- Sync `doc/design.md` §"Module structure" to the actual tree and
  update all `lib.rs` doc links to the new `conn::*` paths.

## Test plan

- `cargo build` — clean.
- `cargo test --workspace` — 377 passed, same as main.
- `cargo clippy --all-targets -- -D warnings` — clean.
- `ls src/` — matches target: `lib.rs`, `conn.rs`, `conn/`,
  `extended.rs`, `lattice.rs`, `property.rs`.
- `ls src/conn/` — `float.rs`, `fixed.rs`, `sample.rs`, `int.rs`,
  `word.rs`.
- `grep -r FloatExt src/` — zero hits.
- `grep -r 'crate::order' src/` — zero hits.
- `grep -r 'crate::float_ext' src/` — zero hits.

Deferred to their own sprints:
- `Join / Meet / Heyting / ...` implementations.
- `src/conn/int.rs` / `word.rs` content.
- `src/property.rs` population (Sprint C).
- `cargo fmt --all` absorbing the rustfmt drift.

## Local review (2026-04-23)

**Branch:** sprint/file-tree-reorg
**Commits:** 7 (origin/main..HEAD, post Tier-1 fix commit)
**Reviewer:** Claude (sonnet, independent)

---

### Findings

Tier-1 raised 1 must-fix + 2 should-fix + 3 follow-ups. Disposition:

- **[must-fix] Push-back.** Plan Review bullet describing the T1+T2
  import fixup as `crate::float_ext::FloatExt` →
  `crate::conn::float::FloatExt` is factually correct for that
  commit's state. The rename to `ExtendedFloat` happened in a later
  commit (T3). The audit trail is internally consistent; the
  reviewer misread the chronology. No change.
- **[should-fix] Fixed.** `doc/design.md §Connections involving
  floats` described `Conn<ExtendedFloat<f64>, ExtendedFloat<f32>>`
  as if current, but `f64_f32()` still returns `Conn<f64, f32>`.
  Added a "Status" callout marking the shape as aspirational.
- **[should-fix] Fixed.** `src/lib.rs` doc link
  `[`conn::float::ExtendedFloat<f64>`]` could trigger a `cargo
  doc` warning on some compiler versions about unresolved generic
  path components. Rewrote as `[`ExtendedFloat<f64>`](conn::float::ExtendedFloat)`.
  Caught one more stale link in `src/conn/sample.rs` module doc
  (`crate::fixed` → `crate::conn::fixed`) along the way. `cargo
  doc --no-deps` now emits zero warnings.
- **[follow-up] Fixed.** `arb_float_ext_f64` in `conn/fixed.rs`
  tests was a FloatExt-name vestige. Renamed to
  `arb_extended_float_f64` (no public API change; `#[cfg(test)]`
  only).
- **[follow-up] Deferred.** PartialOrd match-arm ordering in
  `src/conn/float.rs` (symmetric pairs interleaved instead of
  grouped). Correct but non-idiomatic. Leave for a future touch.
- **[follow-up] Deferred.** Commit-message-should-note-history-loss
  for `float_ext.rs` fold. Can't amend past commits cleanly; the
  plan's Review section documents this instead.

### Plan Conformance

| Task | Status |
|------|--------|
| T1 git mv tier files | ✓ |
| T2 fold float_ext into conn/float | ✓ (history loss noted in plan Review) |
| T3 FloatExt → ExtendedFloat rename | ✓ (99 occurrences) |
| T4 order.rs → lattice.rs + stubs | ✓ |
| T5 property.rs + conn/int.rs + conn/word.rs stubs | ✓ |
| T6 lib.rs + design.md + build | ✓ (377 tests, clippy clean, zero doc warnings) |

### Recommendations

**Must fix before push:** None (must-fix was a push-back).

**Follow-up:** Already tracked above and in the plan Review.
