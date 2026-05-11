# MR !36 — `property` → `prop` cleanup

## Summary

- Renames `property` module to `prop`. All `crate::property::*`
  / `connections::property::*` paths become `crate::prop::*` /
  `connections::prop::*`.
- Splits `prop::laws` into `prop::conn` (Galois-connection laws,
  cast lifter laws) and `prop::lattice` (Heyting / Coheyting /
  Bi-Heyting / Boolean laws). The 700-line single-file laws.rs
  becomes two focused files.
- Renames `cast_foo` → `conn_foo` predicates. The `cast_*` prefix
  was a leftover from the `conn::cast` submodule that was folded
  into `conn` in MR !34; every predicate that exercises a `Conn`
  is now `conn_*`.
- Renames `symmetric_foo` → `biheyting_foo` predicates. The trait
  is `Symmetric`, but the laws characterize bi-Heyting algebras;
  matches the existing `biheyting_neg_le_coneg`.
- Alphabetizes all predicate definitions within `prop::conn` and
  `prop::lattice`. Drops the ad-hoc section dividers
  (Heyting / Coheyting / etc.).

Plan: `doc/plans/plan-2026-04-27-09.md`.

## Test plan

- [ ] `cargo build` (stable, default features) — clean.
- [ ] `cargo test --workspace` (stable) — all green (counts
      unchanged from main: 1119 lib + 1481 integration + 31
      doctests).
- [ ] `cargo clippy --all-targets -- -D warnings` (stable) — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `cargo doc --no-deps --features testing --document-private-items`
      with `RUSTDOCFLAGS=-D warnings` — clean.
- [ ] `cargo +nightly test --features f16` — all green.

## Local review (2026-04-27)

**Branch:** sprint/prop-cleanup
**Commits:** 6 (origin/main..sprint/prop-cleanup)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All six commits use conventional prefixes (`task:`, `plan:`, `doc:`).
Each commit is well-scoped and atomic per the plan's T1–T4 split,
plus the renumber commit. No merge commits.

### Code Quality

`#![forbid(unsafe_code)]` preserved at `src/lib.rs:144`. No dead
code or clippy issues introduced. The `use crate::prop::{conn as
conn_laws, lattice as lattice_laws};` aliasing pattern is justified
— it disambiguates `crate::prop::conn` from the `crate::conn` type
module without forcing every call site to write
`crate::prop::conn::conn_xxx`.

### Test Coverage

Predicate count after the split: **31 in `prop::conn` + 65 in
`prop::lattice` = 96**, exactly the pre-split count from the
original `laws.rs`. No predicates lost. All callers (`src/conn.rs`,
`src/lattice.rs`, `src/fixed/`, `src/float/`, `src/time/`,
`tests/fixed_u*_galois.rs`) are updated. Ignored doctests went
from 3 to 4 — the new ignore is the proptest-block example in the
new `prop::conn` module doc, which correctly mirrors the existing
ignore in `prop.rs`.

### Plan Conformance

T1, T2, T3, T4 all implemented per the plan. Predicate partition
matches the plan table exactly (heyting/coheyting/biheyting/
boolean/symmetric → lattice; conn/cast → conn). Renames applied
without name collisions. Alphabetization verified by byte-order
sort across both files.

### Risks

None. Spot-checked: `conn_galois_l`, `conn_upper1_id_unit`
(ex-`cast_upper1_id_unit`), `biheyting_involution`
(ex-`symmetric_involution`), `heyting_adjunction` all present with
identical bodies. The aliasing pattern (`conn_laws`/`lattice_laws`)
creates no identifier conflicts.

### Recommendations

**Must fix before push:**

1. **`Cargo.toml:46` — stale `connections::prop::laws` path.**
   After T2, `prop::laws` no longer exists. Fixed: comment now
   reads `connections::prop::conn` and `connections::prop::lattice`.

2. **`src/prop/lattice.rs:35` — stale `// ── Heyting (h0–h17) ─`
   divider.** Alphabetical order makes the section header wrong
   (the first fn is `biheyting_coneg_neg_convl`, not Heyting).
   Per plan T4, dropped.

3. **`src/prop/conn.rs:32` — "cast-lifter laws" wording.** T3
   renamed `cast_*` → `conn_*` specifically because "cast" was the
   wrong vocabulary. Fixed: now reads "lifter laws".

4. **`src/prop/conn.rs:38` — stale `// ── Adjoint laws ─`
   divider.** Same issue as item 2 — alphabetical order makes the
   section claim wrong (first fn is `conn_ceiling1_id_kernel`, a
   lifter law). Per plan T4, dropped.

All four addressed in a follow-up `fix:` commit.

**Follow-up (future work):**

- `prop::arb` alphabetization deferred per plan; no action.
