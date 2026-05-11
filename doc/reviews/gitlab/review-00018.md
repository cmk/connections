# MR !18 — Drop `Ple`; adopt `Eq + PartialOrd` as the lawful framework

## Summary

- Replaces the crate-local `Ple` trait (and its 14 hand-coded impls)
  with the standard-library bound `Eq + PartialOrd`. The "broken-
  for-floats" problem turns out to be in `PartialEq` (which Rust
  documents as a *partial* equivalence relation), not in
  `PartialOrd` — and Rust's `Eq: PartialEq` marker trait already
  certifies the reflexivity fix. `ExtendedFloat<T>`'s patched
  `PartialEq` (where `Finite(NaN) == Finite(NaN)` is true) now
  carries an `impl Eq`, so float Conns flow through the law
  machinery via the standard bound. Net new traits in the public
  API: zero.
- Migrates the only raw-float Conn from `pub fn f64_f32() ->
  Conn<f64, f32>` to `pub const F064F032: Conn<ExtendedFloat<f64>,
  ExtendedFloat<f32>>`. Two CLAUDE.md conventions enforced at once:
  Conn becomes a `pub const` (matching every other Conn) and the
  name conforms to the X123Y456 shape. Raw `f32`/`f64` cannot impl
  `Eq` (NaN ≠ NaN under standard `PartialEq`), so the type system
  now rejects raw floats as Conn endpoints — the lawful usage is
  encoded.
- Updates `doc/design.md` ("Why not a custom Preorder trait?" →
  "Why `Eq + PartialOrd` suffices"); amends the cast-accessors plan
  (`plan-2026-04-26-08.md`) to drop the deferred `Pcompare: Ple`
  trait — Sprint B's `pcompare` is now just
  `PartialOrd::partial_cmp`. `f128` / `f16` cross-tier conns
  (`F128F064`, `F032F016`, etc.) remain deferred behind Rust 1.85's
  toolchain pin.

## Test plan

- [ ] `cargo test --workspace` — **1526 unit tests**, 11 doctests pass; 0 failed; 0 ignored.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo doc --no-deps` — clean.
- [ ] Pre-commit hook green on every commit (cargo test, clippy, check-pii).
- [ ] Manual smoke: the canonical downstream usage example compiles and runs:
      ```rust
      use connections::conn::float::{F064F032, ExtendedFloat};
      let x = ExtendedFloat::Finite(1.5_f64);
      let y = F064F032.ceil(x);     // → ExtendedFloat::Finite(1.5_f32)
      let _back = F064F032.inner(y);
      ```
- [ ] Compile-time negative test: `laws::conn_galois_l(&some_conn,
      1.0_f64, 2.0_f32)` fails to compile with a diagnostic naming
      the missing `Eq` bound — the type system now refuses raw float
      Conn endpoints.
- [ ] No `Ple` references remain in `src/`:
      `git grep -nE '\bPle\b|\.ple\(' src/` returns empty.

## Local review (2026-04-26)

**Branch:** sprint/drop-ple-eq-partialord
**Commits:** 6 (origin/main..sprint/drop-ple-eq-partialord)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Six commits, linear history, no merge commits. All conventional
subjects ≤72 chars (longest is the bde8407 `task: Migrate ...`
at 65 chars). Each commit's stated verification condition is
consistent with the build gate.

### Code Quality

**No unsafe code.** `#![forbid(unsafe_code)]` at `src/lib.rs:144`.

**Ple references.** `git grep -nE '\bPle\b|\.ple\(' src/` returns
empty. Clean.

**Raw-float Conn endpoints.** No remaining `Conn<f32, ...>` or
`Conn<f64, ...>` in source — only one comment hit in `src/conn.rs`.

**Stale module doc — fixed in this round.** `src/conn/float.rs:21-25`
formerly said wrappers were "aspirational"; rewritten to describe
`F064F032` as the live float Conn.

**Plan T6 number — fixed in this round.** `plan-2026-04-26-09.md`
T6 originally named `review-00017.md`; updated to match the actual
file `review-00018.md` (the MR iid bumped past 17 between sprint
planning and execution).

**Plan-08 amendment quality.** The Sprint B prose, dependency
table, and Deferred section are internally consistent: `pcompare`
collapses to `PartialOrd::partial_cmp`; trait deps drop from
`Pcompare (new)` to `none — Eq + PartialOrd (std)`.

**Clippy.** `#[allow(clippy::eq_op)]` on `lattice_reflexive`'s
intentional `x <= x` is correctly placed and documented. The
`!(x <= y)` → `x > y` rewrites in the ULP-walk helpers satisfy
`clippy::neg_cmp_op_on_partial_ord`.

### Test Coverage

**Properties retained.** Full Galois battery (`conn_galois_l/r`,
`conn_closure_l/r`, `conn_kernel_l/r`, `conn_monotone_l/r`,
`conn_idempotent`, `conn_floor_le_ceil`) on `F064F032` in
`src/conn/float.rs`. Cast lifter laws migrated to `ID_EF64` (8
proptests). Lattice partial-order laws run on
`ExtendedFloat<f64>` and `ExtendedFloat<f32>`.

**`conn_floor_le_ceil` — added in this round.** Reviewer flagged
its absence; added at `src/conn/float.rs` proptest block.

**`conn_ulp_bound` — intentionally omitted.** Predicate is
documented (`laws.rs:439-447`) as integer-tier-specific (`rung: F
where F: Fn(B) -> i64`). For float Conns, ULP is bit-level mantissa
increment — a different concept with no clean i64 mapping for
`ExtendedFloat<f32>` (Bot / Top would have to alias to sentinel
ints). Inline comment in float.rs explains the exclusion.

**Test count.** 1527 (+1 from new `floor_le_ceil` proptest beyond
the plan's predicted 1526).

### Plan Conformance

| Task | Status |
|------|--------|
| T1 — `impl Eq for ExtendedFloat<T>` | Done. |
| T2 — `f64_f32 → F064F032` const | Done. |
| T3 — Replace Ple bounds with Eq + PartialOrd | Done. `src/conn/mod.rs` → `src/conn.rs` rename completed. |
| T4 — Delete Ple trait + 14 impls | Done. Zero Ple references remain. |
| T5 — design.md + plan-08 Pcompare deferral | Done. |
| T6 — Sprint plan + review file | Done. T6 prose corrected to name `review-00018.md`. |
| T7 — /sprint-review | This review. |
| T8 — Push (gated) | Pending user approval. |

### Risks

**No new dependencies.** Cargo.toml unchanged.

**Conn-name format.** `F064F032` is 8 chars, both sides 1L+3D
(A123 form per CLAUDE.md). Conforms.

**Module rename.** `src/conn/mod.rs` → `src/conn.rs`. Rust 2018+
style. `pub mod conn;` in lib.rs resolves correctly.

**Downstream callers.** Crate is unpublished; no external impact.

### Recommendations

**Must fix before push** — addressed in this round, no blockers
remaining:

1. ~~`src/conn/float.rs:21-25` stale module doc.~~ Fixed: rewritten
   to describe `F064F032` as the live float Conn.
2. ~~`conn_floor_le_ceil` missing from `F064F032` proptest battery.~~
   Fixed: added. `conn_ulp_bound` correctly excluded (integer-tier
   specific; inline comment explains).

**Follow-up (acceptable now, track for later)**

3. ~~`plan-2026-04-26-09.md` T6 named `review-00017.md`.~~ Fixed:
   updated to match the actual `review-00018.md`.
