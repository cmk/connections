# MR !14 — Standardize Conn-name format + add 128-bit Conns

## Summary

- Renames every public `Conn` constant to a uniform 8-character
  `XnnnYmmm` shape (4 chars per side, smaller-resolution tier on
  the right). Family letters: `FD` (decimal fixed, 2L+2D, e.g.
  `FD12FD06`), `F` (float width, e.g. `F064`), `I` / `U` (signed /
  unsigned int width AND signed / unsigned binary-fixed frac level,
  1L+3D, e.g. `I008I016` / `U008U016`), `S` (sample rate kHz,
  e.g. `S088S044`). Type wrappers renamed for full conformity:
  `Pico`→`FD12`, `Uni`→`FD00`, `S44`→`S044`, etc., plus per-binary-
  module type aliases (`pub type I008 = FixedI8<U8>` etc.). Cross-
  module collisions like `i08::I008I004` vs `i64::I008I004` resolve
  via the standard Rust qualified-import idiom.
- Adds 14 missing 128-bit integer Conns: 5 in `conn::int`
  (`I064I128`, `U008I128`..`U064I128`) and 9 in `conn::uint`
  (`U008U128`..`U064U128`, `I008U128`..`I128U128`). The existing
  `ext_int!` / `uint_uint!` / `int_uint!` macros support i128
  endpoints unchanged; only new invocations and `arb_ext_i64` /
  `arb_ext_u64` strategies were added.
- Adds `conn::fixed::i128` — 15 i128-backed binary fixed-point
  Conns over the frac-level set `{U0, U16, U32, U64, U96, U128}`.
  Stable Rust has no native `i256` to widen through, so the i64-
  style `(bits as i128) * RATIO` pattern is replaced by
  `i128::checked_mul + saturate`; bit-identical outputs to a
  hypothetical i256 implementation. The `I128I000` endpoint is
  intrinsically degenerate (RATIO = 2^128 ∉ i128) — detected via
  `i128::checked_shl(128) == None` and handled in dedicated
  branches; pinned by the `degenerate_max_shift` regression test.

## Test plan

- [ ] `cargo test --workspace` — **1491 passed**, 0 failed, 0 ignored
      (1260 pre-rename + 92 from 128-bit ints + 139 from i128 binary).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean on every
      commit.
- [ ] `cargo doc --no-deps` — clean.
- [ ] Pre-commit hook green on every commit (cargo test, clippy,
      check-pii).
- [ ] Manual smoke: the canonical downstream usage example from the
      lib.rs docstring compiles and runs:
      ```rust
      use connections::conn::fixed::decimal::{FD12, FD06, FD12FD06};
      use connections::conn::sample::{S044, S088, S088S044};

      let p = FD12(1_000_000_000_000);
      let m = FD12FD06.floor(p);                   // → FD06(1_000_000)
      let r = S044::from_sample(7);
      let _ = S088S044.inner(r);                   // → S088 with 14
      ```
- [ ] Qualified-import disambiguation works: `i08::I008I000` and
      `i64::I008I000` co-exist when imported under aliases (the only
      shared conn-name across the two modules — `i08` has frac
      `{U0..U8}`, `i64` has `{U0, U8, U16, U32, U48, U64}`).

## Local review (2026-04-26)

**Branch:** sprint/rename-conn-format
**Commits:** 9 (origin/main..sprint/rename-conn-format)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All 9 commits are present, subjects are conventional and under 72
characters. History is linear (no merge commits). The order
(T1→T2→T3→T4→T5→T6→T7→T10→T11) matches the plan's dependency graph:
renames before docs, docs before new features. No issues.

### Code Quality

**No unsafe code.** `#![forbid(unsafe_code)]` at `src/lib.rs:108`; the
new `src/conn/fixed/i128.rs` is clean.

**Convention adherence.** Every module in the diff touches only
renamed constants, type aliases, and test names. No lints or patterns
outside convention were introduced.

**Feature absence (acceptable).** The plan does not mark
`conn_floor_le_ceil` and `conn_ulp_bound` as required for the i128
binary module. The `props_for_pair!` macro in `i128.rs` runs 9
properties: `galois_l`, `galois_r`, `monotone_l`, `monotone_r`,
`closure_l`, `closure_r`, `kernel_l`, `kernel_r`, `idempotent`.
`floor_le_ceil` is absent from the i128 proptest battery, consistent
with the plan's "injective-`inner` Conns only" qualifier — all i128
`inner` functions saturate and are therefore not injective. Correct.

**Documentation error — `I008I004` does not exist in `conn::fixed::i64`.**
The reviewer flagged this in `src/lib.rs`'s qualified-import doctest
(line 53–58) and in `doc/reviews/review-00014.md`'s test plan (final
checkbox). `conn::fixed::i64` uses frac set
`{U0, U8, U16, U32, U48, U64}` — `U4` is absent, so `I008I004`
(FineFrac=U8, CoarseFrac=U4) does not exist. The shared name between
`i08` and `i64` is `I008I000`. **Fixed in this round** before
appending the review (see commit log).

### Test Coverage

**Test count integrity.** The MR claims 1491 = 1260 + 92 + 139.

- `conn::int`: `ext_int_props!` expands to 7 proptest functions. Old
  count: 12 conns × 7 = 84. New: 20 conns × 7 = 140. Delta = 56.
- `conn::uint`: `single_sided_props!` expands to 4 proptest
  functions. Old: 16 conns × 4 = 64. New: 25 conns × 4 = 100. Delta
  = 36.
- Combined 128-bit integer delta: 56 + 36 = 92. Matches.
- `conn::fixed::i128`: 15 conns × 9 properties = 135 proptests + 4
  spot tests = 139. Matches.

**`degenerate_max_shift` regression test.** Present at
`src/conn/fixed/i128.rs:147`. Covers `I128I000.inner` for 0, +1, −1
and `ceil`/`floor` for 0, ±1, `i128::MIN`, `i128::MAX`. Satisfies
plan requirement.

**Boundary fixups.** `ceil` guards `x.to_bits() == FINE_MIN`; `floor`
guards `x.to_bits() == FINE_MAX`. Both present at
`src/conn/fixed/i128.rs:45` and `:93`. The `spot_boundary_fixups`
test exercises them on `I128I064` (SHIFT=64). Pattern is identical
to the `i64` module.

**Edge case not exercised — `floor(I128I000, FINE_MIN)`.**
`degenerate_max_shift` checks `floor(i128::MAX)` (the `FINE_MAX`
branch) but does not check `floor(i128::MIN)` for `I128I000`. The
`FINE_MIN` guard fires only in `ceil`; for `floor`, `FINE_MIN` falls
through to the degenerate `None` branch (bits < 0 → return −1). The
behaviour is correct, but no spot assertion. The proptest battery at
64 cases would likely catch a violation probabilistically; the gap
is not a blocking issue. Track as follow-up.

### i128 Module Correctness

`I128I000` truth table verified:

| Function | Input | Output |
|----------|-------|--------|
| `ceil` | `bits = FINE_MIN` | `from_bits(i128::MIN)` |
| `ceil` | `bits > 0` | `from_bits(1)` |
| `ceil` | `bits ≤ 0` (non-MIN) | `from_bits(0)` |
| `inner` | `bits = 0` | `from_bits(0)` |
| `inner` | `bits > 0` | `from_bits(FINE_MAX)` |
| `inner` | `bits < 0` | `from_bits(FINE_MIN)` |
| `floor` | `bits = FINE_MAX` | `from_bits(i128::MAX)` |
| `floor` | `bits ≥ 0` (non-MAX) | `from_bits(0)` |
| `floor` | `bits < 0` | `from_bits(-1)` |

Galois laws `ceil(fine) ≤ coarse ⟺ fine ≤ inner(coarse)` and
`inner(coarse) ≤ fine ⟺ coarse ≤ floor(fine)` hold at all entries.
The saturation pattern is identical to the i08 degenerate endpoint
`I008I000`. Correct.

For non-degenerate pairs (`RATIO = Some(r)`), the
`checked_mul + saturate` strategy produces the same result as a
widening-to-i256 multiply at every input (both saturate at
`i128::MIN` / `i128::MAX` on overflow; neither wraps).

### Plan Conformance

| Task | Status |
|------|--------|
| T1 — decimal rename | Complete. 7 wrappers, 28 conns, decimal.rs module doc, arb.rs strategies, conn.rs doctests, lib.rs naming table, doc/design.md. |
| T2 — sample rename | Complete. 4 wrappers (S044/S048/S088/S096), 15 rate-pair conns, 6 FD12Sxxx conns. |
| T3 — signed-int rename | Complete. |
| T4 — unsigned-int rename | Complete. |
| T5 — binary-fixed rename | Complete. 66 conns + per-module type aliases. |
| T6 — doc rewrite | Complete. lib.rs naming table, doc/design.md, conn.rs / fixed.rs / property/mod.rs module docs. |
| T7 — plan + review doc | Complete. |
| T10 — 128-bit ints | Complete. arb_ext_i64 / arb_ext_u64 strategies added. |
| T11 — i128 binary fixed | Complete. degenerate_max_shift present. |

### Risks

**No TODOs, stubs, placeholder implementations.** New i128 module
is complete.

**Downstream callers.** Crate is unpublished
(`version = "0.1.0"`); zero downstream risk.

**Security.** No new dependencies introduced.

**Cascading rename completeness.** All active source and doc files
updated consistently. Historical plan/review docs intentionally
unchanged, as specified.

### Recommendations

**Must fix before push** — addressed in this round, no blockers
remaining:

1. ~~`I008I004` cited in lib.rs doctest and review-00014 test plan
   does not exist in `conn::fixed::i64`.~~ Fixed: replaced with
   `I008I000` (the only conn-name shared by `i08` and `i64`
   modules).

**Follow-up (acceptable now, track for later)**

2. `pico_fine` / `pico_coarse` / `pico_safe` strategy names in
   `src/property/arb.rs` still use the `pico_*` prefix despite the
   `Pico`→`FD12` rename. Plan explicitly defers arb-strategy
   renaming to a cosmetic-only sprint.

3. `degenerate_max_shift` does not assert
   `I128I000.floor(from_bits(i128::MIN))`. Adding one explicit
   assertion would make the regression exhaustive for the
   `I128I000` truth table.

4. Minor alignment drift in `src/conn/sample.rs` module doc table
   after the wrapper rename (3-char → 4-char). Cosmetic only.
