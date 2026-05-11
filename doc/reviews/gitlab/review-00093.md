# MR !93 — Phase 1 boundary-saturation fix + plateau coverage

## Summary

- Mirrors the Phase 2 boundary-saturation fix into
  `__float_ext_int_ceil_body!` (`src/float.rs`), closing the
  L-Galois gap on `F032U032` / `F032I032` / `F032U064` / `F032I064`
  / `F064U064` / `F064I064` where the strict `v > hi` guard missed
  inputs at the saturating-cast plateau. The fix routes through the
  existing `BitsToF64Rd` sealed dispatch trait — no new
  infrastructure.
- Extends `arb_f64_bounded` / `arb_f32_bounded` and
  `tests/common/mod.rs` with the saturation plateaus
  (`2^31`/`2^32`/`2^63`/`2^64`/`2^127`/`2^128` plus
  `next_up`/`next_down` of each) so the law battery actually
  exercises the fix. The bounded-uniform random branch stays
  bounded; only the boundary set grows.
- Bumps law-battery cases from the proptest default (256) to
  `cases: 1024` across all 10 `tests/fixed_*_float_q_galois.rs`
  files and the inline f032/f064 Float→Ext<intN> batteries —
  matches plan-02's stated target now that there are interesting
  boundary inputs to sample around.
- Adds 7 new spot tests (`f032/f064 *_at_plateau_to_posinf`)
  pinning the post-fix behavior at the exact plateau values.

## Test plan

- [x] `cargo test --workspace --quiet` — 1355 lib + all
  integration tests pass on stable (was 1348; +7 new spot tests).
  No `#[ignore]`.
- [x] `cargo build --features f16 --quiet` (nightly) — clean.
- [x] `cargo clippy --all-targets --quiet -- -D warnings` — clean.
- [x] `cargo fmt --all -- --check` — clean.
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features
  testing,macros,time --document-private-items --quiet` — clean.
- [x] Plateau coverage exercises the fix: each of `F032U032`,
  `F032I032`, `F032U064`, `F032I064`, `F064U064`, `F064I064` has a
  spot test asserting `ceil(Extend(plateau_value)) == PosInf`. Pre-
  fix the test would have pinned `Finite(MAX)`.

## Notes

Plan: `doc/plans/plan-2026-05-10-01.md`.

Closes 3 of the 4 follow-ups from MR !92 (review-00092.md):
boundary fix mirror, cases bump, plateau coverage. The fourth — T10
f16-source Q-format Conns — ships as MR B in a follow-up sprint
(plan-2026-05-10-02 or revised T10 spec).

## Out of scope (deferred to follow-up MR)

- T10 f16→Q-format Conns (62 Conns gated on `feature = "f16"`).
  Direct implementation via `float_fixed!` / `float_fixed_l!`
  mirroring T6's choice. Bounded separately to keep this MR's
  review surface minimal.
- Inline `cases: 1024` for `src/float/f016.rs` law batteries —
  gated on the f16-feature nightly CI runner; deferred to MR B
  alongside the f16-source Conn additions.

## Local review (2026-05-10)

**Branch:** sprint/fix-boundary
**Commits:** 2 (origin/main..sprint/fix-boundary)
**Reviewer:** Claude (sonnet, independent)

---

# Sprint Review: `sprint/fix-boundary` → `origin/main`

## Pass 1 — Cold Review (no plan)

### P1.A — Trait-claim audit

#### Item 1: `__float_ext_int_ceil_body!` (modified, `src/float.rs` lines 1463–1491)

**The contract.** Pasted into `float_ext_int!` (via `conn_k!`,
claiming `ConnL + ConnR`) and `float_ext_int_l!` (claiming `ConnL`
only). The `ConnL` law is `ceil(a) ≤ b ⟺ a ≤ inner(b)` for all
`a: ExtendedFloat<$float>` and `b: Extended<$int>`.

**The implementation.** New else branch detects boundary
saturation: when `bits == MAX` after the saturating cast and
`to_f64_rd(MAX) < scaled_ceil_float as f64`, the cast actually
overflowed and we return `PosInf` instead of `Finite(MAX)`.

**Consistency.** Consistent with the `ConnL` contract on the full
domain. The fix closes the boundary case for all `$int` types
where `MAX` is not exactly representable in `$float`. **Pass.**

#### Item 2: `__float_ext_int_floor_body!` (unchanged)

Used only by `float_ext_int!` (full triple), where
`<$int>::BITS ≤ <$float>::MANTISSA_DIGITS + 1`. For all such
types, `MAX` is exactly representable in `$float`. **Pass.**

#### Item 3: `__float_ext_int_inner_body!` (unchanged)

No change in diff. **Pass.**

### P1.B — Standard Review

**Commit hygiene.** Two commits, conventional `fix:` and `doc:`
prefixes, atomic. Each leaves the repo green.

**Code quality.** No unsafe code. The `scaled_ceil_float` binding
avoids calling `.ceil()` twice. No clippy concerns.

One observation: the inline comment in `__float_ext_int_ceil_body!`
(and the original Phase 2 comment in `__float_fix_ceil_body!`) says
"For hosts where `MAX` is f64-exact (host bits ≤ 53 plus signed
128-bit)". The signed 128-bit claim is incorrect: `i128::MAX =
2^127 - 1` is not f64-exact (requires 127 mantissa bits). The
check is a live guard for i128, not a no-op. The code is sound;
only the comment misleads.

**Test coverage.** All 10 integration test files bumped to
`cases: 1024`. Phase 1 inline batteries bumped. 7 spot tests cover
every f32/f64 × L-only-target combination (planned 4; extra 3 are
intentional per plan Review).

**Risks.** Plateau values stay in finite range. `from_bits(x.to_bits()
+ 1)` is safe — no overflow into ±∞. `tests/common/mod.rs` mirrors
`src/prop/arb.rs` exactly.

## Pass 2 — Plan-aware Review

### P2.A — Test-exception escalation

The plan's only explicit exception is the `__float_ext_int_floor_body!`
"deliberately not fixed" note, correctly bounded to the full-triple
domain where the issue cannot arise. No type-claim mismatch.

### P2.B — Plan conformance

- T1 (boundary fix): Implemented. Plan pseudocode and actual code are
  semantically equivalent.
- T2 (cases bump): All 10 integration tests + Phase 1 batteries bumped.
- T3 (plateau generators): Implemented. `next_down` of negative plateaus
  was implied in the plan but omitted in implementation; functionally
  harmless (the saturation bug is only on the positive/ceil side).
- T4: Review and plan docs committed.

MR B tasks (T5–T8): Correctly deferred.

## Recommendations

**Must fix before push:**

None.

**Follow-up (future work):**

1. **Comment correction in `src/float.rs`** (~line 1477) and
   `src/fixed.rs` (~line 602): the parenthetical "host bits ≤ 53,
   plus signed 128-bit" is wrong. `i128::MAX` is not f64-exact.
   The check is meaningful for i128, not a no-op. Could mislead a
   future reviewer into removing the guard. ~5-line cleanup.
2. **Add `f064i064_just_past_plateau_to_posinf`** for symmetry
   with the existing `f064u064_just_past_plateau_to_posinf` test.
   The law battery covers this probabilistically but a named test
   is cheap insurance.
