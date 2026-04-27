# Review !20 — `feat: Modularize conn::float and add half-based F016/B016 Conns`

## Summary

- Modularizes `src/conn/float.rs` into the parent + subdirectory shape
  (`conn::float.rs` + `conn::float/{f32,f64}.rs`), mirroring `conn::fixed.rs`
  + `conn::fixed/`. `F064F032` moves into `conn::float::f64`; `f16`/`b16`
  per-source-tier submodules are deferred until they have content.
- Adds four direct precision-narrowing Conns to half-precision via the
  `half` crate: `F032F016`, `F032B016`, `F064F016`, `F064B016`. Each
  goes through `half::{f16,bf16}::from_{f32,f64}` (RNE) and walks ≤ 2
  ULPs on the target side. ULP-walk helpers refactored to return
  `(result, steps)` so a `ulp_steps_bounded` proptest can assert the
  bound. New `F016` / `B016` type aliases swap to native types
  transparently when stable.
- Renames `ExtendedFloat::Finite` → `Extend` (the variant name now
  reflects its lattice role between `Bot` and `Top`, not a numeric
  property of the wrapped value — `NaN` isn't finite). `Extended<T>`
  keeps `Finite` because its wrapped values really are.

## Test plan

- [x] `cargo test --workspace` — 1703 pass (+75 vs main)
- [x] `cargo test --doc` — 23 pass (+4 doctests, including the README
      mirror of `F064B016`)
- [x] `cargo clippy --all-targets -- -D warnings` — clean
- [x] `cargo fmt --all -- --check` — clean on touched files
- [x] `cargo doc --no-deps` — clean (preexisting `arb` link warning
      unrelated to this MR)
- [x] `cargo build --workspace` — clean
- [x] Per-Conn proptest config (cases=256, max_shrink_iters=200)
      keeps shrink-time bounded under the
      [proptest_shrink_tuning](../../) memory's guidance
- [x] `signed16_round_trip` exhaustively sweeps `0u16..=u16::MAX`
- [x] ULP-step bound asserted to be ≤ 2 across all 5 floats Conns
      (the existing F064F032 plus the four new ones)

## Local review (2026-04-26)

**Branch:** sprint/float-half
**Commits:** 13 (origin/main..sprint/float-half)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All 13 commits carry conventional prefixes (`task:`, `refactor:`, `feat:`,
`test:`, `doc:`). Subjects are within 72 chars. The dependency graph
(T0 → T1 → T2 → T3/T4 → T5–T8 → T9 → T10) is reflected faithfully in
the commit ordering — each commit should be self-contained and testable
because the pre-commit hook gates on `cargo test`.

One minor note: commit `feat: Add F064B016` mentions "headline new
feature of MR !19" in the inline rustdoc at `src/conn/float/f64.rs:333`,
but the review doc and plan both use MR !20 (the iid bumped). Stale
reference in a doc comment.

### Code Quality

**No unsafe code.** `#![forbid(unsafe_code)]` applies; nothing in the
diff bypasses it.

**Module layout.** `src/conn/float.rs` + `src/conn/float/f32.rs` +
`src/conn/float/f64.rs` matches the `conn/fixed.rs + conn/fixed/`
pattern. No `mod.rs` files introduced. `f16.rs` / `b16.rs` were not
created prematurely (Q3 confirmed).

**`#[allow(dead_code)]` on `signed16` / `unsigned16`.** Both helpers
are called inside `shift16_f16` and `shift16_bf16`, which are in turn
called inside `ceil_*` / `floor_*` functions in `f32.rs` and `f64.rs`.
The annotations are misleading — they suggest the functions are
otherwise-unused, when in fact they are on the hot path of every new
Conn. Should be removed.

**ULP walk duplication.** The four walk helpers (`ascend_to_ceil_*`,
`descend_to_ceil_*`, `ascend_to_floor_*`, `descend_to_floor_*`) are
repeated four times (f32→f16, f32→bf16, f64→f16, f64→bf16) with
mechanical type substitution — roughly 360 lines of near-identical
code. The plan's Review section already documents this as a follow-up
(`walk!` macro or generic helper). Acceptable for this sprint.

**`signed16` correctness.** The mapping `0x7FFF_i32 - (x as i32)` for
the negative half: at `x = 0x8000` (-0 in sign-magnitude) gives `-1`,
correct. At `x = 0xFFFF` gives `-32768`. The round-trip test
`signed16_round_trip` exercises all 65536 values exhaustively.

### Test Coverage

**Property battery completeness.** All four new Conns carry the full
11-property battery (galois_l/r, closure_l/r, kernel_l/r, monotone_l/r,
idempotent, floor_le_ceil, ulp_steps_bounded). F064F032's existing
battery gains `ulp_steps_bounded`. All required properties present.

**`ulp_steps_bounded` coverage.** Each test mirrors the private walk
logic directly. The NaN early-return path and the exact-match
early-return path both use `return Ok(())` before exercising any
walk — correct, since those inputs have no walk to bound.

**Critical issue — incomplete `bot_top_pass_through` spot checks
(confidence 95).**

Three `bot_top_pass_through`-style tests silently omit assertions:

- `src/conn/float/f32.rs:610–615` `b16_bot_top_pass_through`: tests
  `ceil(Bot)`, `floor(Top)`, `inner(Bot)`, `inner(Top)` — missing
  `ceil(Top)` and `floor(Bot)`.
- `src/conn/float/f64.rs:868–873` `f16_bot_top_pass_through`: same
  pattern — `ceil(Top)` and `floor(Bot)` missing.
- `src/conn/float/f64.rs:912–917` `b16_bot_top_pass_through`: same.

Compare against the complete version in `f32.rs:403–410`
(`bot_top_pass_through` for F032F016) which asserts all six
combinations. The three incomplete tests would pass even if
`ceil(Top)` returned `Bot` or `floor(Bot)` returned `Top`. Real gap.

**`arb_bf16` uniform range.** `(-1.0e6_f32..=1.0e6_f32)` leaves a gap
between `1e6` and `bf16::MAX` (≈3.39e38) that is not reachable from
the uniform slot — only the explicit `Just(half::bf16::MAX)` /
`Just(half::bf16::MIN)` boundary entries cover that interval. The
plan documents this as intentional for shrink performance. Worth a
comment inside the function explaining the gap.

### Plan Conformance

- T0–T10 all delivered.
- Q3 (no placeholder files) confirmed: no `f16.rs` or `b16.rs` exists.
- D9 (`Extended<T>::Finite` left alone): only `ExtendedFloat::Finite`
  → `Extend` was renamed.
- Plan number mismatch in filename ("Plan 12" titled, in
  `plan-2026-04-26-11.md`) — documented explicitly in the Review
  section.

### Risks

**Stale MR reference in rustdoc (confidence 85).**
`src/conn/float/f64.rs:333` says "headline new feature of MR !19"; the
plan and review doc both record !20. Publicly visible in `cargo doc`
output.

**`#[allow(dead_code)]` annotations remain on live code (confidence 80).**
`src/conn/float.rs:200` and `:213` on `signed16` / `unsigned16`. The
plan's Review section says "the attribute was removed implicitly when
the first consumer (T5) landed" — but the attribute is still present.
Suppresses a diagnostic that would otherwise correctly confirm the
functions are live.

**No `#[ignore]`d tests.** Confirmed.

**`half` crate dependency.** `default-features = false` is correct —
avoids pulling in optional features. `half` 2.x is actively maintained;
MSRV (1.51) is well below the pinned 1.85. Justified.

**Doctests.** All four new Conn constants have working doctests. The
`F064B016` doctest is mirrored verbatim into `README.md` and would
catch drift via `cargo test --doc`.

### Recommendations

**Must fix before push:**

1. **Complete the three incomplete `bot_top_pass_through` tests.** Add
   the missing `ceil(Top)` and `floor(Bot)` assertions to:
   - `b16_bot_top_pass_through` in `src/conn/float/f32.rs:610`
   - `f16_bot_top_pass_through` in `src/conn/float/f64.rs:868`
   - `b16_bot_top_pass_through` in `src/conn/float/f64.rs:912`

   Match the complete 6-assertion shape of `bot_top_pass_through` at
   `f32.rs:403`.

2. **Fix the stale `!19` MR reference** in the `F064B016` rustdoc at
   `src/conn/float/f64.rs:333`. Change to `!20`.

3. **Remove the `#[allow(dead_code)]` attributes** from `signed16`
   and `unsigned16` in `src/conn/float.rs:200` and `:213`. The
   consumers shipped in T5–T8.

**Follow-up (future work):**

- Extract the four walk helpers into a `walk!` macro or generic helper
  to eliminate ~360 lines of mechanical duplication.
- Add a comment to `arb_bf16` in `src/property/arb.rs` explaining why
  the uniform slot is bounded at `±1e6`.
- Consider `scripts/check_readme_mirror.sh` to enforce `F064B016`
  doctest sync.

