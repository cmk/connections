# Review 00039 — Plan 25: fold int/ + NonZero into fixed/

## Summary

- Folds `connections::int::*` into `connections::fixed::*` (every
  std-int Conn is structurally a Q*N*.0 fixed-point) and renames
  every intra-fixed Conn prefix `I`/`U` → `Q` so prefix letters alone
  disambiguate Fixed wrappers from std primitives. ~150 constants
  renamed; std-int names (e.g. `I064I128`, `U008I016`) keep their
  letter prefixes since they target std primitives.
- Adds two new families on top of the merge: 10 NonZero Conns
  (`fixed::iN::I{NN}N{NN}`, `fixed::uN::U{NN}N{NN}` of type
  `Conn<{i,u}N, NonZero<{i,u}N>>` — signed is the asymmetric-adjoint
  showcase, both Galois laws hold) and 10 cross-crate iso Conns
  (`fixed::iN::Q000I{NN}` etc., bridging `Fixed{I,U}<U0>` and the
  matching primitive). Lands a `Conn::new_iso` constructor used by
  the iso family.
- Resets `Cargo.toml` to `version = "0.0.0"` (crate is unpublished;
  first crates.io release will be `0.0.1`). Internal-only refactor
  — no migration concern outside the repo.

## Test plan

- [x] `cargo test --workspace` clean across all 18 binaries (1171
      lib tests + 16 integration tests + doctests).
- [x] `cargo clippy --all-targets -- -D warnings` clean.
- [x] `cargo build` clean.
- [x] Depcheck: `git grep "connections::int::"` and `crate::int::`
      return zero hits in `src/`, `tests/`, `README.md`, `CLAUDE.md`.
- [x] T2.5 audit: `git grep -E 'fix_fix_[iu][0-9]+!\([IU][0-9]{3}[IU][0-9]{3}'`
      returns zero hits (every intra-fixed Conn prefix is now `Q`).
- [x] NonZero spot tests on i8 (signed) + u8 (unsigned) cover
      asymmetric `floor`/`ceil` at zero, total inner embedding,
      finite round-trip, infinity / saturation behaviour.
- [x] NonZero proptest: `i008n008_galois_l` + `i008n008_galois_r` +
      `i008n008_inner_then_ceil_recovers_nonzero` all pass on the
      signed Conn (full triple). Unsigned `u008n008_galois_l` +
      round-trip pass; `galois_r` is correctly *not* asserted (fails
      at the unsigned bottom plateau by type-theoretic necessity).
- [x] Iso proptest: `q000i008_galois_l` + `_r` +
      `q000i008_round_trip_both_directions` all pass.
- [ ] Property-test battery on all 10 NonZero widths and all 10 iso
      widths (currently only i8 + u8 representatives are exercised;
      the macros guarantee uniformity, but a parity check would be
      cheap insurance). Tracked as a follow-up in the plan's
      Recommendations.

## Local review (2026-04-28)

**Branch:** sprint/fixed-merge
**Commits:** 14 (origin/main..sprint/fixed-merge)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All 14 commits use conventional prefixes (`feat:`, `fix:`, `task:`,
`doc:`). The fix commits (T9, T10) are correctly tagged for what
they are — mid-sprint orientation corrections, not CI repairs.
Commits are reasonably atomic; the only notable exception is that
T2 (file merges) and T2.5 (rename) are separate commits but T2.5
is a mechanical rename pass on top of T2's merge output, which is
fine. The two mid-sprint `fix:` commits (T9 and T10) were
documented in the plan's Review section before the sprint-review
commit. No empty commits, no merge commits, linear history.

The plan listed T5 as "lib.rs surgery + 0.0.0 reset" but the
corresponding commit message is `task: Reset Cargo.toml to version
0.0.0 (Plan 25 T5)`. The lib.rs surgery (dropping `pub mod int;`)
was folded into T2/T10 rather than T5 as planned. The commit
landed cleanly and `lib.rs` is correct; the mismatch is cosmetic.

### Code Quality

**Stale doc links in `src/lib.rs` — must fix.** Lines 58–85 of
`src/lib.rs` still describe `int::*` paths:

```rust
//! Integer-conn families live under `int::{i8,…,u128}` — one
//! submodule per primitive…
//! - [`int::u16::U008U016`] — `u8 → u16`…
//! - [`int::i16::I008I016`] — `Extended<i8> → i16`…
//! - [`int::i8::I016I008`] — `i16 → i8`…
//! (etc., 8 more `int::` links)
```

The `int` module was deleted in T10; these `[`int::*`]` intra-doc
links are broken. `cargo doc --no-deps` will emit warnings or
errors on every one. T10's depcheck audited `src/`, `tests/`,
`README.md`, and `CLAUDE.md` per the plan, but `src/lib.rs` was
not in that list — and this block survived.

**Stale doc link in `src/conn.rs` — should fix.** Line 13:
`` //! - [`crate::int`] — connections rooted in `std` integer
primitives. `` The module is gone; the link is dead.

**`expect` calls in production macros.** `nz_int_ext!` and
`nz_uint_ext!` in `src/fixed.rs` (lines 345, 349, 378) use
`.expect("nz_int_ext::ceil produced zero")`. These are inside
`const` blocks that are callable at runtime. The precondition
("produced zero") cannot be triggered by any valid input because
the macros guard `v == 0` explicitly before calling
`NonZero::new`, but the `expect` message will appear in a panic
if the logic is ever wrong. This is acceptable defensive code,
but the messages are slightly misleading — they say "produced
zero" when the actual impossible scenario would be a logic error
in the guard. Low severity.

**Section order out-of-sequence in every affected file.** In
`src/fixed/i8.rs`, `src/fixed/i16.rs`, `src/fixed/i128.rs`,
`src/fixed/u8.rs` (and presumably all 10 merged files), the
physical code runs §1 → §3 → §4 → §2. This matches the plan's
comment layout sketch (plan lines 154–161), but the file-level
doc comment in `i128.rs` only documents §1 and §2 — §3 and §4
are undocumented in the module-level doc. Not a bug, but the
out-of-order section numbers will confuse first-time readers; a
brief comment explaining the placement would help. Follow-up
candidate.

No unsafe code. `#![forbid(unsafe_code)]` is present in `lib.rs`
(line 147). No dead code or visible clippy-level issues beyond
what's noted above.

### Test Coverage

**Property tests — highest-priority check.**

The plan's Verification table requires:
- `n008i008_galois` … `n128u128_galois` (10 props, full
  `prop::conn` battery on each NonZero Conn)
- `nz_signed_zero_asymmetry` + `nz_unsigned_zero_collapse`
  (named properties)
- `q000_iso_round_trip` (10 Conns) and `q000_galois` (10 Conns)

What shipped: `i008n008_galois_l`, `i008n008_galois_r`,
`i008n008_inner_then_ceil_recovers_nonzero`, and the equivalent
for `u008n008`. Spot tests exist only for i8 and u8. For i16,
i32, i64, i128, u16, u32, u64, u128: the NonZero and iso consts
are declared but have **zero tests** — no spot checks, no
proptests. The iso consts `Q000I016` through `Q000U128` (except
Q000I008 and Q000U008) also have no proptests.

This is a gap, explicitly flagged in the plan's Review section
("only i8 + u8 are exercised"). The implementer's stated defense
is "the macros guarantee uniformity." That holds for the macro
body, but the `expect` calls and the fact that each module
imports different macros from `super` (some files omit macros
they don't need) means a per-file import error could silently
produce incorrect Conns at other widths. The plan itself lists
all 10 widths in the Verification table. The implementer's own
Recommendations section calls this out as a follow-up, but it is
a gap against the plan's stated properties.

The signed-zero-asymmetry property (`nz_signed_zero_asymmetry`)
and `nz_unsigned_zero_collapse` are described in the plan table
by name. They do not appear under those names in the diff; the
behavior is covered inline in `i008n008_floor_ceil_split_at_zero`
and `u008n008_zero_collapses_to_nonzero_one`, but only for
i8/u8. The named properties are absent for all other widths.

All existing `int_*_galois.rs` and `fixed_*_galois.rs` integration
tests pass (per the plan's Review build-gate count). No
`fixture_or_skip!` usage is needed here (no fixture files
involved). No `#[ignore]`d new tests.

The iso proptests for i8/u8 (`q000i008_galois_l`, `_r`,
`q000i008_round_trip_both_directions`) are present and correct.
The iso proptests for the other 8 widths are absent.

### Plan Conformance

- **T0** (Conn::new_iso): Implemented correctly. Doctest matches
  the plan's example, plus a richer
  `new_iso_floor_eq_ceil_and_round_trip` unit test.
- **T1** (macros into fixed.rs): Done. All seven macros
  (`uint_uint!`, `int_uint!`, `ext_int!`, `int_int_narrow!`,
  `uint_uint_narrow!`, `uint_int_sat!`, `int_uint_narrow!`) plus
  two new ones (`nz_int_ext!`, `nz_uint_ext!`) are in
  `src/fixed.rs`.
- **T2** (file merges): Done for all 10 files.
- **T2.5** (I*/U* → Q* rename): Done.
  `git grep -E '\bfix_fix.*\(I[0-9]{3}I[0-9]{3}'` returns zero
  hits. T2.5 audit passes.
- **T3** (NonZero family): 10 consts declared. Name deviates
  from plan (see below).
- **T4** (cross-crate iso): 10 consts declared and correct.
- **T5** (version reset): `Cargo.toml` reads `0.0.0`.
  `pub mod int;` removed from `lib.rs`.
- **T6** (CHANGELOG): Present and accurate.
- **T7** (CLAUDE.md rewrite): Done. Prefix table updated, worked
  examples updated, module table updated.
- **T8** (README): Done. Family table and framing prose updated;
  README code examples use `fixed::i16::U008I016`.
- **T9** (proptest re-wiring): Integration test paths updated to
  `fixed::*`. NonZero and iso proptests added for i8/u8 only.
  Other widths unpropped.
- **T10** (delete old paths + depcheck): `src/int/` and
  `src/int.rs` deleted. `lib.rs` has `pub mod int;` removed.
  Stray `connections::int::` and `crate::int::` references in
  `src/lib.rs` and `src/conn.rs` doc comments were NOT cleaned up
  — T10's depcheck list did not include doc comments inside
  `src/lib.rs`.

**NonZero type-signature deviation.** The plan originally
specified `Conn<NonZero<X>, Extended<X>>`, then stated
`Conn<Extended<X>, NonZero<X>>` in the Review section after one
fix, and the final shipped form is `Conn<X, NonZero<X>>` (bare
primitive, no Extended). The plan's Review section documents
this correctly. The code is correctly typed.

However, three documentation sites describe the NonZero family
as bridging `NonZero<*> ↔ Extended<*>` (the abandoned intermediate
orientation) rather than the final `X ↔ NonZero<X>` shape:

1. **`README.md` line 115**:
   `| NonZero<*> ↔ Extended<*> (N###I###, N###U###) | …`
2. **`src/fixed/i8.rs` line 56**:
   `// ── §3 NonZeroI8 ↔ Extended<i8>`
3. The Conn-name prefix table in CLAUDE.md (line 115) says
   `N | NonZero<iN> / NonZero<uN> (sign by module) | bit-width` —
   this is correct, it just names the `N` side without claiming
   `Extended`. But point 1 and 2 are stale.

Additionally, the naming convention cited in CLAUDE.md's
canonical examples table (`I008N008`) lists the Conn as
`i8 → NonZeroI8 in fixed::i8` — this is correct. But the README
table header (`N###I###`) implies `N` is on the left (the
source), which is wrong: the actual constants are `I008N008`
(I on left, N on right).

### Risks

**Stale intra-doc links are the primary risk.** `src/lib.rs` has
eight `[`int::*`]` links and multiple paragraphs describing the
deleted `int` module. `src/conn.rs` has one. These will cause
`cargo doc` warnings at minimum and broken documentation at
publish time. Since the crate is unpublished, this doesn't
affect external consumers today, but it does break the T10 goal
("run `cargo build` to confirm no stragglers") and the build
gate "cargo doc --no-deps — clean."

**I*/U*/N naming in README table contradicts actual constants.**
`README.md` line 115 describes the family as `N###I###, N###U###`
— but no such constants exist. The actual constants are `I008N008`
(signed) and `U008N008` (unsigned), with `N` on the right. A
user who reads the README and tries
`connections::fixed::i8::N008I008` will get a compile error.

No security concerns (pure Rust math library, no I/O, no unsafe).

No new dependencies.

### Recommendations

**Must fix before push:**

1. **`src/lib.rs` lines 58–93: rewrite to `fixed::*` paths.** The
   entire block describing `int::*` submodules and the eight
   `[`int::*`]` intra-doc links must be rewritten to `fixed::*`.
   This is the most impactful stale-doc issue because it is the
   crate's root doc page.

2. **`src/conn.rs` line 13: drop or update the `[`crate::int`]`
   link.** The module is gone; the link is dead. Either remove
   the bullet or repoint it to `[`crate::fixed`]`.

3. **`README.md` line 115: fix NonZero family description.**
   Change `NonZero<*> ↔ Extended<*> (N###I###, N###U###)` to
   `X ↔ NonZero<X> (I###N###, U###N###)` to match the actual
   type and constant names. As written, a reader who looks up
   `N008I008` will find nothing.

4. **`src/fixed/i8.rs` line 56 section comment: update.**
   `// ── §3 NonZeroI8 ↔ Extended<i8>` should read
   `// ── §3 i8 ↔ NonZeroI8` to match the actual type
   `Conn<i8, NonZeroI8>`.

**Follow-up (future work):**

5. Add NonZero (`I016N016`, `I032N032`, …, `U016N016`, …) and
   iso (`Q000I016`, `Q000I032`, …, `Q000U016`, …) spot tests and
   proptests for the 8 non-representative widths. The plan's
   Verification table lists all 10 widths as required properties,
   and the implementer's own Review calls this out. The
   macro-uniformity argument reduces risk but does not eliminate
   it — a per-file import mistake would produce a wrong Conn
   silently.

6. Fix the out-of-sequence section numbering in the merged files
   (§1 → §3 → §4 → §2 in every file). The physical order is
   rational given how the code was assembled, but the numbers
   mislead. Renumber to §1 → §2 → §3 → §4 or add a comment
   explaining the deliberate out-of-order placement. Minor, but
   will confuse the next contributor who expects sections to be
   in order.
