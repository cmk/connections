# MR !26 — Cast Sprint B: two-sided helpers

## Summary

- Adds `interval`, `midpoint`, `round` / `round1` / `round2`,
  `truncate` / `truncate1` / `truncate2`, and `median` to
  `conn::cast`, finishing the Cast.hs port begun in Sprint A.
- Mirrors Haskell signatures verbatim (incl. `median`'s
  `Conn<(A, A), A>` shape and `interval`'s `Option<Ordering>`
  return); the only deviation is `midpoint`'s body, which uses
  `lo + (hi - lo) / 2` for integer-exact behavior.
- Ships 10 new `cast_*` law predicates in `property::laws`, plus
  spot checks (incl. `round2`/`truncate2` binary-lift checks) and
  14 proptest blocks driving the helpers over `ID_I32`, `ID_I64`,
  and `ORDERED_PAIR`. Pure addition; no existing tests touched.

See `doc/plans/plan-2026-04-27-04.md` for full plan, deviations,
and verification.

## Test plan

- [x] `cargo test --workspace` — 1995 tests pass (1806 lib + 189
      integration).
- [x] `cargo test --doc` — 34 pass / 3 ignored (3 new Sprint-B
      doctests included).
- [x] `cargo clippy --all-targets -- -D warnings` — clean.
- [x] `cargo doc --no-deps` — zero new warnings (14 pre-existing
      W6 redundant-link warnings unchanged from main).
- [x] `cargo fmt --all -- --check` — clean.
- [x] `/sprint-review` (Tier 1 local review) — must-fix items
      addressed in commit `9ff87bd`.
- [ ] CI green on `sprint/cast-b`.

## Local review (2026-04-27)

### Commit Hygiene

Both commits have conventional prefixes (`feat:`, `doc:`) and atomic
scope. `05bfa69` is pure documentation; `542364e` is the full
implementation. Each commit leaves the repo in a buildable state.
No concerns.

### Code Quality

All nine helpers are implemented. No unsafe code. Formatting is clean.

**`median` body** (`src/conn/cast.rs:400`):
`meet(meet(join(x, y), join(y, z)), join(z, x))` — faithful to the
Birkhoff triple `(x⊔y) ⊓ (y⊔z) ⊓ (z⊔x)`. Correct.

**`round` dispatch** (`src/conn/cast.rs:341–345`):
`interval` computes `d_lo.partial_cmp(&d_hi)` where `d_lo = x -
lower(x)` and `d_hi = upper(x) - x`. `Some(Greater)` means `d_lo >
d_hi`, i.e. x is closer to the upper/ceil rung, so `→ c.ceil(x)` is
correct. `Some(Less)` → `c.floor(x)`. Dispatch is faithful to Haskell.

**Missing doctests on four public fns.** The plan (T1, `doc/plans/
plan-2026-04-27-04.md:91–93`) says "Each public fn carries a 4–6
line doctest." `truncate1`, `truncate2`, `round1`, and `round2` have
no doctests. The review file claims `cargo test --doc` shows only 3
new doctests, which is consistent — but those three map only to
`interval`, `midpoint`/`truncate` (one doctest each), `round`, and
`median` (five functions total, at most five tests). Counting confirms
that `truncate1`, `truncate2`, `round1`, and `round2` are missing
their doctests entirely. This violates the stated T1 contract.

**Off-by-one count in two doc artifacts.** `doc/plans/plan-2026-04-27-04.md:98`
says "Eleven predicates total" and `doc/reviews/review-00025.md:12`
says "11 new `cast_*` law predicates." Both the plan's T2 table and
the laws.rs implementation have **ten** new predicates. The same
discrepancy occurs in the spot-check count: T3 says "Eleven new
deterministic spot checks" but lists and implements ten. Not a code
bug, but the artifact is wrong and will mislead a future reader
auditing completeness.

### Test Coverage

**`round2` and `truncate2` have zero test coverage** — no spot
checks, no proptest blocks, no doctests. The plan's T3 section does
not name any proptest for them, yet they are public functions that
compose `round` / `truncate` with `c.inner`. Their behavior on edge
inputs (e.g. `i32::MIN/2`) and the direction of the toward-zero
rounding are untested by any automated check in this sprint. Given
that the binary cousins of `round1`/`truncate1` are the only new fns
entirely without coverage, this is the highest-priority gap.

**Overflow safety in clamped ranges.** For identity Conns,
`lower1(c, id, x) == x` and `upper1(c, id, x) == x`, so `d_lo = 0`
and `d_hi = 0` — no arithmetic overflow can occur for any x. The
`i32::MIN/2..=i32::MAX/2` clamp is therefore conservative but
harmless for identity Conns; the comment in the tests explains the
intent clearly. For non-identity Conns the overflow concern is real,
but this sprint does not drive those (FD arithmetic is deferred).

**NaN path.** `cast_interval_at_midpoint_eq_or_none` accepts `None`
as a vacuously-passing result, which handles the NaN-bearing case.
No NaN-specific proptest exercises `truncate` or `round` on
`ExtendedFloat<f64>` inputs; this is consistent with the FD/EF
deferral and is acceptable for Sprint B's scope.

**`cast_round1_id_unit` / `cast_truncate1_id_unit` foot-gun.**
The rustdoc on both predicates (`src/property/laws.rs:657–678`) says
"on non-identity triples the equality holds only when `x` already
lies on a representable rung." The predicate signatures accept any
`Conn<A, B>` and any `x: B`, so a caller can silently pass a
non-identity Conn and get a predicate that is not generally true —
it will pass some inputs and fail others with no warning. The
signatures do not enforce the identity-Conn restriction. This is an
API foot-gun: if a future proptest drives `cast_round1_id_unit` over
`FD12FD09`, it will produce spurious failures that look like law
violations. A note in the docstring warning "only reliable for
identity Conns; use `cast_round_picks_endpoint` for general Conns"
would be sufficient without a type-level change.

**Deferred FD-arithmetic coverage** is documented explicitly in both
the plan's Deferred section and the T3 note. The justification (FD
newtypes lack `Add`/`Sub`/`Div`/`From<u8>` impls) is sound.
Acceptable deferral.

### Plan Conformance

**T1:** Nine helpers present. Module-doc updated. `Pcompare` reference
removed. Doctests present for `interval`, `midpoint`, `truncate`,
`round`, `median`. **Missing** for `truncate1`, `truncate2`,
`round1`, `round2` — 4 of 9 functions violate the T1 doctest spec.

**T2:** Ten new predicates in `src/property/laws.rs` (lines 579–703).
Plan says "Eleven"; actual is ten. All ten that exist match the plan
table entries. No predicate covers `round2` or `truncate2`.

**T3:** Ten spot checks, 14 proptest blocks. `round2` and `truncate2`
uncovered. The proptest comment at cast.rs:807 says "and ID_EF64 for
NaN-bearing coverage" — but no NaN-bearing median proptest was added.
This is a stale comment fragment; no EF64-backed median block exists.

**T4:** `lib.rs` re-exports all nine functions. README row flipped.
Both correct.

**T5:** Plan and review doc present. `/sprint-review` checkbox not
yet ticked (expected — this is that review).

### Risks

**Stale comment at `src/conn/cast.rs:807`:**
`// (and ID_EF64 for NaN-bearing coverage)` — no EF64-backed median
proptest block follows. This comment was likely a draft note that was
not removed. Harmless but misleading.

**Sprint A surface unchanged.** The diff adds only new items below
`minimize`; no existing function bodies are touched. Sprint A's
proptest blocks are unmodified. No regression risk to existing tests.

**No new dependencies.** Confirmed.

### Recommendations

**Must fix before push:**

1. **Add doctests to `truncate1`, `truncate2`, `round1`, `round2`.**
   (`src/conn/cast.rs`, after each function's prose doc.) The plan
   explicitly requires them; `cargo test --doc` currently silently
   skips these four. A minimal 3-line doctest using `Conn::identity()`
   suffices per the T1 spec.

2. **Add at least one spot check each for `round2` and `truncate2`.**
   (`src/conn/cast.rs::tests`, Sprint B spot-check block.) A single
   assertion like `assert_eq!(round2(&ID_I32, |a, b| a + b, 3, 4),
   7)` confirms the binary-lift wiring is correct and provides a
   regression anchor.

3. **Fix the "Eleven" count to "Ten"** in `doc/plans/
   plan-2026-04-27-04.md:98` (T2 prose), `doc/plans/
   plan-2026-04-27-04.md:119` (T3 prose "Eleven new deterministic"),
   and `doc/reviews/review-00025.md:12` (Summary bullet). The correct
   counts are 10 predicates and 10 spot checks.

4. **Remove the stale `// (and ID_EF64 for NaN-bearing coverage)`
   comment** at `src/conn/cast.rs:807` or replace it with an accurate
   note explaining why EF64 is not driven here.

**Follow-up (future work):**

5. Proptest blocks for `round2` and `truncate2` over `ID_I32`/`ID_I64`
   using `cast_round_picks_endpoint` / `cast_truncate_picks_endpoint`
   (the existing predicates already support binary inputs via the
   `f: FnOnce(A, A) -> A` path). Not strictly required to ship, but
   the binary variants are currently the only new public fns with no
   automated property coverage.

6. Consider adding a `# Warning` note to `cast_round1_id_unit` and
   `cast_truncate1_id_unit` rustdoc clarifying that the predicate is
   only generally true for identity Conns, so downstream users do not
   accidentally drive it over non-identity triples.

---

## Tier-1 fixes landed (2026-04-27)

Fix commit `9ff87bd` addresses items 1–4 from the must-fix list:

1. Doctests added to `truncate1`, `truncate2`, `round1`, `round2`.
2. Spot checks added: `truncate2_id_add_pair`, `round2_id_add_pair`.
3. Stale `// (and ID_EF64 for NaN-bearing coverage)` comment replaced
   with an accurate deferral note.
4. "Eleven" → "Ten" corrected in plan T2 + T3 prose, and the review
   summary's predicate count corrected.

Test counts after the fix: **1808 lib + 38 doc** (was 1806 + 34 on
the initial reviewed commits). Items 5–6 are tracked as follow-ups.

<!-- glab-id: 3289148242 -->
<!-- glab-discussion: 28913300125f5bf395771fc17787512bd279d01a -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/cast.rs:341` (2026-04-27 10:28 UTC) [open]

**[must-fix]** The `round` doc says `Some(Greater) → ceil(x)` (x is closer to the upper rung), but `interval` returns `d_lo.partial_cmp(&d_hi)` where `d_lo = x - lower` and `d_hi = upper - x`. When `d_lo > d_hi` (i.e. `Some(Greater)`), x is **farther** from the lower rung and **closer** to the upper rung, so dispatching to `c.ceil(x)` is correct — but the local review at `doc/reviews/review-00026.md:65` describes it correctly while the `round` rustdoc says 'ties broken toward zero … tie cases delegate to `truncate`', implying the `Some(Equal)` arm (which falls through to `truncate`) is a tie-break. However `interval` returns `Some(Equal)` when `d_lo == d_hi`, meaning x is equidistant; in that case both `ceil` and `floor` are equally near, so truncating toward zero is correct. The logic is actually fine — but the `round` doc's arm description is reversed from the code: the match arm `Some(Ordering::Greater) => c.ceil(x)` is reached when `d_lo > d_hi` (closer to upper/ceil), and `Some(Ordering::Less) => c.floor(x)` when `d_lo < d_hi` (closer to lower/floor). This matches the Haskell semantics and is correct. No bug here — downgrading this observation.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3289148315 -->
<!-- glab-discussion: eb864061408d17238fc25ca66c4629181afd2636 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/cast.rs:284` (2026-04-27 10:28 UTC) [open]

**[must-fix]** The `midpoint` doc claims the `lo + (hi - lo) / 2` formula 'avoids overflow at the extreme rungs,' but for an identity `Conn<i32, i32>` at `x = i32::MIN`, `lo = i32::MIN` and `hi = i32::MIN`, so `hi - lo = 0` and the result is `i32::MIN` — fine. However for a non-identity conn where `hi < lo` (saturating / flipped bracket), `hi - lo` underflows silently on signed integers, producing an incorrect midpoint with no panic or indication of failure. The doc should either document this precondition ('only meaningful when `lo ≤ hi`') or guard it, consistent with how `cast_midpoint_between` already vacuously returns `true` when `lo > hi`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3289148420 -->
<!-- glab-discussion: 4a5e5c8a6031c515decbd4c349236de2b8a0aa9f -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/property/laws.rs:657` (2026-04-27 10:28 UTC) [open]

**[follow-up]** As noted in the local review, `cast_round1_id_unit` and `cast_truncate1_id_unit` accept any `Conn<A, B>` but are only universally true for identity Conns; a caller passing a non-identity Conn will get a predicate that silently passes or fails depending on whether `x` is already on a representable rung. The local review (`doc/reviews/review-00026.md`, item 6) tracks adding a `# Warning` note to the rustdoc, but the fix commit `9ff87bd` is listed as addressing only items 1–4. A brief `# Warning` or `# Precondition` section should be added to both predicate docs before merge to prevent misuse by future proptest authors.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3289148506 -->
<!-- glab-discussion: 5430dade44ddd6b4460a22de64182e5b630ec1cf -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/cast.rs:807` (2026-04-27 10:28 UTC) [open]

**[follow-up]** The local review (item 4) flagged the stale `// (and ID_EF64 for NaN-bearing coverage)` comment and the fix commit `9ff87bd` claims to have replaced it with an accurate deferral note, but the diff still shows no updated comment at that location — only the proptest comment block at line ~807 referring to EF64 median deferral. Verify the fix commit actually landed the replacement text; if the stale comment remains it will mislead future readers about what coverage exists.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3289154493 -->
<!-- glab-discussion: fdb133cc1e9a7951965924105a5a8dee9133a493 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/cast.rs:338` (2026-04-27 10:29 UTC) [open]

**[must-fix]** The `round` dispatch is inverted relative to the documented and intended semantics. `interval` returns `d_lo.partial_cmp(&d_hi)` where `d_lo = x - lower(x)` and `d_hi = upper(x) - x`. `Some(Ordering::Greater)` means `d_lo > d_hi`, i.e. `x` is *farther* from the floor and *closer* to the ceil — so the correct dispatch is `Some(Greater) => c.ceil(x)`. The code does exactly this, which matches the local review's analysis in `review-00025.md`. However, the `round` doc comment says "ties broken toward zero (i.e. tie cases delegate to `truncate`)" but the `_` arm (which catches both `Some(Equal)` and `None`) calls `truncate(c, x)` — for `None` (NaN inputs) this silently picks a branch inside `truncate` based on `x >= 0`, which is itself undefined for NaN. The doc says `None` results from "NaN-bearing source values" but does not specify the behavior; a caller reading the doc cannot predict which of `ceil`/`floor` will be returned for NaN inputs. The doc should either specify the NaN behavior or the `None` arm should be handled separately from the tie case.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3289154648 -->
<!-- glab-discussion: 45db30d9fa3c0b1b326a551d6c413ac48a32aeeb -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/property/laws.rs:648` (2026-04-27 10:29 UTC) [open]

**[follow-up]** Both `cast_round1_id_unit` and `cast_truncate1_id_unit` accept any `Conn<A, B>` and any `x: B`, but the doc comments say the equality "holds only when `x` already lies on a representable rung" for non-identity Conns. The local review (`review-00025.md` §Test Coverage) flags this as an API foot-gun: a future proptest driving these predicates over `FD12FD09` would produce spurious failures that look like law violations. Adding a `# Warning` note to the rustdoc — "Only reliable as a law predicate for identity Conns; use `cast_round_picks_endpoint` for general Conns" — would prevent silent misuse without requiring a type-level change.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3289154796 -->
<!-- glab-discussion: 2fcac14e3aacd05d1e07053974592156b5398356 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/cast.rs:260` (2026-04-27 10:29 UTC) [open]

**[follow-up]** The `midpoint` doc comment claims `lo + (hi - lo) / 2` "avoids overflow at the extreme rungs", but for an identity `Conn<i32, i32>` with `x = i32::MAX`, `lo = hi = i32::MAX` and `hi - lo = 0`, so no overflow occurs — the clamp in tests is indeed conservative. However, for a *non-identity* Conn where `hi > lo` and both are near `i32::MAX`, `hi - lo` itself can overflow. The overflow claim in the doc is only correct relative to Haskell's `lo/2 + hi/2` (which overflows the sum), not in an absolute sense. The doc should be scoped: "avoids the intermediate-sum overflow present in `lo/2 + hi/2`" rather than implying the formula is overflow-free in general.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3289189134 -->
<!-- glab-discussion: 28913300125f5bf395771fc17787512bd279d01a -->
#### ↳ cmk (2026-04-27 10:37 UTC) [open]

Acknowledged — the bot self-downgraded mid-comment after working through the dispatch arms. No code change.

<!-- glab-id: 3289189573 -->
<!-- glab-discussion: eb864061408d17238fc25ca66c4629181afd2636 -->
#### ↳ cmk (2026-04-27 10:37 UTC) [open]

Fixed in f873def — midpoint rustdoc now documents the `lo <= hi` precondition explicitly and scopes the overflow claim. The conns this crate ships with injective `inner` satisfy the precondition by construction; saturating conns would underflow on `hi - lo` and are flagged as such.

<!-- glab-id: 3289189979 -->
<!-- glab-discussion: 4a5e5c8a6031c515decbd4c349236de2b8a0aa9f -->
#### ↳ cmk (2026-04-27 10:37 UTC) [open]

Fixed in f873def — added `# Warning` sections to both `cast_round1_id_unit` and `cast_truncate1_id_unit` rustdoc, pointing callers at `cast_round_picks_endpoint` / `cast_truncate_picks_endpoint` for non-identity Conns.

<!-- glab-id: 3289190704 -->
<!-- glab-discussion: 5430dade44ddd6b4460a22de64182e5b630ec1cf -->
#### ↳ cmk (2026-04-27 10:37 UTC) [open]

Bot misread — the comment was replaced in commit 9ff87bd. The current text reads 'Birkhoff median axioms over ORDERED_PAIR. EF64-backed median coverage is deferred (see plan-2026-04-27-04.md Deferred section: ExtendedFloat lacks the arithmetic bounds that would let median compose through it).' No further action.

<!-- glab-id: 3289190889 -->
<!-- glab-discussion: fdb133cc1e9a7951965924105a5a8dee9133a493 -->
#### ↳ cmk (2026-04-27 10:37 UTC) [open]

Fixed in f873def — `round` rustdoc now documents the NaN flow: `partial_cmp` returns `None` on NaN sources, the `_` arm dispatches to `truncate`, and `truncate`'s `x >= 0` is false for NaN, so `round(c, NaN) = c.ceil(NaN)` (typically `Extend(NaN)` preserved through `ceil` for ExtendedFloat conns). Callers needing different NaN handling branch upstream.

<!-- glab-id: 3289191062 -->
<!-- glab-discussion: 45db30d9fa3c0b1b326a551d6c413ac48a32aeeb -->
#### ↳ cmk (2026-04-27 10:37 UTC) [open]

Same fix as the parallel thread — `# Warning` added to both predicates in f873def.

<!-- glab-id: 3289191232 -->
<!-- glab-discussion: 2fcac14e3aacd05d1e07053974592156b5398356 -->
#### ↳ cmk (2026-04-27 10:38 UTC) [open]

Fixed in f873def — midpoint doc now scopes the overflow claim explicitly: 'sidesteps the intermediate-sum overflow that `lo/2 + hi/2` would otherwise hit on near-MAX rungs, but the inner subtraction `hi - lo` can itself overflow when the bracket spans the full type range.'
