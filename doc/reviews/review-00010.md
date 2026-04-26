# MR !10 — Plan 04: Integer + unsigned-integer Galois conns (Word.hs + Int.hs port)

## Summary

Port the within-sign and Word↔Int cross-sign portions of Haskell's
`Data.Connection.Word` and `Data.Connection.Int` — **28 named `Conn`
constants total**. Renames the `word.rs` stub to the Rust-idiomatic
`uint.rs` and populates both `uint.rs` and `int.rs` with the full set of
single-sided unsigned widenings, signed-into-unsigned saturate-at-zero
casts, and range-extended (`Extended<source>`) signed-target conns.

### What changed

- **`src/conn/uint.rs`** (renamed from `word.rs`): 16 `pub const Conn`s.
  Six `U??U??` (unsigned widening, single-sided saturating-narrow inner)
  and ten `I??U??` (signed→unsigned, single-sided, ceil clips negatives
  to 0 and inner saturates at source max). Both expanded from per-family
  declarative macros (`uint_uint!`, `int_uint!`).

- **`src/conn/int.rs`**: 12 `pub const Conn`s. Six `I??I??` (signed
  widening) and six `U??I??` (unsigned source into signed target), all
  full adjoint triples (`Conn::new`) over an `Extended<source>`. Both
  families share one `ext_int!` macro, mirroring the single Haskell
  `conn :: Cast k (Extended a) b` helper.

- **`src/lib.rs`**: extends the type-code legend with `U08`–`U64` and
  `I08`–`I64` rows; adds two integer-conn examples. Notes that integer
  codes name primitives directly (no newtype wrapper) and that
  `U??I??` / `I??I??` constants take `Extended<source>` on the source.

- **`src/conn.rs`**: updates the submodule list (`pub mod uint`) and
  the module-table doc comment.

- **159 new tests** (513 → 672 total): per-family proptest macros emit
  `galois_upper` / `galois_lower` / monotonicity / kernel laws per conn,
  plus consolidated boundary spot checks per family.

### Why

Plans 01–03 stabilised the Galois `Conn<A, B>` core, the
`compose_conn!` macro, the `Extended<T>` wrapper, and the proptest
pattern in `conn::fixed`. The integer side of the lattice atlas was
the missing piece — `word.rs` and `int.rs` were single-line stubs.
With this sprint every primitive integer width becomes a node in a
typed Galois ladder. Closes the third source file from the upstream
Haskell repo (after `Data.Connection.Float` partially via plan 03 and
`Data.Connection.Fixed` via plan 02).

## Test plan

- [ ] `cargo build` clean.
- [ ] `cargo test --workspace` — 672 passing (159 new).
- [ ] `cargo clippy --all-targets -- -D warnings` clean.
- [ ] `cargo fmt --all -- --check` clean.
- [ ] `cargo doc --no-deps` renders the new naming-legend rows and
      examples.
- [ ] Each of the 28 conns satisfies `galois_upper` over its full
      source × target product (`any::<u_N>()` / `any::<i_M>()` /
      `arb_ext_*` for the Extended-source families).
- [ ] Both `kernel_upper` (`ceil(inner(b)) ≤ b`) and `kernel_lower`
      (`b ≤ floor(inner(b))`) hold for the 12 full-triple conns.
- [ ] Spot-check assertions cover ceiling/flooring at `NegInf` /
      `PosInf` / `Finite(MIN)` / `Finite(MAX)` for every source family,
      and the `inner` partition (`x ≤ BELOW` → `NegInf`, `x ≥ ABOVE` →
      `PosInf`, otherwise `Finite`).

## Local review (2026-04-26)

**Branch:** sprint/integer-conns
**Commits:** 4 (origin/main..sprint/integer-conns)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Four commits: `plan:` → `feat:` → `doc:` → `doc:`. The `feat:` commit carries all source changes (28 conns, 159 tests, lib.rs legend, conn.rs rename) in one atomic unit, which is correct given the CLAUDE.md rule that tests must ship in the same commit as the code they cover.

One minor issue: commit `60abadc` is titled `doc: MR !9 description for Plan 04` but the very next commit immediately renames that file from `review-00009.md` to `review-00010.md`. The stale `!9` in the subject is cosmetically confusing in `git log`. Not a quality gate failure, but squashing or reordering these two doc commits would be cleaner.

All four subjects are conventional and under 72 characters. The history is linear.

### Code Quality

**No unsafe code.** `#![forbid(unsafe_code)]` is present in `src/lib.rs` (line 93). Clippy passes clean (`-D warnings`) with no `#[allow(…)]` attributes needed in either new file.

**T1 rename is clean.** `word.rs` is gone; `src/conn.rs` exports `pub mod uint`; the module-table doc comment is updated. No dangling reference to `word` anywhere in the source tree.

**Macro design is sound.** `uint_uint!` and `int_uint!` hand-roll the `if x > cap { cap } else { x }` comparison instead of `min()` to keep the body `const fn`–compatible — the plan's justification (line 101–103) is exactly right. The `ext_int!` macro computes `BELOW`/`ABOVE` as `const` items inside the `const` block; the arithmetic is correct for all six `I??I??` pairs (tested manually: `I32I64`'s `ABOVE = (i32::MAX as i64) + 1 = 2_147_483_648` fits comfortably in `i64`) and all six `U??I??` pairs.

**One doc-level inaccuracy in `src/lib.rs`.** The legend prose (lines 46–50) says `I??I??` and `U??I??` constants "wrap the source in `Extended`" and gives `U08I16` as the example. It does not mention that `I??I??` — signed widening — also takes `Extended<i_N>`. A caller searching for "how do I widen an `i8` to `i16`?" will find `I08I16` in `conn::int` and be surprised that its type is `Conn<Extended<i8>, i16>`, not `Conn<i8, i16>`. An example line — `/// - conn::int::I08I16 — Extended<i8> → i16 (range-extended source)` — would prevent that confusion. This is a documentation gap, not a correctness bug; the deviation is properly explained in the plan's Review section.

No dead code, no redundant logic. `pub const` visibility is correct for all 28 conns.

### Test Coverage

**Property tests are present for all 28 conns** and cover the correct invariants for each family.

*Single-sided family (uint.rs, 16 conns):* `single_sided_props!` emits four properties — `galois_upper`, `ceil_monotone`, `inner_monotone`, `kernel` — and uses the sort idiom `let (lo, hi) = if a1 <= a2 { … }` so every generated pair is exercised. Strategies are `any::<T>()`, which is appropriate since these are plain primitives with no boundary pathology.

*Full-triple family (int.rs, 12 conns):* `ext_int_props!` emits seven properties — `galois_upper`, `galois_lower`, `ceil_monotone`, `floor_monotone`, `inner_monotone`, `kernel_upper`, `kernel_lower`. The `arb_ext!` strategy macro biases 4/12 weight toward `NegInf`, `PosInf`, `Finite(MIN)`, `Finite(MAX)`, matching the plan's 1:1:1:1:8 frequency prescription.

**Monotonicity guard vs sort — mild coverage weakness in int.rs.** `ceil_monotone` and `floor_monotone` in `ext_int_props!` use an `if a1 <= a2 { check }` guard (lines 214–225 of `int.rs`) rather than the sort pattern used in `single_sided_props!`. Since `Extended<T>` is totally ordered, the `if` guard means every trial where `a1 > a2` is silently discarded instead of being rephrased as `ceil(a2) <= ceil(a1)`. In practice the property still runs, but roughly half the generated trials contribute nothing. This matches `inner_monotone` in `int.rs` (which *does* sort, line 229), creating a small internal inconsistency. Not a correctness bug, but the sort idiom should be applied to `ceil_monotone` and `floor_monotone` for consistency.

**Spot checks match the plan's Verification table exactly.** Every assertion in the 12-row spot-check table (plan §Spot checks) is present: `U08I16.ceil(Extended::NegInf) == i16::MIN`, `U08I16.ceil(Extended::PosInf) == 256`, `U08I16.inner(-1) == NegInf`, `U08I16.inner(256) == PosInf`, etc. The `I??I??` family has analogous checks in `int_widening_ceil_at_boundaries`, `int_widening_floor_at_boundaries`, and `int_widening_inner_partitions_target_range`.

**No fixture-gated tests.** All tests are pure computation over primitive types; `fixture_or_skip!` is not applicable here.

**Plan's `inner_then_ceil_is_id` renamed to `kernel`.** The Verification table used `<name>_inner_then_ceil_is_id`; the code calls it `kernel` (uint.rs) and `kernel_upper`/`kernel_lower` (int.rs). The invariant — `ceil(inner(b)) ≤ b` — is identical. Rename is fine; the plan's Review section documents the substitution.

### Plan Conformance

| Task | Planned | Implemented |
|------|---------|-------------|
| T1 — rename word→uint | rename + update conn.rs + lib.rs | Done; `word.rs` absent, `pub mod uint` in place |
| T2 — 6 U??U?? conns | single-sided, `Conn<uN, uM>` | Done; 6 conns, `uint_uint!` macro |
| T3 — 10 I??U?? conns | single-sided, `Conn<iN, uM>` | Done; 10 conns, `int_uint!` macro |
| T4 — 6 I??I?? conns | single-sided, `Conn<iN, iM>` | **Deviated**: full-triple `Conn<Extended<iN>, iM>` |
| T5 — 6 U??I?? conns | full-triple, `Conn<Extended<uN>, iM>` | Done; 6 conns |
| T6 — proptests | 28 conns × 4 props + 6 full-triple extra props | Done; 28 conns, correct property sets |
| T7 — lib.rs legend | 8-row table + note + 2 examples | Done; table present, note present, 2 examples |

**T4 deviation is the most significant change.** The plan specified `I??I??` as plain `Conn<i_N, i_M>` (single-sided, saturating clamp). The implementation changed this to `Conn<Extended<i_N>, i_M>` (full adjoint triple), correctly citing that the saturating-clamp `inner` cannot satisfy the Galois law for target values below `i_N::MIN`. This deviation is documented in the plan's Review section (lines 467–478) and accurately reflected in the MR description. The Haskell reference (`i08i16 :: Cast k (Extended Int8) Int16`) confirms the choice. No objection to the deviation; it is correct and documented.

**`floor_le_ceil` dropped** for Extended-source conns. The plan's Verification table listed this property for the 6 full-triple conns; the implementation drops it and explains why (plan Review lines 480–488: `floor(NegInf) = BELOW < target::MIN = ceil(NegInf)`, so the property does not hold). Replaced by `kernel_upper` + `kernel_lower`, which together with the four adjointness/monotonicity laws fully characterise the triple. Correct and documented.

**galois_lower count expanded.** The Verification table said `galois_lower × 6` (only the original T5 full-triple conns). The implementation applies `galois_lower` to all 12 conns in `int.rs` (both `I??I??` and `U??I??`), since T4 became full-triple too. This is a strictly better outcome.

**End-to-end compose_conn! scenarios** (plan §End-to-end, steps 1–2) are not present as tests. These were illustrative examples in the plan, not rows in the Verification table, so their absence does not constitute a Verification gap. They would make a useful addition.

### Risks

**No TODOs, stubs, or placeholder code.** All 28 conns have full implementations.

**No external security surface.** No file I/O, no shell-outs, no user-supplied input. The macros expand purely at compile time.

**No new runtime dependencies.** `paste` was explicitly not added (plan Review, line 496–498). Proptest remains a dev-dependency only.

**Overflow safety at `ABOVE`/`BELOW` boundaries.** For the widest instantiation (`I32I64`), `ABOVE = (i32::MAX as i64) + 1 = 2_147_483_648` and `BELOW = (i32::MIN as i64) - 1 = -2_147_483_649`, both of which fit in `i64`. The macro comment (int.rs lines 38–42) documents the constraint; no panic possible at const-evaluation time.

**Existing tests unaffected.** The only modification to `src/conn.rs` is the `pub mod word` → `pub mod uint` rename and the updated doc comment. No existing consumer of `conn::word` existed (the module was a stub), so the rename has zero downstream impact.

### Recommendations

**Must fix before push:** None. The suite is green, Clippy is clean, all 28 conns are implemented, all planned properties are covered, and the one significant design deviation (T4 Extended) is correctly justified and documented.

**Follow-up (future work):**

1. `src/lib.rs` — add a named example for `I08I16` (`Extended<i8> → i16`) alongside the existing `U08I16` example. The signed-widening family is likely to be the first thing a new user reaches for; the `Extended<i_N>` source type will be a surprise without a concrete example. (`src/lib.rs`, lines 61–62)

2. `src/conn/int.rs`, `ceil_monotone` / `floor_monotone` in `ext_int_props!` — replace the `if a1 <= a2 { check }` guard pattern (lines 214–225) with the sort pattern used elsewhere (`let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) }`). For a totally ordered source this doesn't affect correctness, but the inconsistency with `single_sided_props!` and with `inner_monotone` in the same macro is confusing and wastes half the generated trials.

3. Consider an end-to-end `compose_conn!` smoke test composing two integer conns (e.g., `U08U64 via U08U16, U16U64`) as the plan's §End-to-end described. The plan left this out; it's low-effort and makes the interoperability story concrete.

<!-- glab-id: 3287363071 -->
<!-- glab-discussion: cbdcbc08f862e688867021a25e1b8f5087deb9c5 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/int.rs:214` (2026-04-26 10:21 UTC) [open]

**[follow-up]** The `ceil_monotone` and `floor_monotone` properties in `ext_int_props!` use an `if a1 <= a2 { check }` guard (silently discarding trials where `a1 > a2`) instead of the sort pattern used in `inner_monotone` (line 229) and in the analogous `single_sided_props!` macro in `uint.rs`. Since `Extended<T>` is totally ordered, the sort idiom would double effective trial coverage and remove the internal inconsistency. The local review already flags this as a follow-up recommendation.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287363077 -->
<!-- glab-discussion: 0a5dae6256d91b6da30a41cb3b90684bf38282bf -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/lib.rs:46` (2026-04-26 10:21 UTC) [open]

**[follow-up]** The prose note says `I??I??` and `U??I??` wrap the source in `Extended`, but gives only `U08I16` as a concrete example (line 65); the signed-widening family (`I??I??`, e.g. `I08I16 : Conn<Extended<i8>, i16>`) has no example. A user reaching for `I08I16` expecting `Conn<i8, i16>` will be surprised; adding a second example line for `I08I16` alongside `U08I16` would close the gap the local review already identifies.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287364713 -->
<!-- glab-discussion: cbdcbc08f862e688867021a25e1b8f5087deb9c5 -->
#### ↳ cmk (2026-04-26 10:24 UTC) [open]

Fixed in e498624 — `ceil_monotone` and `floor_monotone` now use the sort idiom `let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) }`, matching `inner_monotone` in the same macro and `single_sided_props!` in uint.rs. No more silent trial discards.

<!-- glab-id: 3287364780 -->
<!-- glab-discussion: 0a5dae6256d91b6da30a41cb3b90684bf38282bf -->
#### ↳ cmk (2026-04-26 10:24 UTC) [open]

Fixed in e498624 — added a `conn::int::I08I16` example next to `U08I16` so the signed-widening family's `Extended<i_N>` source is visible directly in the legend.

<!-- glab-id: 3287365925 -->
<!-- glab-discussion: 847fa773e26f4e42f93894f846c56ede14fc003a -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/int.rs:52` (2026-04-26 10:26 UTC) [open]

**[must-fix]** The `inner` function uses `x <= BELOW` to detect the NegInf region, but `BELOW` is defined as `(<$A>::MIN as $B) - 1`. For the `I08I16` instantiation this works fine, but the **condition is logically too broad**: `inner` maps `x <= BELOW` to `NegInf` and `x >= ABOVE` to `PosInf`; the claimed Galois law requires that `inner` maps `x` to `NegInf` exactly when `x < ceil(NegInf) = i_M::MIN`, yet `i_M::MIN <= BELOW` is always true so all `x <= BELOW` (not just `x < i_M::MIN`) map to `NegInf`. The real issue surfaces at `x = i_M::MIN`: `inner(i_M::MIN) = NegInf` and `ceil(NegInf) = i_M::MIN`, so `galois_upper` requires `ceil(NegInf) <= i_M::MIN` iff `NegInf <= inner(i_M::MIN)`, i.e. `i_M::MIN <= i_M::MIN` iff `NegInf <= NegInf` — this holds. However the *spot check* at line 150 (`I08I16.inner(i16::MIN) == Extended::NegInf`) is only correct because `i16::MIN <= BELOW = -129` is **false** (`i16::MIN = -32768 <= -129` is true), so the test actually passes, but the semantics are: every value below -128 (the source min) — including -32768 — collapses to `NegInf`, which is the intended behaviour. Verify this is intentional by cross-checking against the Haskell reference; as stated in the module doc the NegInf region is `x <= BELOW` which means `-32768..-129` all become `NegInf`, matching the plan's spec. No bug here — but the `inner` boundary condition uses `<=` (inclusive) for `BELOW` and `>=` (inclusive) for `ABOVE`, meaning the values `BELOW` and `ABOVE` themselves map to the infinities rather than to `Finite`. This is correct per the adjoint law but is undocumented and may mislead maintainers adding future conns; add a comment noting that `BELOW` and `ABOVE` are themselves in the infinity regions.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287365929 -->
<!-- glab-discussion: e79d4637b4e994e9ce71a3f9ec67aa616381af9b -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/uint.rs:79` (2026-04-26 10:26 UTC) [open]

**[must-fix]** The `I??U??` family (`int_uint!` macro) builds a `Conn::new_left(ceil, inner)` where `ceil(x) = 0` for all `x < 0`. This means the Galois law `ceil(a) <= b <=> a <= inner(b)` must hold for all `(a, b)`. Consider `a = -1, b = 0`: `ceil(-1) = 0 <= 0` is true, so we need `(-1) <= inner(0)`. `inner(0) = 0 as $A` which for `I08U08` is `0i8`, and `-1 <= 0i8` is true — OK. But now `a = i8::MIN = -128, b = 0`: `ceil(-128) = 0 <= 0` is true, requiring `-128 <= inner(0) = 0` — true. And `a = -1, b`: for any `b`, `ceil(-1) = 0 <= b` is `b >= 0`, always true since `b: u*` — so we need `-1 <= inner(b)` always, and `inner(b): i8` is always `>= -128` and since it's non-negative (cap-clipped from `u*`), always `>= 0 > -1` — OK. The law holds for all negative `a`. However the `galois_upper` proptest uses `prop_assert_eq!(CONN.ceil(a) <= b, a <= CONN.inner(b))` — this is testing *equality of two booleans*, which is correct. The `ceil` side returning `0` for all negatives means every negative `a` is in the same "equivalence class" under `ceil`, and `inner(b)` for all `b` is non-negative, so `a <= inner(b)` is always true for negative `a` — consistent. The law is satisfied. No bug, but the `galois_upper` property is weaker than it looks for the `I??U??` family since negative `a` values never exercise the `ceil(a) > 0` branch; consider adding a spot check that explicitly verifies `ceil(a) <= b` and `a <= inner(b)` agree for a mid-range positive `a`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287365932 -->
<!-- glab-discussion: 70e988e641bb043f2d39956f728d8fb501c15c16 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/int.rs:95` (2026-04-26 10:26 UTC) [open]

**[follow-up]** The plan's Verification table (plan line 370) specifies `<name>_floor_le_ceil × 6` as a property that must pass for the sprint to ship, but the Review section (plan line 480) documents dropping it and replacing it with `kernel_upper`/`kernel_lower`. The CLAUDE.md convention (§TDD workflow step 13) requires that any dropped property have its reason and re-enablement plan documented in the plan's Review section before merge — the plan does document the reason, but does not provide a re-enablement plan (i.e. no statement of whether this property is permanently inapplicable or would be reinstated under a different formulation). Add a note to the plan's Review section explicitly stating that `floor_le_ceil` is permanently inapplicable for full-triple Extended-source conns (not just deferred), so future reviewers don't expect it to be re-enabled.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287365937 -->
<!-- glab-discussion: 2904fe7c31a8b352284615e5755a8dddbaef381d -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `doc/reviews/review-00010.md:159` (2026-04-26 10:26 UTC) [open]

**[follow-up]** The review doc records the author's reply (line 159, cmk 2026-04-26 10:24 UTC) as fixing `ceil_monotone`/`floor_monotone` in commit `e498624`, but that commit does not appear in the MR diff — the `ext_int_props!` macro in the submitted `src/conn/int.rs` already shows the sort idiom at lines 214–225 (the `let (lo, hi) = ...` pattern). Either the fix was squashed into the `feat:` commit before the diff was generated (obscuring the history) or the review reply references a commit that hasn't been pushed. Per the CLAUDE.md workflow (step 10), reply commits should be a single unpushed fix commit — verify the fix commit `e498624` is included in the branch and not missing from the pushed diff.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287368930 -->
<!-- glab-discussion: 847fa773e26f4e42f93894f846c56ede14fc003a -->
#### ↳ cmk (2026-04-26 10:31 UTC) [open]

Comment added in 66fe0ff inside the `ext_int!` const block: `BELOW` and `ABOVE` are themselves in the infinity regions (inclusive `<=` / `>=`); `Finite(_)` covers only the open interval `(BELOW, ABOVE)`. Tagging this `[must-fix]` was inflated — your own analysis concludes there is no bug.

<!-- glab-id: 3287368951 -->
<!-- glab-discussion: e79d4637b4e994e9ce71a3f9ec67aa616381af9b -->
#### ↳ cmk (2026-04-26 10:31 UTC) [open]

Added `int_uint_galois_at_mid_positive` in 66fe0ff — fixes (50, 100), (50, 49), (100, 100) as representative non-boundary points to complement proptest's boundary-skewed `any::<iN>()`. As with the sibling thread, `[must-fix]` was inflated — your own analysis confirms the law holds.

<!-- glab-id: 3287368964 -->
<!-- glab-discussion: 70e988e641bb043f2d39956f728d8fb501c15c16 -->
#### ↳ cmk (2026-04-26 10:32 UTC) [open]

Plan Review section updated in 66fe0ff to state that `floor_le_ceil` is permanently inapplicable for full-triple Extended-source conns — intrinsic to non-injective `inner` whenever the source is range-extended, no re-enablement plan, future conns of the same shape should use the same six-property contract.

<!-- glab-id: 3287368979 -->
<!-- glab-discussion: 2904fe7c31a8b352284615e5755a8dddbaef381d -->
#### ↳ cmk (2026-04-26 10:32 UTC) [open]

GitLab's MR diff is cumulative `branch...main`, not per-commit, so what you see at lines 214–225 is the post-fix state — that's exactly why the sort idiom appears there. Commit `e498624` was the round-1 fix; it was amended to `e39cb45` when `/reply-reviews` folded the reply-mirror in (per CLAUDE.md TDD step 10) and then pushed. No squash, no missing commits — `git log origin/main..sprint/integer-conns` shows both `e39cb45` and the round-2 `66fe0ff`.

<!-- glab-id: 3287373976 -->
<!-- glab-discussion: c242d33de47dee1cdf5753649d8251c04f74fa2f -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/uint.rs:183` (2026-04-26 10:42 UTC) [open]

**[follow-up]** The `int_uint_galois_at_mid_positive` test (lines 183–193) compares `I08U16.ceil(a) <= b` against `a as i32 <= I08U16.inner(b) as i32` — it widens both sides to `i32` to avoid sign-compare issues, but the `galois_upper` proptest in `single_sided_props!` uses `prop_assert_eq!($CONN.ceil(a) <= b, a <= $CONN.inner(b))` which compares `bool` values directly (no cast). The hand-rolled spot check uses a different comparison strategy than the property test for the same law; if the types involved ever differ in surprising ways this inconsistency could hide a real discrepancy. Both expressions should express the identical condition.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287373982 -->
<!-- glab-discussion: ede64199a23cc3d4ce025ce19b3b9de84cbcbed4 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/int.rs:56` (2026-04-26 10:42 UTC) [open]

**[must-fix]** For the `I??I??` (signed widening) instantiations, `BELOW = (<$A>::MIN as $B) - 1` is computed at `const` time. For `I08I16` this is `(-128i16) - 1 = -129`, which fits. But consider `I32I64`: `BELOW = (i32::MIN as i64) - 1 = -2_147_483_649`, which also fits in `i64`. However the macro comment says the constraint is `bits($A) < bits($B)`, which is satisfied, so all six `I??I??` pairs are safe. The concern is that the macro is also used for `U??I??` where `BELOW = (<u_N>::MIN as $B) - 1 = (0 as $B) - 1 = -1`, which is fine, but `ABOVE = (<u_N>::MAX as $B) + 1` — for `U32I64` this is `(4_294_967_295i64) + 1 = 4_294_967_296`, which fits. All six are safe. The actual bug: the macro constraint comment (lines 45–47) says `bits($A) < bits($B)` for signed source, but `I08I16` has `bits(i8)=8 < bits(i16)=16` ✓. This is fine — but there is **no compile-time check** enforcing the constraint, so a future caller like `ext_int!(I64I64, i64, i64)` would cause `BELOW = i64::MIN - 1` to overflow at const-evaluation time with a hard-to-diagnose panic rather than a clear error. Add a `const _: () = assert!(...)` guard inside the macro body checking `<$A>::MIN as $B > <$B>::MIN` to catch this at compile time.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287373987 -->
<!-- glab-discussion: eb9508083f283bc7557e43ca980c5b5a84e3c7c4 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/int.rs:70` (2026-04-26 10:42 UTC) [open]

**[follow-up]** The module doc comment table (lines 20–24) states that `I??I??` requires `bits(i_N) < bits(i_M)` (strict inequality) and `U??I??` requires `bits(u_N) < bits(i_M)` (strict). The `I08U08` conn in `uint.rs` instantiates `int_uint!(I08U08, i8, u8)` where `bits(i8) = bits(u8) = 8` — same width — which is legal for `I??U??` because the positive half of `i8` fits in `u8`. But the `int.rs` doc comment could mislead a reader into thinking strict-less-than is always required for the cross-sign case; a clarifying parenthetical `(positive half of source fits in target)` would match the actual constraint.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287375883 -->
<!-- glab-discussion: c242d33de47dee1cdf5753649d8251c04f74fa2f -->
#### ↳ cmk (2026-04-26 10:47 UTC) [open]

Fixed in 841345f — dropped the `as i32` cast on both sides; the spot check now compares `i8 <= i8` directly, matching the form the `single_sided_props!` proptest uses.

<!-- glab-id: 3287375910 -->
<!-- glab-discussion: ede64199a23cc3d4ce025ce19b3b9de84cbcbed4 -->
#### ↳ cmk (2026-04-26 10:47 UTC) [open]

Pushing back: your walk-through confirms all six current instantiations are safe and finds no actual bug — the suggested `const _: () = assert!(...)` is defensive coding for a hypothetical future misuse, not a `must-fix`. The macro is private, used in one file with a fixed set of call sites; the comment-level constraint at lines 38–43 is sufficient until/unless someone adds a new pair.

<!-- glab-id: 3287375951 -->
<!-- glab-discussion: eb9508083f283bc7557e43ca980c5b5a84e3c7c4 -->
#### ↳ cmk (2026-04-26 10:47 UTC) [open]

Pushing back: `int.rs` documents only the conns it owns (`I??I??` and `U??I??`), where strict `bits < bits` is correct — the unsigned-source-into-signed-target case requires the source to fit in the target's positive half, forcing strict less-than. The `I??U??` family lives in `uint.rs` and that file's module-doc correctly documents its `bits <= bits` constraint. The two files describe different families with different rules.
