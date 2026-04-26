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
