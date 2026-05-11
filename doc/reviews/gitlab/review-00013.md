# MR !13 — `fixed`-crate-native binary Galois conns (i08/i16/i32/i64)

## Summary

- Add `conn::fixed::{i08,i16,i32,i64}` — 66 binary `Conn` constants
  wrapping the upstream `fixed` crate's `FixedI*<Frac>` ladder, each
  total and lawful over the full primitive bit range.
- Blanket `Ple` impls for `fixed::FixedI{8,16,32,64}<F>` slot the new
  constants into the public `property::laws::conn_*` predicate API
  directly. Test suite drives the laws predicates: 9 properties per
  Conn × 66 Conns = **594 generated proptests** + boundary spot checks
  per inner width; no inline `prop_assert*` patterns.
- Document a previously-unstated distinction in `doc/design.md`: the
  triple-only "rounding sandwich" `floor(a) ≤ ceil(a)` is *not* a
  Galois axiom but a side condition requiring injective `inner`. The
  new connections have a saturation plateau on `inner` (Coarse value
  range exceeds Fine's), so they intentionally do not assert it —
  every other Galois axiom holds for every input.

## Test plan

- [ ] `cargo test --workspace` — all 1260 tests pass (594 new +
      existing).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo doc --no-deps` — clean (one pre-existing warning on
      `src/property/mod.rs:8` about `[arb]` link gating; not
      introduced by this MR).
- [ ] Pre-commit hook green on every commit.
- [ ] Manual smoke:
      `connections::property::laws::conn_galois_l(&F08F04, q88, F08F04.floor(q88))`
      where `q88: I8F8` and `F08F04: Conn<FixedI16<U8>, FixedI16<U4>>`.

## Local review (2026-04-26)

**Branch:** sprint/fixed-binary
**Commits:** 3 (origin/main..sprint/fixed-binary)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Three commits, all conventional and atomic. Subjects:
- `66f115f doc: Distinguish Galois axioms from triple-only rounding sandwich` — 58 chars
- `a96d5c2 feat: fixed-crate-native binary Galois conns (i08/i16/i32/i64)` — 59 chars
- `303e044 doc: Plan 07 + MR !13 description for binary-conns sprint` — 55 chars

Each commit is self-contained and buildable. The doc commit landing before the feat commit is the correct order (justification before code). No merge commits in the log.

### Code Quality

**`inner` / `ceil` / `floor` structure** in `src/conn/fixed/i16.rs`: `inner` widens to `i32`, multiplies by `RATIO`, and saturates with explicit clamps before constructing the Fine value — boundary-fixup rationale is documented inline. `ceil` has its fixup at the entry guard (`x.to_bits() == FINE_MIN`); `floor` mirrors it for `FINE_MAX`. The guard comments correctly explain the plateau semantics.

**Ple impls** in `src/conn/fixed.rs`: the four blanket impls each bound on `LeEqU{8,16,32,64}`, which are exactly the constraints `FixedI{8,16,32,64}<F>` enforces internally. No orphan-rule clash; no conflicts with existing `Ple` impls.

**`src/conn/fixed.rs` doc comment**: accurately names all four new sub-modules and describes the `F<dd>F<dd>` naming convention. No stale future-tense placeholder text remains.

No dead code, no `#[allow]` suppression, no comment drift found.

### Test Coverage

All four modules emit exactly the 9 properties promised in the plan via `props_for_pair!`: `galois_l`, `galois_r`, `monotone_l`, `monotone_r`, `closure_l`, `closure_r`, `kernel_l`, `kernel_r`, `idempotent`. Every property is a `prop_assert!(laws::conn_<name>(...))` call with no inline pattern logic.

**Predicate argument ordering**: `conn_galois_l(c, a: A, b: B)` and `conn_galois_r(c, a: A, b: B)` — both take Fine (`A`) first, Coarse (`B`) second. Tests construct `fine = FixedI*::<$FineFrac>` and pass it as the first value, `coarse = FixedI*::<$CoarseFrac>` as the second. Correct throughout. `monotone_l` receives two Fine-side values; `monotone_r` receives two Coarse-side values. Both match the `laws.rs` signatures.

**Invocation counts match pair counts**: i08: 21, i16: 15, i32: 15, i64: 15 → 66 total × 9 = 594 proptests as claimed.

**`conn_floor_le_ceil` is absent** from all four test modules. No test anywhere in the diff asserts it.

**i64 case count cap**: `ProptestConfig::with_cases(64)` is set at the `proptest!` block level. Consistent with the plan.

**Spot check abbreviated** in i08/i32/i64 (only i16 has the full suite). Proptest coverage makes this low-risk; the abbreviated spot checks reduce readability of the boundary arithmetic for future readers.

### Plan Conformance

- **T1**: `doc/design.md` gains the "Triple-only properties and the role of injectivity" section.
- **T2**: All four Frac-level sets match the plan's table exactly. Ple impls added. Laws-driven tests through `property::laws` predicates.
- **T3**: Single `feat:` commit (`a96d5c2`) covers all four modules, Ple impls, and tests.
- **Deferred**: Families B–F, unsigned mirror, i128, decimal totality — all scoped out and absent from the diff.

No code in the diff falls outside the plan scope.

### Risks

**Widening multiplication — all widths safe**:

- i08: `i8::MAX × 256 = 32 512 < i16::MAX`. No overflow before the saturating clamp.
- i16: `i16::MAX × 65 536 = 2 147 418 112 < i32::MAX`. Fits.
- i32: `i32::MAX × 2^32 = 2^63 − 2^32 < i64::MAX`. Fits.
- i64: `i64::MIN × 2^64 = i128::MIN`, which satisfies the saturating clamp; the unsafe `as i64` branch is unreachable.

**SHIFT = full-width** (`F64F00` in i64, `F32F00` in i32, etc.): `1_i128 << 64 = 2^64` fits in i128. `1_i64 << 32 = 2^32` fits in i64. No shift-overflow.

**Strategy coverage**: `any::<i_W>()` generates the full primitive bit range including `MIN`/`MAX`. The boundary fixup paths in `ceil` and `floor` are therefore exercised by proptest in addition to the spot checks.

No test fixtures or external scripts are touched by this diff.

---

### Recommendations

**Must fix before push:** None.

**Follow-up (future work):**

1. The `i08`, `i32`, and `i64` spot-check suites omit named off-grid positive/negative tests. The plan table's `iWW` notation implies per-module parity with `i16`. Consider adding `spot_<conn>_off_grid_{positive,negative}` to each module in a future `test:` commit.
2. The decimal module's `inner` still uses a naked `i64` multiplication that panics in debug mode on out-of-range Coarse input (noted in Deferred). This is pre-existing and out of scope here, but now stands out against the totality-everywhere standard established by this MR.

(One typo fix from the original review — `i16/i16/i64/i128` → `i16/i32/i64/i128` in the plan's T2 description — was applied before push.)


<!-- glab-id: 3287420210 -->
<!-- glab-discussion: 058cf080a5a844518c2a4eb781a62400087fd790 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/fixed/i08.rs:27` (2026-04-26 12:17 UTC) [open]

**[must-fix]** The `ceil` boundary fixup returns `FixedI8::from_bits(FINE_MIN)` (an `i8::MIN` Fine value) instead of `FixedI8::from_bits(i8::MIN)` cast to the **Coarse** type. The return type is `FixedI8<$CoarseFrac>`, so this should be `FixedI8::<$CoarseFrac>::from_bits(i8::MIN)`. As written it compiles only because `FINE_MIN: i8 = i8::MIN` happens to be the same literal, but the semantic intent — returning `Coarse::MIN` — is obscured and structurally wrong: for other widths (i16/i32/i64) the analogous line correctly uses the coarse type's `FINE_MIN` constant as the bit value, but the `from_bits` call constructs a Fine-typed value and relies on implicit coercion. In i16 line 103 the same pattern appears: `FixedI16::from_bits(FINE_MIN)` is returned where the return type is `FixedI16<$CoarseFrac>` — this compiles because `FINE_MIN: i16` and the bit representation of `Coarse::MIN` equals `i16::MIN`, but the intent should be explicit: `FixedI16::<$CoarseFrac>::from_bits(i16::MIN)`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287420219 -->
<!-- glab-discussion: 6e562b3b988d4e563ed00ad55266f35b235bcf1f -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/fixed/i08.rs:51` (2026-04-26 12:17 UTC) [open]

**[must-fix]** The `floor` boundary fixup guard is `if x.to_bits() == FINE_MAX { return FixedI8::from_bits(FINE_MAX); }`, but `FINE_MAX: i8 = i8::MAX` and the Coarse bit-range maximum is also `i8::MAX` here — this is only coincidentally correct for i8. The symmetry argument in `doc/design.md` and the module doc says `floor(Fine::MAX) = Coarse::MAX`; `Coarse::MAX` in bits is `i8::MAX` only because both sides share the same primitive width. The analogous i16 `floor` (line 131) returns `FixedI16::from_bits(FINE_MAX)` with `FINE_MAX: i16 = i16::MAX`, which equals `Coarse::MAX` in bits for the same reason. This is correct in the current design but should use an explicit `i{W}::MAX` for the Coarse type to make the plateau semantics self-documenting and safe under future refactoring.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287420230 -->
<!-- glab-discussion: 81cc77fef9af8d208ef86fdb38bf62defe3d60b5 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/fixed/i64.rs:21` (2026-04-26 12:17 UTC) [open]

**[must-fix]** For `SHIFT = 64` (the `F64F00` pair), `1_i128 << 64` is well-defined in Rust because `i128` has 128 bits and `64 < 128`, so this does not panic. However the subsequent multiplication `(x.to_bits() as i128) * RATIO` with `RATIO = 1_i128 << 64 = 2^64` and `x.to_bits()` in range `[i64::MIN, i64::MAX]` can produce values up to `i64::MAX * 2^64 ≈ 2^127 - 2^64`, which is within `i128::MAX ≈ 2^127 - 1`. The negative extreme `i64::MIN * 2^64 = -2^63 * 2^64 = -2^127 = i128::MIN` is exactly `i128::MIN` and does not overflow. The local review's risk analysis in `doc/reviews/review-00013.md` states "i64::MIN × 2^64 = i128::MIN, which satisfies the saturating clamp; the unsafe `as i64` branch is unreachable" — this is correct for the negative extreme, but `i64::MAX * 2^64 = (2^63-1)*2^64 = 2^127 - 2^64 < i128::MAX`, also fine. No overflow. However `RATIO` as `i128` for SHIFT=64 means `1_i128 << 64` is computed at compile time in a `const` context — Rust does evaluate this correctly. This is actually safe; downgrade to follow-up to verify via a dedicated spot test that `F64F00.inner(FixedI64::<U0>::from_bits(i64::MIN))` returns `FixedI64::<U64>::from_bits(i64::MIN)` (the negative plateau boundary), which is missing from the current spot checks.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287420233 -->
<!-- glab-discussion: 9069f25faa64366a27f0831f2238d5ccc0aec64a -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/fixed/i64.rs:155` (2026-04-26 12:17 UTC) [open]

**[follow-up]** The `spot_f64f00_degenerate` test checks `inner(0) = 0` and `inner(1) = i64::MAX` but omits the negative plateau boundary: `inner(-1)` should equal `i64::MIN`. The plan's Verification table lists `spot_*_degenerate` as asserting that `±1 saturates inner`, and the i08 module's `spot_f08f00_degenerate` test (line 122) covers both `inner(1)` and `inner(-1)`. The i64 and i32 degenerate spot checks only cover the positive side, leaving the negative saturation path untested by spot checks (proptest will likely catch it, but the asymmetry is a plan-conformance gap).

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287423056 -->
<!-- glab-discussion: 058cf080a5a844518c2a4eb781a62400087fd790 -->
#### ↳ cmk (2026-04-26 12:23 UTC) [open]

Fixed — `ceil` boundary fixups in all four widths now use `FixedIW::<$CoarseFrac>::from_bits(iW::MIN)` explicitly. Behavior was identical (`FINE_MIN` bits equal `Coarse::MIN` bits at the same primitive width) but the explicit form documents intent and survives a future macro generalization where Fine and Coarse widths differ.

<!-- glab-id: 3287423088 -->
<!-- glab-discussion: 6e562b3b988d4e563ed00ad55266f35b235bcf1f -->
#### ↳ cmk (2026-04-26 12:23 UTC) [open]

Same fix — `floor` boundary fixups in all four widths now use explicit `FixedIW::<$CoarseFrac>::from_bits(iW::MAX)`.

<!-- glab-id: 3287423116 -->
<!-- glab-discussion: 81cc77fef9af8d208ef86fdb38bf62defe3d60b5 -->
#### ↳ cmk (2026-04-26 12:23 UTC) [open]

Confirmed safe per your analysis. Added the suggested spot test: `spot_f64f00_degenerate` now asserts `inner(-1) == i64::MIN`.

<!-- glab-id: 3287423145 -->
<!-- glab-discussion: 9069f25faa64366a27f0831f2238d5ccc0aec64a -->
#### ↳ cmk (2026-04-26 12:23 UTC) [open]

Fixed — `inner(-1) == i64::MIN` added to `spot_f64f00_degenerate`. Same assertion added to `spot_f32f00_degenerate` for parity.
