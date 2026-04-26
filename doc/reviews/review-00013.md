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

