# MR !91 — Float → Extended<intN> connections

## Summary

- Ports the Haskell `Data.Connection.Float` Float→Extended-int family to
  Rust: 24 new `Conn` consts spanning f32/f64/f16 sources × {u8,u16,u32,
  u64,i8,i16,i32,i64} targets. Full Galois triples where the target
  fits losslessly in the source mantissa; L-only Conns where it
  doesn't.
- Adds the supporting infrastructure: `float_ext_int!` /
  `float_ext_int_l!` macros (in `src/float.rs`), `shift64` ULP machinery
  matching the existing `shift32`, a `RoundDownFromI128` trait + per-
  float `round_down_to_*` helpers (so `inner` rounds toward `-∞` and
  the L-Galois kernel law holds even when target precision exceeds the
  source mantissa), and the missing
  `arb_extended_{u8,u16,i8,i16,i32}` proptest generators.
- Extends `compose_k!` to accept doc comments and visibility, lets
  composed Conns ship as documented `pub` consts. Used by
  `F064U008`/`F064U016`/`F064I008`/`F064I016` (composed via `F064F032
  ∘ F032<X>`, since narrowing through f32 is exact for ≤16-bit
  targets). f16 source Conns ship direct rather than composed — see
  the deferred-decisions section below.

The Float→FixedI/U Q-format target family (~186 Conns) was deferred
to a follow-up sprint per the plan's "Phase split fallback" (saturate-
and-scale arithmetic across 5 host-int widths × 6–7 frac rungs ×
3 source floats × 2 signs is materially more work than this MR's
24 Conns and warrants its own focused review). The Phase 1 surface
shipped here unblocks the follow-up cleanly: the `RoundDownFromI128`
trait, `shift64`, and the macro layout transfer directly.

## Test plan

- [x] `cargo test --features testing` — all 1339 tests pass on stable.
- [x] `cargo +nightly test --features f16,testing` — all 1462 tests
      pass on nightly (additional 123 f16 tests covering F016U/I*).
- [x] `cargo clippy --all-targets --features testing -- -D warnings` —
      clean.
- [x] `cargo +nightly clippy --all-targets --features f16,testing
      -- -D warnings` — clean.
- [x] `cargo fmt --all --check` — clean.
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features
      testing,macros --document-private-items` — clean (no broken
      intra-doc links).
- [x] Per-Conn law battery: each of the 24 new Conns has a
      `crate::law_battery!` invocation — `subset: full` for triples,
      `subset: l_only` for L-only. Adjoint laws verified across
      `Bot`/`Top`/`Extend(NaN)`/`Extend(±∞)`/`Extend(boundary)`/
      `Finite(MIN)`/`Finite(MAX)`/generic via the existing
      `extended_float_*` and `arb_extended_*` strategies (256
      cases per law).
- [x] Spot tests covering: NaN ceil → PosInf, NaN floor → NegInf,
      ±∞ saturation through `v > hi`/`v < lo` branches,
      `Bot`/`Top` pass-through, exact-integer round-trip,
      sub-integer ceil/floor bracket, composed Conn agrees with
      direct path on a representative input.

## Local review (2026-05-09)

**Branch:** sprint/float-ext-int
**Commits:** 4 (origin/main..sprint/float-ext-int)
**Reviewer:** Claude (sonnet, independent)

---

# Review: `sprint/float-ext-int` vs `origin/main`

Reviewing 4 commits adding 24 Float → `Extended<intN>` Conns and supporting infrastructure.

## P1.A — Trait-Claim Audit

### 1. `float_ext_int!` (full triple, `conn_k!`): F032U008, F032U016, F032I008, F032I016, F064U032, F064I032, F016U008, F016I008

**Contract.** `conn_k!` emits `ConnL + ConnR` on the same marker struct, claiming the full Galois triple: `ceil(a) ≤ b ⟺ a ≤ inner(b)` (L-law) AND `inner(b) ≤ a ⟺ b ≤ floor(a)` (R-law), with `inner` order-reflecting.

**Implementation.** `ceil` matches on `Bot→NegInf, Top→PosInf, Extend(v)→__float_ext_int_ceil_body!`. `inner` maps `NegInf→Bot, PosInf→Top, Finite(i)→Extend(from_i128_rd(i as i128))`. `floor` matches `Bot→NegInf, Top→PosInf, Extend(v)→__float_ext_int_floor_body!`. The `from_i128_rd` path reduces to a no-op (exact cast) when target bits ≤ mantissa digits.

**Consistency.** Consistent. The mantissa threshold is correct: f32 has 24 bits of mantissa (incl. implicit), so u16 (16 bits) and i16 (16 bits) fit losslessly; u32 (32 bits) does not. f64 has 53 bits; u32 fits, u64 does not. f16 has 11 bits; u8 fits, u16 does not. All eight full-triple Conns are correctly classified. The `inner` sentinel mapping to `Bot`/`Top` (not `Extend(±∞)`) is mathematically required: under the N5 ordering `Bot < Extend(-∞)`, so `inner(NegInf) = Extend(-∞)` would break the L-law at `b = NegInf` by making the inequality `a ≤ inner(NegInf)` true for `a = Extend(-∞)` while `ceil(Extend(-∞)) = Finite(MIN) ≰ NegInf`. The implementation is sound.

### 2. `float_ext_int_l!` (L-only, `Conn::new_l`): F032U032, F032U064, F032I032, F032I064, F064U064, F064I064, F016U016, F016U032, F016U064, F016I016, F016I032, F016I064

**Contract.** `Conn::new_l(ceil, inner)` claims only the L-Galois adjunction `ceil(a) ≤ b ⟺ a ≤ inner(b)`, not `order_reflecting` or `floor`.

**Implementation.** Same `ceil` and `inner` as above, no `floor` emitted.

**Consistency.** Consistent. `inner` uses `from_i128_rd` (round-toward-negative-infinity), which ensures `ceil(inner(Finite(b))) ≤ b` (the kernel law) even when RTNE rounding would map `inner(Finite(b))` above `b`. Correctly no `floor` for these Conns. The subset choice `l_only` in the law batteries matches.

### 3. `compose_k!(F064F032, F032{U,I}{008,016})` for F064U008, F064U016, F064I008, F064I016

**Contract.** `compose_k!` emits a unit-struct marker with `ConnL + ConnR` impls that chain the component `conn_l()` / `conn_r()` methods. Claims full adjoint triple.

**Implementation.** `F064F032` is a full triple (existing); `F032U008/U016/I008/I016` are full triples (new). The composition of two full triples is a full triple.

**Consistency.** Consistent. The intermediate type is `F032 = ExtendedFloat<f32>`, the composition chain is type-correct, and narrowing through f32 first is lossless for ≤16-bit integer targets (16 bits < 24-bit f32 mantissa). Law batteries use default `subset` (full). Correct.

## Critical Issues

**None.** The trait-claim audit found no law-claim violations.

## Important Issues

### `RoundDownFromI128` is `pub` in a `pub mod` — it becomes part of the crate's public API

**File:** `src/float.rs:829`.

`pub trait RoundDownFromI128` lives in `float.rs`, which is `pub mod float` in `lib.rs`. This means `connections::float::RoundDownFromI128` is reachable by downstream users. The trait's purpose is as an internal dispatch shim for the macros; its three `impl` blocks are for `f32`, `f64`, and `f16`. There is no downstream use-case for it: the macros that use it are already sealing the type at each float variant. Exposing it as `pub` makes it part of the stable API.

If the intent is to allow downstream crates using `float_ext_int_l!` with a custom float type to supply their own `impl`, then `pub` is correct but must be documented. If the intent is purely internal dispatch, change to `pub(crate)`.

**Concrete fix:** Either add a doc comment making the stability commitment explicit, or change to `pub(crate)`.

### `shift64` has no unit tests; the existing `shift32` tests have direct counterparts

**File:** `src/float.rs:758-768` (and surrounding helpers `signed64`/`unsigned64`/`clamp64`).

`shift64` is new code. The analogous `shift32` has three unit tests: `shift32_from_zero`, `shift32_nan_to_inf`, `shift32_inf_clamped`. None exist for `shift64`. The function is indirectly exercised when `round_down_to_f64` calls it, which is in turn exercised by the L-only law batteries, but the indirect path doesn't test the ULP-step-from-zero, NaN-routing, or clamp-at-infinity behaviors directly.

`shift64` is also marked as Phase 2 infrastructure, so it will carry more weight in the follow-up sprint.

**Concrete fix:** Add `shift64_from_zero`, `shift64_nan_to_inf`, and `shift64_inf_clamped` tests mirroring the existing `shift32_*` tests.

### f016 spot tests are thin compared to f032 and the plan's T11 checklist

**File:** `src/float/f016.rs` test module.

The f032 test module has dedicated spot tests for: NaN → PosInf/NegInf (ceil/floor), `Extend(+∞)` via `v > hi` branch, `Extend(-∞)` via `v < lo` branch, `Bot`/`Top` pass-through, `inner` sentinel round-trip, MIN/MAX saturation, exact integer round-trip, and sub-integer bracket. The f016 module has three spot tests (`f016u008_exact`, `f016u016_max_finite_f16_in_range`, `f016i008_saturate`) and eight law batteries.

The law batteries via `extended_float_f16()` do generate NaN, Bot, Top, and ±∞ inputs proptest-style, so the Galois laws are covered. However the plan's T11 checklist (`NaN, ±Inf, Bot/Top, MAX/MIN saturation, zero / -0 collapse, exact-integer/rung round-trip`) is the spot-check deliverable, and f016 doesn't have it.

Below the bar set by the plan and the f032 precedent. Not a correctness bug given law battery coverage, but leaves f016 harder to diagnose when a law battery does fail.

**Concrete fix:** Add spot tests mirroring `f032.rs::nan_ceil_pos_inf`, `bot_top_pass_through`, and `inner_round_trip_finite` for at least one f16 Conn. The f16-specific case that warrants a dedicated spot test: the `v == INFINITY → PosInf` explicit branch added because `u8::MAX as f16 < +∞` but `u16::MAX as f16 = +∞` — test `F016U016.ceil(Extend(+∞)) == PosInf`.

## Standard Review

### Commit Hygiene

Four commits: `doc:`, `feat:`, `feat:`, `test:` — prefix choices are conventional. Subjects are under 72 characters. The `feat:` commits each land a coherent unit (infrastructure, then Conns). The `test:` commit for arb generators precedes the `feat:` commits that need them. Dependency order is correct.

### Code Quality

- No unsafe code.
- `compose_k!` macro change is backward compatible: `$(#[$meta:meta])* $vis:vis` match zero occurrences cleanly; existing call sites continue working.
- `signed64` / `unsigned64` / `clamp64` values are correct. The comment values in `clamp64` at lines 742-743 are accurate.
- `__float_ext_int_ceil_body!` has an explicit `v == INFINITY` branch before the `v > hi` / `v < lo` comparisons. Required for f16 sources where `INT_MAX as f16` saturates to `+∞`. The implementation is correct. The f32/f64 sources don't need this guard but the unified macro's explicit check is safe for all three.
- `__float_ext_int_floor_body!` has no explicit `+∞` check. For f32/f64 sources this is safe. For f16 sources, `floor` is only invoked for the full-triple Conns `F016U008`/`F016I008`, where `hi = 255.0_f16`/`127.0_f16` (both finite), so `+∞ > hi` fires correctly. No bug.
- The `#[cfg(not(feature = "f16"))] #[allow(unused_imports)] use super::F032;` in `f032.rs` is unusual but harmless.
- `RoundDownFromI128` is used via `<$float as RoundDownFromI128>::from_i128_rd(i as i128)`. The `as i128` upcasts `i8..u64` losslessly. Correct.

### Test Coverage

- All 24 Conns have a `law_battery!` invocation with the correct `subset:` choice.
- `arb_extended_u32` imported in f016 tests includes Unicode-range bias values (`0xD7FF`, `0xE000`, etc.) inherited from the char Conn test design. These values are valid `u32`s and don't invalidate the law battery, but generate values in a narrow `[55295, 65536]` cluster rather than the boundary/random mix the other generators use. Minor quality gap, not a correctness issue.
- The f016 law batteries use `extended_float_f16()` which includes `Bot`, `Top`, `NaN`, `±∞`. Coverage adequate for correctness despite thin spot tests.

### Risks

- `RoundDownFromI128` `pub` trait the only unresolved API-surface question.
- No TODOs or stubs.
- Phase 2 deferred cleanly; infrastructure coherent.
- The plan's documentation of the `v < lo` path for f16 wide-target `ceil(-∞)` is imprecise: for i32 targets, `i32::MIN as f16 = -∞_f16` and `-∞ < -∞` is false, so the code falls to the `else` branch (`Finite((-∞_f16).ceil() as i32)`), not the `v < lo` arm. Result is correct (Rust's saturating cast makes `-∞ as i32 = i32::MIN`), but the doc traces the wrong code path. Doc inaccuracy, not a code bug.

## P2.A — Test-Exception Escalation

The plan's Review section states: **"#[ignore]d properties: none."** The diff confirms this. No relaxed/weakened predicates in test names. Plan's Verification table lists the full law battery and the subset choices match the shipped code. No escalation needed.

## P2.B — Plan Conformance

- **T0**: Outcome documented; option (c) for f16, option (a) for f64 narrow targets. Shipped code matches.
- **T1**: 5 `arb_extended_*` generators (`u8, u16, i8, i16, i32`). All present.
- **T2 / T3**: `float_ext_int!` and `float_ext_int_l!` macros present.
- **T4**: 8 f32 Conns. Correct.
- **T5**: 4 direct + 4 composed f64 Conns. Correct.
- **T6**: 8 f16 Conns direct. Correct (option (c) per T0).
- **T7–T10**: Deferred. Phase split fallback applied. Coherent.
- **T11**: Law batteries present for all 24 Conns. Spot tests comprehensive for f032/f064; sparse for f016 (see Important Issues).
- **Design deviations**: All three listed and correctly implemented.
- **Extra code**: `shift64` ULP machinery. Justified emergent work (needed by `round_down_to_f64`), not scope creep.

## Recommendations

**Must fix before push:**

1. **`RoundDownFromI128` visibility** (`src/float.rs:829`): Change `pub trait RoundDownFromI128` to `pub(crate)` unless it is intentionally part of the stable downstream API. If `pub` is correct, add a doc comment declaring stability intent.

2. **`shift64` unit tests** (`src/float.rs`): Add `shift64_from_zero`, `shift64_nan_to_inf`, and `shift64_inf_clamped` mirroring the existing `shift32_*` tests at lines 1377-1395.

**Follow-up (future work):**

3. **f016 spot tests**: Add at least `nan_ceil_pos_inf`, `bot_top_pass_through`, `inner_round_trip_sentinels`, and `f016u016_pos_inf_ceil` to `src/float/f016.rs` tests.

4. **Plan doc inaccuracy on f16 `ceil(-∞)` path**: The Review §Design-deviations item #2 traces a code path that doesn't fire (the `v < lo` branch). The result is correct but the doc traces the wrong arm. Fix the comment in the plan or add an inline comment in `__float_ext_int_ceil_body!`.

5. **`arb_extended_u32` Unicode bias**: Consider extracting a plain `arb_extended_u32_plain()` without Unicode-specific bias for use in float-to-int tests, or accept the current distribution.
