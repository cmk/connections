# MR !68 — feat: Sprint 4 hifi/epoch.rs §4 relativistic scales (Plan 45)

## Summary

- Add `ETDTF064`, `ETDEF064`, `ETDBF064` — F064-only `Conn`s for the
  TT, NAIF SPICE ET, and ESA TDB time scales. F064-only (not the
  master plan's HDUR/NANO triple) because TT's +32.184 s offset
  saturates `Duration::add` at `HD::MAX` and ET/TDB are lossy at the
  ≤1 ns level under hifitime's instant-based `Eq` — both make the
  integer-Duration projections imply false precision. F064 walks
  absorb the imprecision via the established 1 ns ULP descent.
- Extend Kani SMT verification with the `f64_etdt_walks` step-bound
  tier (T1 + T2; T0 deferred per the established `f64_etai_walks`
  pattern). ET / TDB walks defer entirely — their widens call
  `f64::sin` inside iterative loops, which CBMC can't symex.
- 16 new property tests (5 ConnL laws × 3 Conns + spot checks +
  J2000 ≤ 1 ns drift assertions). All 1370 lib tests pass.

## Test plan

- [ ] `cargo build --features hifi`
- [ ] `cargo test --features hifi,testing`
- [ ] `cargo clippy --all-targets --features hifi,testing -- -D warnings`
- [ ] `cargo doc --features testing --no-deps --document-private-items`
      with `RUSTDOCFLAGS=-D warnings`
- [ ] `cargo build --no-default-features` (feature truly optional)
- [ ] `cargo kani --features hifi --harness '*etdt*'` —
      `t1_f64_etdt_walk_steps_le_1`, `t2_f64_etdt_walk_steps_unit_binade`
      verify

## Local review (2026-05-07)

**Branch:** sprint/hifi-relativistic
**Commits:** 1 (origin/main..sprint/hifi-relativistic)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Single commit `4b54a7c feat: Add hifi/epoch.rs §4 — relativistic
scale Conns (Plan 45)`. Subject is conventional, under 72 chars,
uses correct `feat:` prefix. The commit includes plan doc, review
doc, implementation, and tests together — appropriately atomic.
All gates pass.

### Code Quality

The code is structurally sound and follows the §3 BDT template
faithfully. No unsafe code. The `j2000_tai_ns()` helper is correctly
placed and its usage in `et_max_secs_f64()` is correct. The
`TT_OFFSET_NS = 32_184_000_000` (32.184 s in nanoseconds) correctly
matches `hifitime::TT_OFFSET_MS = 32_184` (milliseconds). The
`tt_max_nanos()` subtracting `TT_OFFSET_NS` from `hd_max_nanos()`
correctly guards the upper boundary so the fast-path intercepts
inputs that would saturate. Consistent with the plan's analysis.

The Kani probes follow the existing pattern exactly. ET/TDB Kani
deferral is documented both in `hifi_walk.rs` and the plan.

The deferred items (`ETDTHDUR`/`ETDTNANO`/`ETDEHDUR`/etc.) are
documented in three places: the §4 banner, `hifi.rs` module doc,
and the plan's Deferred section.

### Test Coverage

15 proptest laws (5 × 3 Conns) plus 10 spot checks plus 2 J2000
round-trip checks. The proptest count matches the Verification
table. The J2000 round-trip tests exercise the only place where
hifitime's iterative imprecision is non-trivial (per hifitime's
own tests). The §4 comment block correctly explains why a bounded
proptest isn't more meaningful than the J2000 spot check.

### Plan Conformance

T1–T8 all present. Test names differ from plan's Verification
table (see follow-up #3) but the diff fully covers the planned
property + spot-check matrix.

### Risks

None blocking. No TODOs, no stubs. The deferred items are
documented in three places.

---

### Must fix before push

**1. Doctest uses strict `<` where the contract is `≤ 1 ns`**

`src/hifi/epoch.rs` ETDEF064 / ETDBF064 doctests:
```rust
assert!((got - j2000_et).abs() < 1.0 * hifitime::Unit::Nanosecond);
```

The doc comments for both Conns say "precise to **≤ 1 ns**"; the
unit tests use `<=`. If hifitime's actual round-trip drift is
exactly 1 ns, the doctest fails while the unit test passes.

**Resolution (2026-05-07):** Fixed in this commit — both doctests
now use `<=` to match the stated contract and the unit tests.

**2. Misleading comment: `et_min_secs_f64()` is not anchored at j2000**

The comment "Same asymmetric bounds as the GNSS scales, anchored at
`j2000_tai_ns()`" implies both bounds involve j2000; only the max
is. The GNSS comment at line 660 is clearer.

**Resolution (2026-05-07):** Fixed in this commit — comment
reworded to mirror the GNSS pattern, explicitly calling out
unshifted min and j2000-shifted max.

### Follow-up (future work)

**3. Plan's Verification table names don't match shipped test names**

`etdef064_zero_is_j2000_et` shipped as `etdef064_zero_is_near_j2000`;
`etdef064_round_trip` (described as proptest) shipped as `#[test]`
spot check `etdef064_at_j2000_within_1ns`. Acceptable for this push
since the in-code comment explains the design decision. Plan's
Review section should note these deviations in a follow-up.

**4. `etdef064_nan_inf_bot_top` and `etdbf064_nan_inf_bot_top`
missing `f64::INFINITY` arm**

Both tests omit the `f64::INFINITY → PosInf` case that
`etdtf064_nan_inf_bot_top` and the GNSS analogs cover. Galois_l
proptest provides coverage via `extended_float_f64()`; not a
correctness gap, just a visual symmetry break.
