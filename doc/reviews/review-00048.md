# MR !48 — Plan 31: Codegen-macro consolidation

## Summary

- Adds three new declaration-form macros — `iso!` (degenerate-Galois
  bijection over a `(forward, back)` pair), `prop::conn::law_battery!`
  (9-property test battery with `full`/`l_only`/`r_only`/`iso_only`
  subset arms and optional `cases: N` proptest config), and
  `connections::macros::*` (feature-gated re-exports of the nine
  internal saturating-cast / NonZero macros) — and migrates every
  existing call site that fits.
- Folds 11 hand-written `pub struct + impl + ViewL + ViewR` blocks
  in `time/duration.rs`, `float/{f32,f16}.rs`, and `addr/ip.rs` into
  the existing `triple!` macro.
- Net: ≈800 LoC removed across `src/` and `tests/`; no behavioral
  change; full test count rose from 1198 → 1230 lib tests because
  `addr::U032IPV4` / `U128IPV6` now run the standard 9-prop battery
  instead of the prior 5-prop hand-rolled subset.

## Test plan

- [x] `cargo test --workspace` — default features, 1198+ tests pass
- [x] `cargo test --workspace --features nix` — Unix-platform Conns
- [x] `cargo test --workspace --features nix,macros,testing` — full
      stable surface
- [x] `cargo test --workspace --no-default-features` — minimal config
- [x] `cargo clippy --all-targets --features nix,macros,testing -D
      warnings` — clean
- [x] `cargo fmt --all -- --check` — clean
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
      --document-private-items --features nix,macros,testing` — no
      broken intra-doc links
- [x] `tests/macros_feature_smoke.rs` — exercises every newly-public
      macro from outside the crate (verifies `$crate::*` path hygiene)

## Local review (2026-04-30)

**Branch:** sprint/macro-consolidation
**Commits:** 7 (origin/main..sprint/macro-consolidation)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All 7 commits use conventional prefixes (`doc:`, `feat:`). The
sequence is clean: plan doc first, then T1–T4 independent feat
commits, then T5 doc polish with a review-skeleton commit. Each
task is atomic — no unrelated changes are mixed.

### Code Quality

- `#![forbid(unsafe_code)]` not violated.
- `#[cfg_attr(feature = "macros", macro_export)]` placement is
  correct on every macro_rules! definition in `src/fixed.rs`.
- `iso!` doc example uses `=>` matching the actual implementation
  (the `<=>` syntax described in the plan was found incompatible
  with `:ty` follow-set rules during T1 and replaced).
- Five `fixed/i*.rs` files keep `#[allow(unused_imports)] use
  crate::extended::Extended` because spot tests in their
  `mod tests` block reference `Extended::Finite` directly. Load-
  bearing.

### Test Coverage

- `addr/ip.rs::U032IPV4` and `U128IPV6` migrations are strictly
  stronger: 5-prop hand-rolled battery → standard 9-prop
  `law_battery!` battery + standalone `floor_le_ceil` spot check.
  No test was dropped.
- Bare-`pub const` Conns (TIMENANO/TIMESECS/DATEJDAY/PDTMDATE/
  OFDTNANO/OFDTSECS) retain their hand-rolled batteries
  (Deferred per plan).
- `tests/fixed_u{8,16,32,64,128}_galois.rs` import removal is
  correct — the macro fully qualifies inside its expansion.
- `tests/macros_feature_smoke.rs` covers all nine newly-public
  macros from outside the crate.

### Plan Conformance

T1–T5 all implemented. Verification table mostly satisfied. Two
spec/implementation deltas:

1. **`r_only` subset emits 4 tests, plan said 5.** The `@batch
   r_only` arm in `src/prop/conn.rs` emits `galois_r`,
   `closure_r`, `kernel_r`, `monotone_r` — no `idempotent`. This
   is correct (idempotent uses the L-side adjoint pair, which
   wouldn't apply to a one-sided R-Conn) but the plan's
   Verification table claimed 5. Documented and fixed below.
2. The promised `tests/iso_macro_smoke.rs` and
   `tests/law_battery_smoke.rs` were consolidated into a single
   `tests/macros_feature_smoke.rs`. Acceptable consolidation.

### Risks

- **`max_shrink_iters: 200` regression for `F064DURN` /
  `F032DURN`.** The pre-migration hand-rolled batteries used
  `ProptestConfig { cases: 64, max_shrink_iters: 200, .. }`. The
  `law_battery!` macro's `cases: N` arm only sets `cases`, leaving
  `max_shrink_iters` at proptest's default (4096). On the rare
  occasion a counterexample is found in these walk-heavy tests,
  shrinking can now run far longer than before. Tests still pass
  cleanly today; this is a latency regression only.
- No broken internal call sites from the `$crate::`-path additions
  (verified by full test suite passing).

### Recommendations

**Must fix before push:**

1. `src/prop/conn.rs::law_battery!` — `r_only` doc table claims
   5 tests; the implementation emits 4. Fix the doc table to
   match (the implementation is correct; only the docs are
   wrong).

**Follow-up (future work):**

2. Add a `max_shrink_iters: M` optional key to `law_battery!`
   so the F064DURN/F032DURN batteries can restore their 200-cap
   shrinking behavior.
3. Plan's Verification table mentions separate
   `tests/iso_macro_smoke.rs` / `tests/law_battery_smoke.rs`
   files; the consolidated `tests/macros_feature_smoke.rs`
   covers the same surface. Update the plan or split into
   two files in a follow-up.
