# MR !62 — Plan 39: Kani SMT verification of Galois-connection laws

## Summary

- Adds a `#[cfg(kani)]`-gated proof tree at `src/kani_proofs/`
  (parent `src/kani_proofs.rs`, eight submodules) that promotes the
  proptest-asserted Galois laws on every integer / Q-format /
  NonZero / iso Conn family from sampled spot-checking to
  **SMT-verification over the full bit-width domain**. Each
  `#[kani::proof]` harness is a one-liner calling the existing
  unconditionally-`pub` predicates in `crate::prop::conn` (`galois_l`,
  `monotone_l`, `closure_l`, `kernel_l`, `idempotent_l`, …) on a
  `kani::any::<_>()` symbolic input. Coverage: **604 harnesses, 0
  failures**, dispatching in well under one minute total wall-time.
- The headline Group-2 result — **the f64 → f32 ULP walk in
  `src/float/f32.rs` converges in ≤ 2 iterations for every finite
  non-NaN f64** — is proven via three tiered harnesses
  (`float_walk::t0/t1/t2_*`); T0 covers the unrestricted finite
  domain in ~2s with `#[kani::unwind(4)]`. Two `pub(crate)`
  walk-step probe wrappers gated on `cfg(kani)` make the walk's
  `(z, steps)` tuple visible to the proof; release builds compile
  no proof code.
- `Cargo.toml` gains a one-line
  `[lints.rust] check-cfg = ["cfg(kani)"]` declaration so
  `cargo build` / `cargo test` don't warn about the proof harnesses'
  unknown cfg name. No new dependency: Kani injects its own crate at
  build time when `cargo kani` runs. Two harness predicates that
  don't hold by construction (`uint_sat::roundtrip_floor`,
  `float_weaker::finite_in_finite_out_*` over saturation regimes)
  are documented in their respective files rather than asserted.

## Test plan

- [ ] `cargo install --locked kani-verifier && cargo kani setup` —
      one-time install, unchanged from upstream.
- [ ] `cargo build` — clean, no `unexpected_cfg` warnings.
- [ ] `cargo test --workspace --quiet` — unchanged from baseline
      (proofs are `#[cfg(kani)]`-gated; pre-sprint test count
      preserved).
- [ ] `cargo kani --harness 'int_narrow::'` — 60 / 60 verified.
- [ ] `cargo kani --harness 'uint_sat::'` — 70 / 70 verified.
- [ ] `cargo kani --harness 'nz_ext::'` — 60 / 60 verified.
- [ ] `cargo kani --harness 'iso_family::'` — 50 / 50 verified.
- [ ] `cargo kani --harness 'fix_fix_signed::'` — 230 / 230
      verified (i8 / i16 full ladder; i32 / i64 / i128 boundary
      pairs).
- [ ] `cargo kani --harness 'fix_fix_unsigned::'` — 120 / 120
      verified (u8 representative; u16 / u32 / u64 / u128 boundary
      subsets).
- [ ] `cargo kani --harness 'float_walk::t0_'` — 2 / 2 (headline:
      ULP walks ≤ 2 over all finite non-NaN f64).
- [ ] `cargo kani --harness 'float_walk::t1_'` — 2 / 2 (walks ≤ 1
      on `|x| ≤ 1e6`).
- [ ] `cargo kani --harness 'float_walk::t2_'` — 2 / 2 (walks ≤ 1
      on the `[1, 2)` binade).
- [ ] `cargo kani --harness 'float_weaker::'` — 8 / 8 (finite-domain
      laws after in-range tightening).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `scripts/check-pii.sh` — exits 0.
