# Review !20 — `feat: Modularize conn::float and add half-based F016/B016 Conns`

## Summary

- Modularizes `src/conn/float.rs` into the parent + subdirectory shape
  (`conn::float.rs` + `conn::float/{f32,f64}.rs`), mirroring `conn::fixed.rs`
  + `conn::fixed/`. `F064F032` moves into `conn::float::f64`; `f16`/`b16`
  per-source-tier submodules are deferred until they have content.
- Adds four direct precision-narrowing Conns to half-precision via the
  `half` crate: `F032F016`, `F032B016`, `F064F016`, `F064B016`. Each
  goes through `half::{f16,bf16}::from_{f32,f64}` (RNE) and walks ≤ 2
  ULPs on the target side. ULP-walk helpers refactored to return
  `(result, steps)` so a `ulp_steps_bounded` proptest can assert the
  bound. New `F016` / `B016` type aliases swap to native types
  transparently when stable.
- Renames `ExtendedFloat::Finite` → `Extend` (the variant name now
  reflects its lattice role between `Bot` and `Top`, not a numeric
  property of the wrapped value — `NaN` isn't finite). `Extended<T>`
  keeps `Finite` because its wrapped values really are.

## Test plan

- [x] `cargo test --workspace` — 1703 pass (+75 vs main)
- [x] `cargo test --doc` — 23 pass (+4 doctests, including the README
      mirror of `F064B016`)
- [x] `cargo clippy --all-targets -- -D warnings` — clean
- [x] `cargo fmt --all -- --check` — clean on touched files
- [x] `cargo doc --no-deps` — clean (preexisting `arb` link warning
      unrelated to this MR)
- [x] `cargo build --workspace` — clean
- [x] Per-Conn proptest config (cases=256, max_shrink_iters=200)
      keeps shrink-time bounded under the
      [proptest_shrink_tuning](../../) memory's guidance
- [x] `signed16_round_trip` exhaustively sweeps `0u16..=u16::MAX`
- [x] ULP-step bound asserted to be ≤ 2 across all 5 floats Conns
      (the existing F064F032 plus the four new ones)
