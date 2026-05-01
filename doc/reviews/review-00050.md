# MR !50 — Plan 32: `floor_le_ceil` cleanup — demote ~140 non-triple Conns to ConnL

## Summary

- A connection labeled as a **triple marker** (impl `ViewL` + `ViewR`) is
  a true adjoint triple iff its middle adjoint `inner` is order-reflecting,
  iff `floor(a) ≤ ceil(a)` for every `a` (proof in
  `prop::conn::floor_le_ceil` docstring; both directions are elementary
  applications of the per-side adjunction laws + monotonicity). Connections
  failing the rounding sandwich aren't triples — and the two-sided helpers
  (`round`, `truncate`, `interval`, `midpoint`) inherit the inverted
  bracket and produce wildly wrong answers (e.g. previously
  `Q004Q000.round(7.9375) = 127`).
- This MR demotes **~140 connections** whose `inner` is non-injective from
  `triple!` to `Conn::new_l`, splits across 5 commits (T1 STDRU128 = 1 Conn;
  T2 `ext_int!` macro = 14 widening Conns; T3 `fix_fix_*!` macros across 9
  host-type modules = ~119 Q-format Conns; T4–T5 the four float↔duration
  Conns the strengthened battery surfaced as latent failures; T6 docs).
- Strengthens `prop::conn::law_battery!`'s `full` subset to require
  `floor_le_ceil` so future triple markers can't silently re-introduce the
  flaw. Every remaining triple (`DURNSECS`, `STDRU064`, `U032CHAR`,
  `U032IPV4`, `U128IPV6`, `IPV6IPV4`, `F064F032`, plus f16-gated
  `F064F016`/`F032F016`) passes the strengthened battery — they're true
  triples.
- Breaking change: callers of `.floor()` on any demoted Conn will see a
  compile error (the method literally doesn't exist on `ConnL`). This is
  the desired outcome — explicit at compile time vs. wrong answer at
  runtime. Migration guidance documented in the CHANGELOG entry.

## Test plan

- [x] `cargo test --workspace` — 2300+ tests pass (lib, integration,
      doctests, compile_fail). Test count drop from ~3000 → ~2300 reflects
      the 4 R-side proptests dropped per demoted Conn (~560), minus added
      boundary spot tests (~5) and the new `floor_le_ceil` checks in `full`
      (~7).
- [x] `cargo clippy --all-targets -- -D warnings` — clean
- [x] `cargo fmt --all -- --check` — clean
- [x] `bash scripts/check_readme_mirror.sh` — clean
- [x] STDRU128 boundary spot test (`stdru128_kernel_l_at_above_max_boundary`)
      explicitly probes `Finite(max_nanos + 1)` and `Finite(u128::MAX)`,
      pinning the previously-broken case
- [x] `compile_fail/round_on_l_conn.stderr` re-blessed (the trait-impl-list
      portion of the error message changed when the demoted markers'
      `ViewR` impls disappeared)
