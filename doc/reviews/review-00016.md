# MR !16 — Port `Cast.hs` accessors and lifters (Sprint A)

## Summary

- Add `conn::cast` — 14 free functions porting the L-side
  (`upper`/`upper1`/`upper2`/`ceiling`/`ceiling1`/`ceiling2`/`maximize`)
  and R-side (`lower`/`lower1`/`lower2`/`floor`/`floor1`/`floor2`/
  `minimize`) accessor + lifter API from Haskell `Data.Connection.Cast`.
  Both naming conventions live as free functions on the unified
  `Conn<A, B>` (which always carries the full triple `ceil ⊣ inner ⊣
  floor`); the Haskell `Side` data kind is deliberately not ported.
- Re-export the Cast API at the crate root so callers write
  `connections::ceiling(&c, x)` rather than reaching into
  `connections::conn::cast::ceiling`.
- Add 8 new `cast_*` law predicates to `property::laws`
  (`cast_upper1_id_unit`, `cast_lower1_id_counit`,
  `cast_ceiling1_id_kernel`, `cast_floor1_id_kernel`, plus
  `cast_*2_id_diag` for the binary lifters), each routed through the
  lifter under test. 38 new proptest blocks (8 predicates × 3 conn
  bases — `Conn::<i32, i32>::identity()`, `Conn::<f64, f64>::identity()`,
  and the non-trivial triple `F12F09`) plus deterministic spot checks.
  Total: 1298 lib tests (up from 1260) + 11 doctests.
- Rewrite `README.md` as a Rust-native landing page (Rust-native
  motivations: gaps in `as`/`From`, round-trip law guarantees, ladder
  ergonomics; quick tour with five examples; status table; relationship
  to the upstream Haskell library). The README is wired into `lib.rs`
  via `#![doc = include_str!]` so `cargo test --doc` compile-checks
  every example.
- Append a `doc/design.md` section "Cast: L/R as a naming axis, not a
  type axis" documenting why no `CastR` constructor was added (the
  Haskell library has 122 L-only concrete connections vs **0** R-only,
  so the unified `Conn` already covers every use case without a
  type-level split).

## Test plan

- [ ] `cargo test --workspace` — 1298 tests pass (up from 1260; 38
      new proptest blocks).
- [ ] `cargo test --doc` — 11 doctests pass (up from 5; README rust
      blocks are now compile-checked).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo doc --no-deps` — clean (one pre-existing warning on
      `src/property/mod.rs:8` about `[arb]` link gating; not
      introduced by this MR).
- [ ] Pre-commit hook green on every commit.
- [ ] Manual smoke:
      `connections::ceiling(&F12F09, Pico(1_500))` returns
      `F12F09.ceil(Pico(1_500))`; `connections::maximize(&ord_pair,
      3, 5)` returns `5` for the obvious `Conn<(i32, i32), i32>`
      built from `(max, diag, min)`.
