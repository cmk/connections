# MR !45 — Plan 29: Phantom kind tag + 2-fn Conn with marker-type triples

## Summary

- Reshape `Conn` to a strict 2-fn-pointer struct kind-tagged by `L` /
  `R`, with adjoint triples encoded as zero-sized marker types
  implementing `ViewL` / `ViewR` projection traits. Mirrors Haskell's
  `Cast (k :: Side) a b` discipline at the type level: kind-mismatched
  predicate / accessor calls (`floor` on an `L`-Conn, `galois_l` on an
  `R`-Conn, etc.) become compile errors instead of runtime test
  failures. 4 trybuild compile-fail fixtures pin the discipline.
- Adjoint triples ship as unit-struct markers via the `triple! { pub
  NAME : A => B { ceil, inner, floor } }` declaration-form macro; their
  L-view and R-view `Conn`s are accessed via `NAME::L` / `NAME::R` (or
  via default `.ceil()` / `.inner()` / `.floor()` methods on `ViewL` /
  `ViewR` directly). Two-sided ops (`round`, `truncate`, `interval`,
  `midpoint`, `median` + lifters) bind on the `Triple<A, B>`
  super-trait. `compose!` (declaration form) and `compose_l!` /
  `compose_r!` (variadic same-kind) cover the composition surface.
- Migration scope: 28 macro-generated triples (`ext_int!`,
  `nz_int_ext!`, `fix_fix_*!`) + 10 cross-crate iso consts + 13
  standalone triples (float / time / addr) → markers; one-sided
  `new_l` / `new_r` consts stay as `Conn` values. All 1172 lib tests +
  16 integration suites + 36 doctests + 4 compile-fail fixtures green;
  clippy + fmt clean.

## Test plan

- [ ] `cargo test --workspace` passes (1172 lib + 1080+ integration
      proptests + 36 doctests + 4 compile-fail fixtures, all green
      locally).
- [ ] `cargo clippy --all-targets -- -D warnings` clean.
- [ ] `cargo fmt --all -- --check` clean.
- [ ] `compile_fail::kind_discipline` rejects all 4 wrong-kind fixtures
      (`floor` on `L`, `ceiling` on `R`, `galois_l` on `R`-kind,
      `galois_r` on `L`-kind).
- [ ] Spot-check `triple!` macro: a fresh `pub TRIPLE : A => B { ... }`
      declaration produces a unit-struct marker satisfying `Triple<A, B>`
      (covered by the migrated callsites — every `ext_int!` /
      `fix_fix_*!` invocation exercises the macro path).
- [ ] Spot-check `compose!`: composing two triple markers produces a
      fresh marker satisfying `Triple<A, C>` (verified by the
      `compose_*_step_matches_handcoded_at_samples` proptest battery
      in `src/conn.rs::tests`).
- [ ] Spot-check default-method dispatch: `MARKER.ceil(x)` /
      `MARKER.inner(x)` / `MARKER.floor(x)` resolve via `ViewL` /
      `ViewR` defaults when those traits are in scope (covered by
      restored doctests and per-Conn test blocks).
