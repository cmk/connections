# MR !18 — Drop `Ple`; adopt `Eq + PartialOrd` as the lawful framework

## Summary

- Replaces the crate-local `Ple` trait (and its 14 hand-coded impls)
  with the standard-library bound `Eq + PartialOrd`. The "broken-
  for-floats" problem turns out to be in `PartialEq` (which Rust
  documents as a *partial* equivalence relation), not in
  `PartialOrd` — and Rust's `Eq: PartialEq` marker trait already
  certifies the reflexivity fix. `ExtendedFloat<T>`'s patched
  `PartialEq` (where `Finite(NaN) == Finite(NaN)` is true) now
  carries an `impl Eq`, so float Conns flow through the law
  machinery via the standard bound. Net new traits in the public
  API: zero.
- Migrates the only raw-float Conn from `pub fn f64_f32() ->
  Conn<f64, f32>` to `pub const F064F032: Conn<ExtendedFloat<f64>,
  ExtendedFloat<f32>>`. Two CLAUDE.md conventions enforced at once:
  Conn becomes a `pub const` (matching every other Conn) and the
  name conforms to the X123Y456 shape. Raw `f32`/`f64` cannot impl
  `Eq` (NaN ≠ NaN under standard `PartialEq`), so the type system
  now rejects raw floats as Conn endpoints — the lawful usage is
  encoded.
- Updates `doc/design.md` ("Why not a custom Preorder trait?" →
  "Why `Eq + PartialOrd` suffices"); amends the cast-accessors plan
  (`plan-2026-04-26-08.md`) to drop the deferred `Pcompare: Ple`
  trait — Sprint B's `pcompare` is now just
  `PartialOrd::partial_cmp`. `f128` / `f16` cross-tier conns
  (`F128F064`, `F032F016`, etc.) remain deferred behind Rust 1.85's
  toolchain pin.

## Test plan

- [ ] `cargo test --workspace` — **1526 unit tests**, 11 doctests pass; 0 failed; 0 ignored.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo doc --no-deps` — clean.
- [ ] Pre-commit hook green on every commit (cargo test, clippy, check-pii).
- [ ] Manual smoke: the canonical downstream usage example compiles and runs:
      ```rust
      use connections::conn::float::{F064F032, ExtendedFloat};
      let x = ExtendedFloat::Finite(1.5_f64);
      let y = F064F032.ceil(x);     // → ExtendedFloat::Finite(1.5_f32)
      let _back = F064F032.inner(y);
      ```
- [ ] Compile-time negative test: `laws::conn_galois_l(&some_conn,
      1.0_f64, 2.0_f32)` fails to compile with a diagnostic naming
      the missing `Eq` bound — the type system now refuses raw float
      Conn endpoints.
- [ ] No `Ple` references remain in `src/`:
      `git grep -nE '\bPle\b|\.ple\(' src/` returns empty.
