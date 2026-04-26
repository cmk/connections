# MR !9 — `compose!` macro for compile-time Conn composition

## Summary

- **Add `compose!`** — variadic `macro_rules!` in `src/conn.rs` that
  expands a chain of two or more `Conn` consts into a fresh
  `Conn<Src, Dst>` via nested calls. Non-capturing closures coerce to
  `fn(_) -> _` pointers at the `Conn::new` call site, so the result
  preserves `Conn`'s `Copy` + `const`-constructible shape with no
  changes to the struct itself.
- **Tests** — replace the hand-nested
  `composition_pico_to_uni_matches_ladder_climb` with macro-driven
  equivalents (`compose_two_step_*`, `compose_four_step_*`) and add
  Galois-law preservation checks against a macro-composed
  `Conn<Pico, Uni>` (`compose_inner_then_ceil_is_id`,
  `compose_floor_le_ceil`, `compose_galois_upper`,
  `compose_galois_lower`, `compose_idempotent`). +9 proptest instances,
  test count 505 → 514.
- **`doc/design.md`** — replace the broken pseudo-implementation of
  `Conn::then` (lines 91–112, which couldn't compile against the
  `fn`-pointer struct) with a "Why not a runtime `Conn::then`" section
  documenting the storage-shape constraint and the two future shape
  options (generic-default type params; boxed trait objects). Update
  the combinator table at line 120: `compose!` is the implemented
  primitive, `Conn::then` stays deferred.

## Test plan

- `cargo build` — clean.
- `cargo test --workspace` — 514 passed, up from 505.
- `cargo clippy --all-targets -- -D warnings` — clean.
- `cargo fmt --all -- --check` — matches main's pre-existing drift
  (27 lines across files this MR doesn't touch); no new drift introduced.
- `const F12F00_BIS: Conn<Pico, Uni> = compose!(F12F09, F09F06, F06F03, F03F00);`
  compiles in const context, exercising non-capturing-closure → fn-ptr
  coercion at const-eval.
- `cargo doc --no-deps` — zero warnings on the new macro and design
  doc section.

Deferred (tracked in plan Review):
- Runtime `Conn::then` — re-open when a concrete consumer appears;
  the macro covers all known compile-time use cases.
- `product` / `coproduct` — same shape constraint as `then`.
