# MR !32 — `conn::cast` cleanup: drop `maximize`/`minimize`, π-driven doctests, edge-case prose

## Summary

- Removes `conn::cast::maximize` / `minimize` (curried forms over
  `Conn<(A, B), C>`) — they were a faithful Haskell port that only
  earned rent in `median`, which now calls `c.ceil((p, q))` /
  `c.floor((p, q))` directly. Drops the two functions, their
  re-exports, two property predicates, two spot tests, and two
  proptest blocks.
- Replaces every `Conn::identity::<i32>()` doctest in `conn::cast`
  with one driven over `F064F032` and `Extend(std::f64::consts::PI)`,
  showing the real f32-bracket structure (ceiling and floor return
  distinct endpoints; `interval` returns `Some(Greater)` because π
  is closer to its f32 ceiling; `round` picks the ceiling for the
  same reason).
- Adds `Add` / `Sub` / `Div` / `From<u8>` impls for
  `ExtendedFloat<f32 | f64>` — minimal numeric surface needed to
  thread `ExtendedFloat<T>` through the chain combinators in
  `conn::cast`. Bot/Top edge cases documented; finite Extend
  operands flow through to the inner type's arithmetic. No `Mul`,
  no `Neg`, no `half`/`bf16` impls — added only when a caller
  needs them.
- Centralizes the chain combinators' length-2-conn and NaN-input
  behavior in a new `## Behavior on edge inputs` module-level
  section in `conn::cast`. Trims `round`'s NaN paragraph (the
  trailing "Callers that need different NaN handling should branch
  upstream" sentence in particular) to a single back-reference.

## Test plan

- [x] `cargo build` — clean.
- [x] `cargo test --workspace` — 1189 lib tests + 36 doctests
      pass. Six new `ExtendedFloat<T>` numeric tests (`add_*`,
      `sub_*`, `div_*`, `from_u8_round_trips_f32_f64`) added; two
      `cast_maximize_eq_ceiling` / `cast_minimize_eq_floor`
      predicates plus their proptest invocations removed alongside
      `maximize` / `minimize`.
- [x] `cargo clippy --all-targets -- -D warnings` — clean.
- [x] `cargo doc --no-deps` — clean (the two pre-existing
      `property::arb` warnings predate this branch and will get
      fixed in a follow-up; `git show 0642acf:src/property.rs`
      confirms they were already there).
- [x] Doctests against `F064F032` exercise the new
      `Add`/`Sub`/`Div`/`From<u8>` impls end-to-end (`midpoint`,
      `round`, `truncate`, plus `1`/`2` lifters all invoke them).
