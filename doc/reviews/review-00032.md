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

## Local review (2026-04-27)

### Verdict
PASS. Plan executed cleanly: `maximize`/`minimize` dropped end-to-end
(re-exports, laws, README, design.md), four-op `ExtendedFloat<f32|f64>`
arithmetic surface is minimal and the in-file doc table agrees with
the match arms, every `cast.rs` doctest now exercises `F064F032` + π,
and the module-level `## Behavior on edge inputs` section deduplicates
per-fn NaN prose. `cargo test --lib` 1195/1195 green;
`cargo test --doc` 36/36 green; `cargo clippy -D warnings` clean;
`cargo doc` produces only the two pre-existing `property::arb`
warnings the MR description acknowledges. Six commits, linear, no
merges, conventional subjects.

### Must-fix (block push)
- None.

### Should-fix (recommend before push)
- `src/conn/cast.rs` `truncate2` / `round2` doctests — assertions
  were one-sided upper bounds; a regression returning `Extend(0.0)`
  or `Bot` would still pass. **Addressed in fix commit:** `truncate2`
  now `assert_eq!`s against `F064F032.floor(Extend(2.0 * π32 as f64))`
  exactly; `round2` asserts the result lands on either bracket
  endpoint.
- `src/conn/float.rs` Bot/Top doc-vs-plan drift — the plan's Div row
  promised "endpoint by sign" semantics; the impl simplifies every
  non-`(Extend, Extend)` case to `Extend(NaN)`. **Addressed:** the
  in-file caveat now explicitly defends the simplification (no chain
  combinator reaches Bot/Top operands; deterministic tests pin the
  semantics for direct callers); the plan's Review section
  acknowledges the simplification.

### Nits
- `src/conn/cast.rs:46-49` — module doc said the arithmetic helpers
  carry `Add`/`Sub`/`Div`/`From<u8>` bounds, which over-claimed for
  `interval` (only `Sub`). **Addressed:** rephrased per-fn so each
  helper's bound list is accurate.
- `src/conn/float.rs:117-118` — "no in-tree caller exercises a Bot
  or Top operand" was inaccurate after `add_endpoints_absorb` landed.
  **Addressed:** rephrased to "no chain-combinator caller reaches
  the Bot/Top arms; deterministic tests pin them for direct callers".

### Verification check
The plan's verification table is satisfied. Three required new
properties (`add_extends_passes_through_f64`, `sub_zero_is_id_f64`,
`from_u8_round_trips_f32_f64`) are present; three bonus deterministic
tests (`div_by_two_halves_f64`, `add_endpoints_absorb`,
`sub_extends_passes_through_f64`) close the Bot/Top coverage gap. The
deleted laws (`cast_maximize_eq_ceiling`, `cast_minimize_eq_floor`)
and their proptest invocations are gone from `src/property/laws.rs`
and `src/conn/cast.rs::tests`. Doctests exercise the new arithmetic
impls end-to-end. Sole remaining gap: no proptest drives `Add`/`Sub`/
`Div` on Bot/Top — deterministic coverage only. Acceptable for the
"minimal surface" scope of this sprint.
