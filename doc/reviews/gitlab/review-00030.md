# MR !30 — `conn::std` doc touch-ups (post-MR !27 review follow-up)

## Summary

- Adds doc-constraint pre-conditions to two macros in
  `src/conn/std.rs`, mirroring the pattern already used by
  `ext_int!`:
  - `int_int_narrow!` — `bits($A) > bits($B)` constraint plus an
    expanded "Why no FINE_MIN fixup?" derivation showing why
    `galois_l` holds at the low-end plateau without one.
  - `uint_int_sat!` — `bits($A) ≥ bits($B)` constraint with a
    note on the `<$B>::MAX as $A` and signed-to-unsigned cast
    safety under that constraint.
- Adds a one-line in-test rationale to all nine
  `tests/conn_std_<primitive>_galois.rs` files explaining that
  `galois_lower` is intentionally omitted from
  `single_sided_props!` (it fails by design for `Conn::new_left`
  at saturation plateaus). The full worked counter-example lives
  in `tests/conn_std_u8_galois.rs`; the other eight files point
  at it.

No code changes — only inline comments and rustdoc. Picks up
follow-up suggestions #4, #5, #7, #8 from the post-merge
`claude-review` round on MR !27. Suggestion #6 (test idempotency
form `inner∘ceil` vs `inner∘floor`) is style-only and equivalent
under `floor = ceil`; deferred.

## Test plan

- [ ] `cargo test --workspace` — unchanged from main; doc-only
      patch (1447 lib + 1481 integration + 26 doctests, all green).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `cargo doc --no-deps` — clean (the new rustdoc constraint
      blocks render correctly; modulo the pre-existing `arb`
      warning in `property/mod.rs`).
