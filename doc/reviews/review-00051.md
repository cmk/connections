# MR !51 — Plan 33: order_reflecting predicate + audit cleanup

## Summary

- Adds `prop::conn::order_reflecting` and wires it into `law_battery!`'s
  `full` arm so every triple marker exercises the load-bearing property
  (`inner(b1) ≤ inner(b2) ⟹ b1 ≤ b2`) of which Plan 32's `floor_le_ceil`
  was the corollary. All seven existing triples pass without changes.
- Expands the README *Why one-sided?* section with explicit step-by-step
  proof chains for both directions of the equivalence, a sharpened
  counterexample that derives `ceil(a)`/`floor(a)` from L/R-Galois, and
  back-references from Examples 3 and 6.
- Closes the easily-completable items from the post-Plan-32 audit:
  `f032/f064_floor_nan` symmetric tests, `F064F032` definition-site
  doctest, `sovxsov6_idempotent_r`, fixed `SOVXSOV6.inner(NegInf)` doc
  reasoning, five stale `tests/conn_fixed_*` filename references, three
  duplicated-`.ceil()` test artifacts surfaced by Plan 32's NonZero
  demotion.

## Test plan

- [ ] `cargo test --workspace` — all green; new `order_reflecting`
      tests visible per triple (`U032CHAR`, `F064F032`, `DURNSECS`,
      `STDRU064`, `IPV6IPV4`, plus `U032IPV4`/`U128IPV6` isos via
      `law_battery!`; `F032F016`/`F064F016` via inline proptest).
- [ ] `cargo test --doc` — F064F032 doctest passes, README proof
      chains rendered as text fences (no rustdoc compile attempts).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean (the new
      `order_reflecting` predicate uses the `monotone_l` if/else
      pattern to satisfy `neg_cmp_op_on_partial_ord`).
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] Local pre-push hook (`RUSTDOCFLAGS="-D warnings" cargo doc
      --no-deps --features testing --document-private-items`) — clean.
