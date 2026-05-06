# MR !61 — Plan 38: Interval<A> + filter_l/filter_r; prune midpoint

## Summary

- Adds an `Interval<A>` ADT (`Empty | Bounded { lo, hi }`) in a new
  `src/interval.rs` module, ported from `Data.Order.Interval` in the
  Haskell `connections` crate. `Interval::new` collapses
  incomparable / out-of-order endpoints to `Empty` (handles NaN
  cleanly); `imap` re-runs the preorder check on its result so
  non-monotonic maps collapse to `Empty`. Carries a containment
  preorder (`Empty ≤ everything`; `Bounded i₁ ≤ i₂ ⟺ i₂ ⊇ i₁`).
  Re-exported as `connections::Interval`.
- Replaces `pub fn interval(t, x) -> Option<Ordering>` (the misnamed
  half-comparison) with a real bracket function returning
  `Interval<A>`. Deletes `pub fn midpoint` (the `Add + Div`
  constraints excluded NonZero / dates / IpAddr / fixed-point
  shapes; only consumer was `round`). Rewrites `round` to compute
  its tiebreak directly from the bracket endpoints; bound delta
  drops `Add + Div`, keeps `Sub + From<u8> + PartialOrd`. Tiebreak
  direction (toward zero) preserved.
- Adds `Conn<_, _, L>::filter_l` and `Conn<_, _, R>::filter_r`
  inherent methods — principal-filter / principal-ideal membership
  predicates (`PartialOrd`-only, no arithmetic). Wires nine new
  property predicates into `law_battery!`: three bracket
  invariants on the `full` arm, three filter invariants each on
  `l_only` / `r_only`. New `src/prop/interval.rs` carries five
  standalone `Interval<A>` predicates with their own proptest block.

## Test plan

- [ ] `cargo test --lib` — 1163 tests pass (was 893 pre-sprint;
      delta ≈ 9 properties × ~30 battery instantiations + new
      `prop::interval` proptests).
- [ ] `cargo test --doc` — 57 doctests pass (was 51; delta = 5
      `Interval<A>` doctests + 1 reworked `interval` + 2
      `filter_l` / `filter_r`, minus 1 deleted `midpoint`).
- [ ] `cargo test --workspace --quiet` — battery green on every
      `law_battery!` instantiation under `src/{addr,char,float,
      fixed,time}/`.
- [ ] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
      --document-private-items` — clean (catches the
      `crate::interval` ambiguity introduced by the new module
      vs the existing fn re-export; resolved via fully-qualified
      `crate::conn::interval`).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `scripts/check-pii.sh` — exits 0.
- [ ] `scripts/check_readme_mirror.sh` — exits 0 (no new headline
      `Conn` const introduced; README mirror rule N/A).
