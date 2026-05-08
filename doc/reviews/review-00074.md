# MR !74 — Extended functor-lift macros (`lift_l!` / `lift_r!` / `lift_k!`)

## Summary

- Add three macros that lift a parent `Conn` (or `ConnK` marker)
  through the `Extended` functor: `lift_l!` / `lift_r!` produce a
  fresh `Conn<Extended<A>, Extended<B>, K>` value (const-init
  friendly); `lift_k!` is a declaration macro that emits a fresh
  unit-struct triple marker. Synthetic markers map identically;
  the `Finite` arm dispatches through the parent. Specialises the
  Haskell `mapped :: Functor f => Cast k a b -> Cast k (f a) (f b)`
  to the only saturation-bearing functor the crate ships,
  `Extended`.
- Unblocks compose chains where one Conn's endpoint is already
  `Extended<…>` and the adjacent Conn's corresponding side is bare
  (e.g. the linklab `F064 → Extended<HD> → Epoch via UTC` chain is
  the proximate use case; `connections::hifi` itself does not ship
  any composed const in this MR).
- Drives the lifted Conns through the full `prop::conn::*` law
  battery: `Conn::identity::<i64>` lifted through `lift_l!` runs the
  `l_only` subset (galois_l, closure_l, kernel_l, monotone_l,
  idempotent, filter_l_*); the iso `Q000I016` lifted through
  `lift_k!` runs the `full` subset (14 properties incl.
  `floor_le_ceil`, `order_reflecting`, and the bracket family).

## Test plan

- [x] `cargo test --features testing --lib extended::` — 38 tests,
  all green (six spot checks + `lifted_id_i64::*` + `lifted_q000i016::*`).
- [x] `cargo test --features "testing macros hifi byte" --lib` — 1492
  tests, all green; no regressions in the existing hifi/time/fixed
  Conn law batteries.
- [x] `cargo test --features "testing macros hifi byte" --doc` — 94
  doctests, all green; the four new lift macro doctests
  (`lift_l!`, `lift_r!`, `lift_k!`, plus the module-doc paragraph)
  use only unconditional fixtures (`Conn::identity`, `Q000I016`).
- [x] `cargo clippy --all-targets --features testing -- -D warnings` —
  clean.
- [x] `cargo fmt --all -- --check` — clean.
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features testing
  --document-private-items` — clean (no broken intra-doc links).
- [x] `scripts/check-pii.sh` on the staged diff — clean.
- [x] `scripts/check_readme_mirror.sh` — clean (no mirrored sections
  touched).
