# Review 00042 — Plan 24: `addr/` submodule + `LATTBOOL` helper

## Summary

- Adds a new top-level `addr/` submodule with seven Galois connections
  for `std::net` address types: `U032IPV4` and `U128IPV6` (total
  bijections), `IPV6IPV4` (v4-mapped bridge, full triple), and the
  four sum projections `IPVXIPV4` / `IPVXIPV6` / `SOVXSOV4` /
  `SOVXSOV6` (one-sided `new_left` / `new_right` Conns extracting
  variant-specific values from `IpAddr` and `SocketAddr`).
- Adds a generic `LATTBOOL<A>() -> Conn<A, bool>` helper to
  `lattice.rs` — the canonical `bndbin`-shape Conn for any bounded
  lattice — plus `Join` + `Meet` impls on `core::cmp::Ordering` as
  the smallest non-trivial in-crate test surface.
- Cuts the original Plan 24 scope significantly: the `char`,
  `Ordering`, and `bool` Conns from the spec are deferred, and the
  one-sided structure of the four sum-projection Conns replaces the
  originally-specced full triples (which weren't Galois-lawful
  because `inner` is non-order-reflecting at the source extremes).
  The plan's Review section captures the math, the deviations, and
  the lessons.

## Test plan

- [x] `cargo build` clean.
- [x] `cargo test --workspace` clean (1291 lib tests, +61 over Plan 23 baseline).
- [x] `cargo test --doc` clean — every shipped Conn has a runnable doctest.
- [x] `cargo clippy --all-targets -- -D warnings` clean.
- [x] `cargo fmt --all -- --check` clean.
- [x] `scripts/check-pii.sh` and `scripts/check_readme_mirror.sh` exit 0.
- [x] Every full-triple Conn (`U032IPV4`, `U128IPV6`, `IPV6IPV4`)
      has `conn_floor_le_ceil` in its battery (over its source domain).
- [x] Every one-sided Conn (`IPVXIPV4`, `IPVXIPV6`, `SOVXSOV4`,
      `SOVXSOV6`) asserts the appropriate Galois law (`L` for
      `new_left`, `R` for `new_right`) plus `floor_le_ceil` (which
      holds trivially because `floor = ceil` as a fn pointer).
- [x] `LATTBOOL::<Ordering>()` exercises both Galois laws +
      `floor_le_ceil` + `idempotent` over the 3-element chain.
