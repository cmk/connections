# MR !17 — `conn::time` module (Sprint Time)

## Summary

- Add `conn::time` — five public `Conn` constants over the
  [`time`](https://crates.io/crates/time) crate's `Date` / `Time` /
  `Duration` / `PrimitiveDateTime` types: **`DATEJDAY`** (`Extended<Date>
  ↔ i32` Julian day), **`TIMENANO`** (`Extended<Time> ↔ i64` ns since
  midnight), **`TIMESECS`** (`Extended<Time> ↔ i64` whole seconds with
  sub-second rounding), **`DURNSECS`** (`Duration ↔ Extended<i64>` with
  sign-aware sub-second rounding and ±Inf overflow on the rung), and
  **`PDTMDATE`** (`PrimitiveDateTime ↔ Extended<Date>` with sub-day
  rounding).
- First module to take the `ABCDXWYZ` (4-letter halves) shape from the
  4+4 naming standard. CLAUDE.md lists it as "reserved — no current
  uses"; this module is the first user. Domain-typed sources/targets
  (`Date`, `Time`, `Duration`, `PrimitiveDateTime`) read better as
  letters than tier codes.
- Add `Ple` impls for `Date`, `Time`, `Duration`, `PrimitiveDateTime`,
  each delegating to the type's existing total `Ord`. No NaN patching
  needed.
- Extend `property::arb` with ten new strategies (`arb_date`,
  `arb_time`, `arb_duration`, `arb_primitive_dt`, `arb_extended_date`,
  `arb_extended_time`, `arb_extended_i64`, `arb_jd_in_range`,
  `arb_ns_in_range`, `arb_secs_in_range`), all biased toward
  MIN/MAX/MIDNIGHT/ZERO boundaries.
- Drive the full Galois law battery from `property::laws` for every
  Conn: `galois_l/r`, `closure_l/r`, `kernel_l/r`, `monotone_l/r`,
  `idempotent`. Plus `roundtrip_ceil/floor` (bounded), and
  `ulp_bound` for the three rounding conns. `floor_le_ceil` is
  intentionally omitted — same precedent as `conn::int::U008I016` and
  the other Extended-source conns: saturation makes `inner`
  non-injective, so the law fails at the arms.
- Update `README.md`: new row in the Connection families table, a
  Quick-tour `DURNSECS` block mirrored verbatim into the `conn::time`
  module-level doctest (so `cargo test --doc` keeps README and rustdoc
  in sync), Layout tree includes `conn/time.rs`, and the runtime-deps
  prose now cites both `fixed` and `time`.
- Add `Cargo.toml` dep on `time = "0.3"` (resolves to v0.3.45 under
  the crate's `rust-version = "1.85"` constraint; v0.3.47+ require
  1.88).

## Test plan

- [ ] `cargo test --workspace` — 1628 lib tests pass (1529 baseline +
      99 new: 20 preorder + 79 conn-law / spot).
- [ ] `cargo test --doc` — 18 doctests pass (12 baseline + 6 new: 1
      module-level + 5 per-constant).
- [ ] `cargo clippy --all-targets --no-deps -- -D warnings` — clean.
- [ ] `cargo doc --no-deps` — no new warnings (the four pre-existing
      warnings on `i16`/`i32`/`i64` module-vs-primitive shadowing and
      the `[arb]` link are out of scope).
- [ ] Pre-commit hook green on every commit.
- [ ] Manual smoke from the Quick-tour example: bracketing
      `Duration::seconds(5) + Duration::nanoseconds(1)` via `DURNSECS`
      gives `Extended::Finite(6)` for ceil and `Extended::Finite(5)`
      for floor, and `DURNSECS.inner(Extended::Finite(42)) ==
      Duration::seconds(42)`.
