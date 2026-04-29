# Review 00041 — Plan 23: std-time Duration family inside `time/`

## Summary

- Adds four Galois connections bridging `std::time::Duration` to numeric
  rungs — `STDRU064` (whole seconds, `Extended<u64>`), `STDRU128` (exact
  nanoseconds, `Extended<u128>`), and the float bridges `F064STDR` /
  `F032STDR` — all hosted in `src/time/duration.rs`.
- Reframes `time/` from "the `time` crate's Conns" to "time-domain Conns
  spanning the `time` crate and `std::time`": new `STDR` prefix in the
  module's naming table, four new constants table rows, second
  README-mirrored doctest using `STDRU064` as the unsigned counterpoint
  to `DURNSECS`, and a CLAUDE.md note codifying the merged-module
  pattern that Plan 25 (`int` ⊕ `fixed`) will follow.
- Three lawfulness deviations from the plan, each captured in the plan's
  Review section: source-side `Extended` wrap on STDRU064/128 to avoid
  the Galois-forced `ceil(ZERO) = NegInf` arm; corrected F???STDR
  negative-input arms (`ceil → Finite(ZERO)`, `floor → NegInf`); and a
  rung-bounded proptest strategy for STDRU128's law battery (mirrors
  `OFDTNANO`'s `arb_unix_nanos_in_range`).

## Test plan

- [x] `cargo build` clean.
- [x] `cargo test --workspace` clean (1230 tests; the new STDR* battery
      adds 41 of them).
- [x] `cargo test --doc` clean — the new doctests on `STDRU064`,
      `STDRU128`, `F064STDR`, `F032STDR` and the second README-block
      mirror (`STDRU064` quick tour) all run.
- [x] `cargo clippy --all-targets -- -D warnings` clean.
- [x] `cargo fmt --all -- --check` clean.
- [x] `scripts/check-pii.sh` and `scripts/check_readme_mirror.sh`
      both exit 0.
- [x] STDRU064 / STDRU128 spot-check round-trip (1.5 s ↔ Finite(2) /
      Finite(1) and Finite(1_500_000_000)).
- [x] F064STDR / F032STDR negative-input asymmetry verified by both
      spot tests and a dedicated proptest
      (`f64_stdr_negative_input_ceil_to_zero`).
