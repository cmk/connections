# MR !44 — Plan 27: time/ Conns to one-sided so floor_le_ceil holds

## Summary

- Convert six `time/` Conns (`TIMENANO`, `TIMESECS`, `DATEJDAY`,
  `OFDTNANO`, `OFDTSECS`, `PDTMDATE`) from full-triple `Conn::new` to
  one-sided `Conn::new_left(ceil, inner)`. Each had a non-order-
  reflecting `inner` at synthetic extremes that broke
  `conn_floor_le_ceil`; `new_left` wires `floor = ceil` structurally
  so the law holds by construction.
- Behavioral deltas on `floor()` for the three sub-unit projections
  (`TIMESECS`, `OFDTSECS`, `PDTMDATE`): previously truncated, now
  rounds up to match `ceil` (the round-up semantics is preserved as
  the canonical answer). Synthetic-end values (`floor(NegInf)` /
  `floor(PosInf)`) similarly collapse onto `ceil`'s saturation values.
- Property batteries lose `_r` family tests on the converted Conns
  (`galois_r`, `closure_r`, `kernel_r`, `monotone_r`, `roundtrip_floor`)
  since they don't hold under `new_left`; `_l` family + `floor_le_ceil`
  + `idempotent` + `roundtrip_ceil` remain.

## Test plan

- [ ] `cargo test --workspace` passes (1265 lib + 45 integration + 55
  doctests, all green locally).
- [ ] `cargo clippy --all-targets -- -D warnings` clean.
- [ ] `cargo fmt --all -- --check` clean.
- [ ] `floor_le_ceil` proptests pass for all 6 converted Conns.
- [ ] Spot-check `floor` and `ceil` agree at synthetic extremes for
  each Conn (covered by updated `saturation_extremes` tests).
