# MR !63 — `hifi` cargo feature + `hifi/duration.rs` (Sprint 1 of hifitime integration)

## Summary

- New optional `hifi` cargo feature pulls
  [`hifitime`](https://docs.rs/hifitime) v4.3 with
  `default-features = false` (no-std-friendly; downstream re-enables
  what it needs).
- `connections::hifi::duration` ships four Conns over
  `hifitime::Duration`: `HDURNANO` (i128 total nanoseconds, OFDTNANO
  shape), `HDURSECS` (i64 whole seconds, OFDTSECS shape),
  `F064HDUR` / `F032HDUR` (IEEE float seconds via 1 ns ULP walks,
  F064DURN / F032DURN shape).
- All four use **single-side `Extended<…>`** — no two-sided wrapping.
  Sets the precedent for the rest of the hifitime sprints (see
  `doc/plans/plan-2026-05-06-04.md` for the master integration plan).

## Test plan

- [ ] `cargo build --no-default-features` — feature genuinely optional
- [ ] `cargo build --features hifi`
- [ ] `cargo test --features hifi,testing` — all suites green
      (1212 lib + 4 hifi doctests)
- [ ] `cargo clippy --features hifi,testing --all-targets -- -D warnings`
- [ ] `RUSTDOCFLAGS=-Dwarnings cargo doc --features hifi,testing,macros
      --no-deps --document-private-items`
- [ ] Galois L laws hold over `arb_extended_hifi_duration` × `any::<i128>()`
      (and the i64 / float-bridge analogs) across all six Conns
- [ ] `HDURNANO` round-trips `arb_hifi_total_nanos_in_range` exactly
