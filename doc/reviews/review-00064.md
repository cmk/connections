# MR !64 — `hifi/epoch.rs` §1 TAI baseline + §2 UTC (Sprint 2 of hifitime integration)

## Summary

- Six new Conns under `connections::hifi::epoch` covering
  `hifitime::Epoch` projections in **TAI** (storage-native) and
  **UTC** (leap-second-aware) scales.
- Per-scale shape mirrors the per-Duration shape from Sprint 1:
  `E{xx}HDUR` (Epoch ↔ HDuration, `iso!`) +
  `E{xx}NANO` (Extended<Epoch> ↔ i128, `conn_l!` OFDTNANO shape) +
  `E{xx}F064` (F064 → Extended<Epoch>, `conn_l!` F064DURN shape via
  1ns ULP walks on the underlying TAI Duration).
- **Reference epochs**: ETAI* uses J1900 TAI (hifitime-native);
  EUTCNANO/EUTCF064 use UNIX EPOCH UTC (matches `OFDTNANO`'s
  semantic for callers bridging `time::OffsetDateTime` ↔ `Epoch`).
  EUTCHDUR uses J1900 UTC (UNIX-anchoring would push the iso's
  round-trip boundary outside HD's range).
- Single-side `Extended<…>` throughout, per the project rule.

## Test plan

- [ ] `cargo build --no-default-features` — feature still optional
- [ ] `cargo build --features hifi`
- [ ] `cargo test --features hifi,testing` — all suites green
      (53 hifi::epoch unit tests + 6 epoch doctests)
- [ ] `cargo clippy --features hifi,testing --all-targets -- -D warnings`
- [ ] `RUSTDOCFLAGS=-Dwarnings cargo doc --features hifi,testing,macros
      --no-deps --document-private-items`
- [ ] `cargo fmt --all -- --check`
- [ ] iso laws hold for ETAIHDUR / EUTCHDUR (`iso_only` law_battery)
- [ ] ConnL laws hold for ETAINANO / EUTCNANO / ETAIF064 / EUTCF064
- [ ] EUTCNANO round-trips Y2038 unix nanoseconds exactly
