# MR !37 — CI cost reduction + walk-perf fix + extremal coverage

## Summary

- Restructures CI: drops the 2.6 GB `target/` from the GitLab cache,
  rekeys to `Cargo.lock`, sets `CARGO_HOME=$CI_PROJECT_DIR/.cargo`,
  scopes `fmt` to no cache and `doc` to MR + `main` only. One
  pipeline now moves ~50 MB of cache traffic vs ~20 GB before.
- Switches the test job to `cargo nextest run --workspace --profile
  ci` (parallelizes individual `#[test]` fns; doctests run
  separately via `cargo test --doc`). New `.config/nextest.toml`
  with a warn-only 180s slow-timeout.
- Fixes a perf bug in `F032DURN.ceil`/`F064DURN.ceil` (mirrored on
  `floor`) where a strict `<` boundary check on `min_secs` failed to
  fast-path the round-trip value `Duration::MIN.as_seconds_f??()`,
  triggering a ~70-second nanosecond-by-nanosecond walk through the
  f-precision plateau. Per-call wall-time on the slow input
  72.7s → 84ns. Suite total 248s → 7.7s.
- Boosts extremal sampling in `src/prop/arb.rs`: float strategies go
  from 4:1/6:1 uniform-to-boundary to 1:2; Extended-wrapped
  strategies go from 1:1:8 to 1:1:3 (floats) / 1:1:2 (time types) /
  1:1:1 (finite-variant enums). New extrema added: `EPSILON`,
  smallest positive subnormal, integer-precision boundary `2^N ± 1`.
  Per-named-extremum sampling rate goes from 0.4–1.8% to >5%.

Plan: `doc/plans/plan-2026-04-27-11.md`.

## Test plan

- [ ] `cargo build` (stable, default features) — clean.
- [ ] `cargo nextest run --workspace --profile ci` — all 2728 green,
      no slow-timeout warnings >180s, total ≤10s on M1.
- [ ] `cargo test --workspace --doc` — all green.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `cargo doc --no-deps --features testing --document-private-items`
      with `RUSTDOCFLAGS=-D warnings` — clean.
- [ ] CI: confirm post-merge pipeline cache transfer ≤100 MB per job
      (vs ~2.6 GB prior) and total wall-time roughly halved.
