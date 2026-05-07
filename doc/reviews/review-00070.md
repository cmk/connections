# MR !70 — Plan 47: feature-flagged `byte` module

## Summary

- Add `byte` cargo feature gating a new `connections::byte::*` module
  that ships **14 sortable byte-encoding Conns**: `{u,i}{8..128} ↔
  [u8; N]` (big-endian for unsigned; sign-flipped BE for signed),
  `f{16,32,64} ↔ [u8; N]` (IEEE 754 totalOrder pre-encoding via the
  same algebra `signed32` already uses for ULP walks), and a one-sided
  `BOOLOBYT`. Right-side constant code is `OBYT` ("Ordered BYTes").
- All 13 isos are degenerate Galois (`floor = ceil = forward`) with
  bit-exact round-trip; lex byte order matches host numeric order
  (`total_cmp` for floats). No new third-party dependencies — the
  implementation only touches std's `to_be_bytes` / `from_be_bytes`.
  Default builds (no `byte` feature) are unaffected.
- Verification: 73 proptests + 7 doctests + **43 Kani SMT proofs**
  (1- and 2-byte hosts exhaustive; 4-byte under 64-bit symex on the
  two-input order-preservation predicate). 8/16-byte hosts are
  proptest-only; CBMC stalls on 128/256-bit two-input symex.

## Test plan

- `cargo test --workspace` — default-feature build, all 1166 existing
  tests pass; byte module is invisible.
- `cargo test --workspace --features byte` — adds 69 byte proptests +
  7 byte doctests, all green.
- `cargo clippy --all-targets --features byte -- -D warnings` — clean.
- `cargo kani --features byte --harness 'byte_'` — 43/43 SMT proofs
  green.
- `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features byte`
  — docs render without intra-link breakage.
