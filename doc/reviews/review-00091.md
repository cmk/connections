# MR !91 — Float → Extended<intN> connections

## Summary

- Ports the Haskell `Data.Connection.Float` Float→Extended-int family to
  Rust: 24 new `Conn` consts spanning f32/f64/f16 sources × {u8,u16,u32,
  u64,i8,i16,i32,i64} targets. Full Galois triples where the target
  fits losslessly in the source mantissa; L-only Conns where it
  doesn't.
- Adds the supporting infrastructure: `float_ext_int!` /
  `float_ext_int_l!` macros (in `src/float.rs`), `shift64` ULP machinery
  matching the existing `shift32`, a `RoundDownFromI128` trait + per-
  float `round_down_to_*` helpers (so `inner` rounds toward `-∞` and
  the L-Galois kernel law holds even when target precision exceeds the
  source mantissa), and the missing
  `arb_extended_{u8,u16,i8,i16,i32}` proptest generators.
- Extends `compose_k!` to accept doc comments and visibility, lets
  composed Conns ship as documented `pub` consts. Used by
  `F064U008`/`F064U016`/`F064I008`/`F064I016` (composed via `F064F032
  ∘ F032<X>`, since narrowing through f32 is exact for ≤16-bit
  targets). f16 source Conns ship direct rather than composed — see
  the deferred-decisions section below.

The Float→FixedI/U Q-format target family (~186 Conns) was deferred
to a follow-up sprint per the plan's "Phase split fallback" (saturate-
and-scale arithmetic across 5 host-int widths × 6–7 frac rungs ×
3 source floats × 2 signs is materially more work than this MR's
24 Conns and warrants its own focused review). The Phase 1 surface
shipped here unblocks the follow-up cleanly: the `RoundDownFromI128`
trait, `shift64`, and the macro layout transfer directly.

## Test plan

- [x] `cargo test --features testing` — all 1339 tests pass on stable.
- [x] `cargo +nightly test --features f16,testing` — all 1462 tests
      pass on nightly (additional 123 f16 tests covering F016U/I*).
- [x] `cargo clippy --all-targets --features testing -- -D warnings` —
      clean.
- [x] `cargo +nightly clippy --all-targets --features f16,testing
      -- -D warnings` — clean.
- [x] `cargo fmt --all --check` — clean.
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features
      testing,macros --document-private-items` — clean (no broken
      intra-doc links).
- [x] Per-Conn law battery: each of the 24 new Conns has a
      `crate::law_battery!` invocation — `subset: full` for triples,
      `subset: l_only` for L-only. Adjoint laws verified across
      `Bot`/`Top`/`Extend(NaN)`/`Extend(±∞)`/`Extend(boundary)`/
      `Finite(MIN)`/`Finite(MAX)`/generic via the existing
      `extended_float_*` and `arb_extended_*` strategies (256
      cases per law).
- [x] Spot tests covering: NaN ceil → PosInf, NaN floor → NegInf,
      ±∞ saturation through `v > hi`/`v < lo` branches,
      `Bot`/`Top` pass-through, exact-integer round-trip,
      sub-integer ceil/floor bracket, composed Conn agrees with
      direct path on a representative input.
