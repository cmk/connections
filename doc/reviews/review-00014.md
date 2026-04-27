# MR !14 — Standardize Conn-name format + add 128-bit Conns

## Summary

- Renames every public `Conn` constant to a uniform 8-character
  `XnnnYmmm` shape (4 chars per side, smaller-resolution tier on
  the right). Family letters: `FD` (decimal fixed, 2L+2D, e.g.
  `FD12FD06`), `F` (float width, e.g. `F064`), `I` / `U` (signed /
  unsigned int width AND signed / unsigned binary-fixed frac level,
  1L+3D, e.g. `I008I016` / `U008U016`), `S` (sample rate kHz,
  e.g. `S088S044`). Type wrappers renamed for full conformity:
  `Pico`→`FD12`, `Uni`→`FD00`, `S44`→`S044`, etc., plus per-binary-
  module type aliases (`pub type I008 = FixedI8<U8>` etc.). Cross-
  module collisions like `i08::I008I004` vs `i64::I008I004` resolve
  via the standard Rust qualified-import idiom.
- Adds 14 missing 128-bit integer Conns: 5 in `conn::int`
  (`I064I128`, `U008I128`..`U064I128`) and 9 in `conn::uint`
  (`U008U128`..`U064U128`, `I008U128`..`I128U128`). The existing
  `ext_int!` / `uint_uint!` / `int_uint!` macros support i128
  endpoints unchanged; only new invocations and `arb_ext_i64` /
  `arb_ext_u64` strategies were added.
- Adds `conn::fixed::i128` — 15 i128-backed binary fixed-point
  Conns over the frac-level set `{U0, U16, U32, U64, U96, U128}`.
  Stable Rust has no native `i256` to widen through, so the i64-
  style `(bits as i128) * RATIO` pattern is replaced by
  `i128::checked_mul + saturate`; bit-identical outputs to a
  hypothetical i256 implementation. The `I128I000` endpoint is
  intrinsically degenerate (RATIO = 2^128 ∉ i128) — detected via
  `i128::checked_shl(128) == None` and handled in dedicated
  branches; pinned by the `degenerate_max_shift` regression test.

## Test plan

- [ ] `cargo test --workspace` — **1491 passed**, 0 failed, 0 ignored
      (1260 pre-rename + 92 from 128-bit ints + 139 from i128 binary).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean on every
      commit.
- [ ] `cargo doc --no-deps` — clean.
- [ ] Pre-commit hook green on every commit (cargo test, clippy,
      check-pii).
- [ ] Manual smoke: the canonical downstream usage example from the
      lib.rs docstring compiles and runs:
      ```rust
      use connections::conn::fixed::decimal::{FD12, FD06, FD12FD06};
      use connections::conn::sample::{S044, S088, S088S044};

      let p = FD12(1_000_000_000_000);
      let m = FD12FD06.floor(p);                   // → FD06(1_000_000)
      let r = S044::from_sample(7);
      let _ = S088S044.inner(r);                   // → S088 with 14
      ```
- [ ] Qualified-import disambiguation works: `i08::I008I004` and
      `i64::I008I004` co-exist when imported under aliases.
