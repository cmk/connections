# MR !27 — Final pre-publish push: 45 missing Conns + `conn::std` restructure

## Summary

- Closes the API-symmetry gaps identified in the 0.1.0 publish
  audit (`note-2026-04-27-01.md`) by shipping **45 new `pub
  const` Conns** across four families:
  - **§1 I→I narrowing** (10 Conns, `int_int_narrow!`,
    left-Galois) — `I016I008` … `I128I064`.
  - **§2 U→U narrowing** (10, `uint_uint_narrow!`, left-Galois) —
    `U016U008` … `U128U064`.
  - **§3 U→I non-widening** (15, `uint_int_sat!`,
    **right-Galois** via new `Conn::new_right`) — `U008I008` …
    `U128I128`. The right-Galois shape is forced by the
    target-side saturation plateau (`i_M`'s negative half
    collapses to `0_u_N` via `inner`); single-sided left-Galois
    breaks at every `(0_u_M, neg_i_N)` corner.
  - **§4 I→U narrowing** (10, `int_uint_narrow!`, left-Galois) —
    `I016U008` … `I128U064`.

  Each new single-sided narrowing macro carries the same
  **FINE_MAX boundary fixup** in `inner` that landed in MR !20
  for `conn::fixed::u<width>` — required for `galois_l` to hold
  at the source-side saturation plateau.
- Restructures `conn::int` and `conn::uint` into per-primitive
  submodules `conn::std::{i8,i16,i32,i64,i128,u8,u16,u32,u64,u128}`
  per right-side wins. The 24 existing widening Conns are
  redistributed (e.g. `conn::int::I008I016 →
  conn::std::i16::I008I016`); the three existing macros
  (`uint_uint!`, `int_uint!`, `ext_int!`) move to
  `src/conn/std.rs` as `pub(crate) use`-exported items shared
  across submodules. Indirectly closes audit W1's recommendation
  by going one level deeper (`conn::std::<dest>` rather than
  `conn::primitive::{int,uint}`).
- Adds `Conn::new_right(inner, floor)` constructor (one-line
  additive API mirroring `new_left`). Documents the right-Galois
  single-sided shape and pins `ceil = floor`.
- Migrates std-int proptest batteries to integration tests under
  `tests/conn_std_<primitive>_galois.rs` (10 files), mirroring
  the pattern established in MR !20. Spot tests stay inline.
  Indirectly closes audit W2 for the std-int family.
- Updates `src/lib.rs` convention examples to `conn::std::*`
  paths and adds four representative new-narrowing bullets;
  `doc/design.md` file-tree expanded to enumerate every
  `conn/std/*.rs`. README.md docfence example switched from
  `conn::int::U008I016` to `conn::std::i16::U008I016`.

Net post-sprint coverage:
- **Fixed-width int/word Conns: 120** (was 75 — adds 45).
- **All 28 fixed-width Haskell `Connection.{Word,Int}` Casts
  ported**, plus 92 new Rust-only Conns covering i128/u128
  extensions and the four narrowing/non-widening directions
  Haskell doesn't define directly.

## Test plan

- [ ] `cargo test --workspace` — **~3070 tests** pass (1584 lib +
      ~1490 integration across 15 binaries + 26 doctests), 0
      failed.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `cargo doc --no-deps` — clean (modulo the pre-existing
      unrelated `arb` warning in `property/mod.rs`).
