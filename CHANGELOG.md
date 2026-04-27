# Changelog

All notable changes to this crate will be documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] — 2026-04-27

Initial release. A Rust port of the Haskell
[`connections`](https://github.com/cmk/connections) library, encoding
Galois connections as first-class `Conn<A, B>` values and exposing a
hierarchy of lattice-based numerical conversions on top.

### Added

- **`Conn<A, B>`** — adjoint triple `ceil ⊣ inner ⊣ floor` stored as
  three bare `fn` pointers. `Copy`, `const`-constructible, heap-free.
  `Conn::new` (full triple), `Conn::new_left` (one-sided),
  `Conn::identity()`.
- **`compose!` macro** — variadic compile-time composition of two or
  more parent Conns into a fresh `Conn<Src, Dst>`. Source/dest types
  come from the binding's annotation; intermediates are inferred.
- **`Extended<T>`** and **`ExtendedFloat<T>`** — three-element extensions
  (`Bot`/`Extend(_)`/`Top`) recovering the lattice top/bottom that std
  primitives lack. `ExtendedFloat<T>` patches NaN reflexivity so the
  Galois-law machinery can reason about IEEE floats under N5.
- **Lattice trait hierarchy** in `connections::lattice` (Eq + PartialOrd
  base, Heyting / Bi-Heyting operators).
- **`property::laws`** — pure `bool`-returning Galois-law predicates
  (`conn_galois_l/r`, `conn_closure_l/r`, `conn_kernel_l/r`,
  `conn_monotone_l/r`, `conn_idempotent`, `conn_floor_le_ceil`,
  `conn_roundtrip_ceil/floor`, `conn_ulp_bound`). Always public; no
  `proptest` dependency.
- **`property::arb`** (gated on the `testing` feature) — proptest
  strategies (`arb_f32`/`arb_f64`/`arb_f64_bounded`/`arb_f16`/
  `arb_bf16`, `fixed_*`, `extended_fd00..extended_fd12`, time-crate
  generators).
- **Cast operations** in `connections::conn::cast` — `ceiling`,
  `floor`, `upper`, `lower`, their `*1` / `*2` lifters, plus
  `maximize` / `minimize`. All re-exported at the crate root and
  marked `#[inline]` + `#[must_use]`.

#### Conn families

- **`conn::std::i64::decimal`** — decimal-SI ladder `FD00` (1 s) …
  `FD12` (1 ps). Adjacent and non-adjacent pair Conns
  (`FD<M>FD<N>`), plus IEEE-float bridges `F064FD<N>` for every
  rung.
- **`conn::fixed::{i8,i16,i32,i64,i128}` and `{u8,u16,u32,u64,u128}`**
  — `fixed`-crate-backed binary Q-format ladders. `i128` uses
  `checked_mul`+saturate.
- **`conn::int`** — signed-int widening (`I###I###`) and
  unsigned-source-into-signed-target (`U###I###`) families,
  range-extended via `Extended<T>`.
- **`conn::uint`** — unsigned widening (`U###U###`) and signed-into-
  unsigned saturating cast (`I###U###`) families.
- **`conn::float::f64`** — `F064F032`, `F064F016`, `F064B016`.
- **`conn::float::f32`** — `F032F016`, `F032B016`. (IEEE binary16
  and Google bfloat16 via the [`half`](https://docs.rs/half) crate.)
- **`conn::time`** — time-crate types: `DATEJDAY`, `TIMENANO`,
  `TIMESECS`, `DURNSECS`, `DURNFD09`, `PDTMDATE`, `OFDTNANO`,
  `OFDTSECS`.

#### Conventions

- 8-character Conn names with a fixed two-side shape (smaller-
  resolution / coarser tier on the right; see CLAUDE.md §Conn-name
  format).
- Module organization: one `conn::` submodule per dependency crate
  (`std`, `fixed`, `half`, `time`); type-named filenames; placement
  by specificity (specific > general; right > left as tie-breaker).

### Deferred (planned for future releases)

- Symmetric extensions of the integer Conn families (narrowing,
  cross-sign in the unsigned-target direction). Spec'd in the
  publish-prep audit notes.
- Half-bridge Conn relocation into `conn::half::{f16,bf16}` per the
  placement rules (currently still in `conn::float`).
- `int`/`uint` migration into per-type files under `conn::std`.
- Float-Duration bridges (`F064DURN`, `F032DURN`, etc.).
- `f128` Conns (blocked on stable `f128`).
- Runtime composition (`Conn::then` / `DynConn`).
- Audio-domain types (sample-rate ladders, rate↔FD12 cross-tier
  Conns) live in the downstream
  [`agogo`](https://gitlab.com/cmk/agogo) crate, not here.

### Requirements

- **MSRV**: Rust 1.85.

[0.1.0]: https://gitlab.com/cmk/connections/-/tags/v0.1.0
