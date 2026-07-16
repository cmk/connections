# Changelog

All notable changes to this crate will be documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2026-07-16

Initial release. A Rust port of the Haskell
[`connections`](https://github.com/cmk/connections) library: Galois
connections encoded as first-class `Conn<A, B, K>` values, with a
lattice hierarchy and per-host-crate numeric cast families on top.

### Added

- **`Conn<A, B, K>`** — a Galois connection stored as bare `fn` pointers;
  `Copy`, `const`-constructible, heap-free. The kind `K` selects the
  surface: `L` (left, `ceil ⊣ inner`), `R` (right, `inner ⊣ floor`), or
  the adjoint triple `ceil ⊣ inner ⊣ floor`. Constructors `Conn::new_l`,
  `Conn::new_r`, `Conn::identity`, plus kind-gated inherent accessors
  (`ceil` / `upper` / `floor` / `lower` / `round` / `truncate` /
  `median` / `interval` and their `*1` / `*2` lifters).
- **Capability traits `ConnL` / `ConnR` / `ConnK`** — one swap method
  each; `ConnK` is the adjoint-triple super-trait, blanket-implemented
  for every `ConnL + ConnR`.
- **Three-surface prelude** — `prelude::left`, `prelude::right`, and
  `prelude::bilateral` each bundle the matching trait, kind marker, and
  `conn_*!` / `compose_*!` / `lift_*!` macros; `prelude::*` unions all
  three plus the shared core (`Conn`, `Extended`, `compose!`, `iso!`).
- **Cast families** — `core` (std ints `i8`…`u128`, `f16` / `f32` /
  `f64`, `char`, `bool`, `NonZero`), `fixed` ([`fixed`]-crate Q-formats
  with cross-crate isos and float bridges), `time` (`time` crate +
  `std::time`), `hifi` ([`hifitime`]), `uhlc` ([`uhlc`] hybrid logical
  clock), and `addr` (`std::net` IP / socket). 8-character two-side Conn
  names throughout.
- **`N5`** — IEEE-float wrapper giving NaN a reflexive preorder so the
  Galois laws can quantify over it, with the ULP / rounding machinery and
  `float_ext_int!` bridges. **`Extended<T>`** — a `NegInf` / `Finite` /
  `PosInf` three-point extension recovering the lattice top and bottom
  that std primitives lack. **`Interval<A>`**.
- **Lattice traits** in `connections::lattice` — `Join`, `Meet`,
  `Heyting`, `Coheyting`, `Symmetric`, `Boolean`.
- **`connections::prop`** — pure `bool`-returning Galois-law predicates
  (`prop::conn`, `prop::interval`, `prop::lattice`; always public, no
  `proptest` dependency) plus proptest strategies (`prop::arb`, behind
  the `proptest` feature).
- **Codegen macros** — `conn_l!` / `conn_r!` / `conn_k!` / `iso!`
  (declaration-form Conn constructors), `compose!` / `compose_l!` /
  `compose_r!` / `compose_k!` (compile-time composition), and `lift_l!` /
  `lift_r!` / `lift_k!` (endpoint lifting). Exported at the crate root
  under the default-on `macros` feature, and re-exported as
  `connections::macros::*`.

### Features

- `macros` (**default**) — lift the codegen macros to the crate root.
- `fixed`, `time`, `hifi`, `uhlc` — enable the matching cast family (each
  pulls one optional dependency).
- `proptest` — expose the `prop::arb` strategies to downstream crates.
- `f16`, `try_trait` — nightly-only (`#![feature(f16)]` /
  `#![feature(try_trait_v2)]`); off by default and out of the docs.rs
  build.

### Requirements

- **MSRV**: Rust 1.88, edition 2024.
- No `unsafe` — `#![forbid(unsafe_code)]` where the macro layer permits.

[`fixed`]: https://docs.rs/fixed
[`hifitime`]: https://docs.rs/hifitime
[`uhlc`]: https://docs.rs/uhlc

[0.1.0]: https://github.com/cmk/connections/releases/tag/v0.1.0
