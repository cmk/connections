//! Connections rooted in `i64`.
//!
//! Currently nests the custom [`decimal`] SI-prefix ladder, which
//! views `i64` as the storage backing for fixed-point time rungs
//! `FD00` (1 s) through `FD12` (1 ps). Decimal-decimal Conns
//! (`FD<M>FD<N>`) and float-decimal bridges (`F064FD<N>`) all live
//! there.
//!
//! Width-crossing integer Conns where `i64` is the placement target
//! (e.g. `I008I064`, `U032I064`) will land alongside as the
//! per-crate-module migration completes.

pub mod decimal;
