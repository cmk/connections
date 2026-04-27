//! Connections over fractional number representations.
//!
//! - [`decimal`] — `i64`-backed SI-prefix ladder (`FD00`..`FD12`,
//!   base-10 scaling). Hand-rolled, independent of the upstream
//!   `fixed` crate.
//! - [`i08`] / [`i16`] / [`i32`] / [`i64`] — `fixed`-crate
//!   `FixedI<width><Frac>` ladders (base-2 scaling). The submodule
//!   name encodes the inner primitive width; `Frac` levels are
//!   encoded in the Conn-constant names (`I<frac>I<frac>`, three-digit
//!   zero-padded).

pub mod decimal;
pub mod i08;
pub mod i16;
pub mod i32;
pub mod i64;

// `Ple` impls for the `fixed`-crate signed types backing the binary
// sub-modules. The `<=` semantics are the same as `PartialOrd` (values
// are totally ordered by their underlying integer bits); this just
// re-exposes them through the `Ple` trait so `property::laws::conn_*`
// predicates accept the binary `Conn` constants directly.

use crate::lattice::Ple;

impl<F: ::fixed::types::extra::LeEqU8> Ple for ::fixed::FixedI8<F> {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}

impl<F: ::fixed::types::extra::LeEqU16> Ple for ::fixed::FixedI16<F> {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}

impl<F: ::fixed::types::extra::LeEqU32> Ple for ::fixed::FixedI32<F> {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}

impl<F: ::fixed::types::extra::LeEqU64> Ple for ::fixed::FixedI64<F> {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}
