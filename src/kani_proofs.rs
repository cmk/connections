//! SMT-verified Galois-connection laws via [Kani].
//!
//! This subtree mirrors the macro families in [`crate::fixed`] one
//! file per family. Each `#[kani::proof]` harness is the SMT
//! analogue of one of the proptest cases under `tests/*_galois.rs` —
//! same predicate (from [`crate::prop::conn`]), but the input is a
//! `kani::any::<_>()` symbolic value rather than a sampled
//! `proptest::any!()`. CBMC then bit-blasts the predicate over the
//! full input domain and either returns a proof or surfaces a
//! counterexample.
//!
//! ## Running
//!
//! Install once:
//!
//! ```text
//! cargo install --locked kani-verifier
//! cargo kani setup
//! ```
//!
//! Then from the crate root:
//!
//! ```text
//! cargo kani                    # all harnesses
//! cargo kani --harness <name>   # one harness
//! ```
//!
//! ## Layout
//!
//! | Module                 | Macro family                                   |
//! |------------------------|------------------------------------------------|
//! | [`int_narrow`]         | [`crate::int_int_narrow!`]                     |
//! | [`uint_sat`]           | [`crate::uint_int_sat!`] (single-sided R)      |
//! | [`nz_ext`]             | [`crate::nz_int_ext!`] (signed triple)         |
//! | [`fix_fix_signed`]     | `fix_fix_iN!` (Q-format ladder, signed)        |
//! | [`fix_fix_unsigned`]   | `fix_fix_uN!` (Q-format ladder, unsigned)      |
//! | [`iso_family`]         | [`crate::iso!`] (lossless cross-crate iso)     |
//! | [`float_walk`]         | F064F032 ULP-walk iteration upper bound        |
//! | [`float_weaker`]       | F064F032 finite-domain weaker properties       |
//!
//! [Kani]: https://model-checking.github.io/kani/

#![allow(dead_code, unused_imports)]

mod fix_fix_signed;
mod fix_fix_unsigned;
mod float_walk;
mod float_weaker;
mod int_narrow;
mod iso_family;
mod nz_ext;
mod uint_sat;
