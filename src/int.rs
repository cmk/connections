//! **Deprecated module path — use [`crate::fixed`] instead.**
//!
//! Connections rooted in primitive types from [`std`]. Per Plan 25,
//! every Conn const here is a Q*N*.0 fixed-point Conn, and the
//! contents are being folded into [`crate::fixed`]. The module
//! continues to expose its existing `pub mod iN` / `pub mod uN`
//! submodules during the transition; the per-primitive Conn-hosting
//! files (`src/int/iN.rs`, `src/int/uN.rs`) are merged into their
//! `src/fixed/iN.rs` / `src/fixed/uN.rs` siblings in T2 and the
//! whole tree is deleted in T10.
//!
//! The seven generator macros (`uint_uint!`, `int_uint!`, `ext_int!`,
//! `int_int_narrow!`, `uint_uint_narrow!`, `int_uint_narrow!`,
//! `uint_int_sat!`) now live in [`crate::fixed`]. The per-primitive
//! submodule files in `src/int/` import them via re-export shims
//! below so they keep building until T2 removes them.

// All per-primitive submodules (`int/iN.rs`, `int/uN.rs`) are now
// re-export shims pointing at `crate::fixed::iN` / `crate::fixed::uN`,
// so the macro re-exports added in T1 are no longer needed. The
// macros live solely in `crate::fixed`.

pub mod i128;
pub mod i16;
pub mod i32;
pub mod i64;
pub mod i8;
pub mod u128;
pub mod u16;
pub mod u32;
pub mod u64;
pub mod u8;
