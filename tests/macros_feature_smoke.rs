//! Smoke test for the `macros` feature surface (Plan 31 T4).
//!
//! Compiles only when `cargo test --features macros` is invoked.
//! Exercises each re-exported macro on a small local newtype to
//! verify the `$crate`-qualified paths resolve correctly outside
//! the crate that defines the macros.

#![cfg(feature = "macros")]

// The `connections::macros` namespace provides curated re-exports.
// Reference it once here so the smoke test fails to compile if the
// path is broken; individual tests below invoke macros via the
// crate-root paths (the way `#[macro_export]` actually surfaces them).
#[allow(unused_imports)]
use connections::macros as _curated_namespace;

// `iso!` — a tiny `MyId(u64) <-> u64` bijection.
mod iso_smoke {
    const fn fwd(x: u64) -> u64 {
        x
    }
    const fn bk(x: u64) -> u64 {
        x
    }

    connections::iso! {
        pub IDU064 : u64 => u64 {
            forward: fwd,
            back:    bk,
        }
    }

    #[test]
    fn iso_round_trip() {
        for v in [0_u64, 1, 42, u64::MAX] {
            assert_eq!(
                connections::conn::ceil(&IDU064, connections::conn::upper(&IDU064, v)),
                v
            );
        }
    }
}

// `conn_k!` — same shape as iso! but with explicit ceil/inner/floor.
mod triple_smoke {
    const fn ceil_(x: i32) -> i32 {
        x
    }
    const fn inner_(x: i32) -> i32 {
        x
    }
    const fn floor_(x: i32) -> i32 {
        x
    }

    connections::conn_k! {
        pub IDI032 : i32 => i32 {
            ceil:  ceil_,
            inner: inner_,
            floor: floor_,
        }
    }

    #[test]
    fn triple_both_views() {
        assert_eq!(connections::conn::ceil(&IDI032, 7), 7);
        assert_eq!(connections::conn::floor(&IDI032, 7), 7);
    }
}

// `uint_uint!` — saturating widening between unsigned primitives.
mod uint_uint_smoke {
    connections::uint_uint!(SMOKE_U008U016, u8, u16);

    #[test]
    fn widens() {
        assert_eq!(connections::conn::ceil(&SMOKE_U008U016, 255_u8), 255_u16);
    }

    #[test]
    fn inner_saturates() {
        assert_eq!(connections::conn::upper(&SMOKE_U008U016, u16::MAX), u8::MAX);
    }
}

// `ext_int!` — full triple with `Extended` source.
mod ext_int_smoke {
    use connections::extended::Extended;

    connections::ext_int!(SMOKE_EXT08, i8, i16);

    #[test]
    fn ext_finite() {
        assert_eq!(
            connections::conn::ceil(&SMOKE_EXT08, Extended::Finite(1_i8)),
            1_i16
        );
    }

    #[test]
    fn ext_synthetic() {
        // `inner` saturates outside [BELOW, ABOVE] to NegInf/PosInf.
        assert_eq!(
            connections::conn::upper(&SMOKE_EXT08, i16::MIN),
            Extended::NegInf
        );
        assert_eq!(
            connections::conn::upper(&SMOKE_EXT08, i16::MAX),
            Extended::PosInf
        );
    }
}

// Light verification that the other narrowing/cross-sign macros
// also expand cleanly outside the crate. We don't exhaustively
// test their semantics here — the in-crate `tests/fixed_*.rs`
// integration tests already cover that.
mod narrow_macro_smoke {
    connections::int_int_narrow!(SMOKE_I016I008, i16, i8);
    connections::uint_uint_narrow!(SMOKE_U016U008, u16, u8);
    connections::int_uint_narrow!(SMOKE_I016U008, i16, u8);
    connections::uint_int_sat!(SMOKE_U016I008, u16, i8);
    connections::int_uint!(SMOKE_I008U008, i8, u8);

    #[test]
    fn all_compile() {
        // Touch each so the compiler doesn't dead-code them.
        let _ = connections::conn::ceil(&SMOKE_I016I008, 0_i16);
        let _ = connections::conn::ceil(&SMOKE_U016U008, 0_u16);
        let _ = connections::conn::ceil(&SMOKE_I016U008, 0_i16);
        let _ = connections::conn::floor(&SMOKE_U016I008, 0_u16);
        let _ = connections::conn::ceil(&SMOKE_I008U008, 0_i8);
    }
}

// `nz_int_ext!` and `nz_uint_ext!` — NonZero adjoints.
mod nz_smoke {
    use core::num::{NonZeroI8, NonZeroU8};

    connections::nz_int_ext!(SmokeNzI8, i8, NonZeroI8);
    connections::nz_uint_ext!(SMOKE_NZ_U8, u8, NonZeroU8);

    #[test]
    fn nz_int_at_zero() {
        // floor and ceil split zero between -1 and +1.
        assert_eq!(
            connections::conn::floor(&SmokeNzI8, 0_i8),
            NonZeroI8::new(-1).unwrap()
        );
        assert_eq!(
            connections::conn::ceil(&SmokeNzI8, 0_i8),
            NonZeroI8::new(1).unwrap()
        );
    }

    #[test]
    fn nz_uint_at_zero() {
        // Unsigned: 0 collapses to NonZero(1) via ceil.
        assert_eq!(
            connections::conn::ceil(&SMOKE_NZ_U8, 0_u8),
            NonZeroU8::new(1).unwrap()
        );
    }
}
