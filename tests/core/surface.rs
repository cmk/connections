//! Surface-level smoke tests for the public `Conn` impls and the
//! `prelude` module added in plan-2026-05-19-01.

use connections::core::f064::F064F032;
use connections::core::i008::I008I016;
use connections::core::u008::U008U016;

#[test]
fn conn_eq_reflexive() {
    // `U008U016` and `I008I016` are `Conn<…>` consts; equality
    // compares the (f, g) fn-pointer pair via the hand-rolled
    // `PartialEq` on `Conn<A, B, K>`.
    assert_eq!(U008U016, U008U016);
    assert_eq!(I008I016, I008I016);
    // `F064F032` is a triple-marker unit struct from `conn_k!`; its
    // `PartialEq` is derived (unit-struct equality is trivially true).
    assert_eq!(F064F032, F064F032);
}

#[test]
fn conn_debug_non_empty() {
    // `Conn<…>`-valued constants render via the hand-rolled `Debug`
    // impl on `Conn<A, B, K>` (includes the source/target type names).
    let dbg = format!("{U008U016:?}");
    assert!(dbg.starts_with("Conn<"), "got {dbg:?}");
    assert!(dbg.contains("u8"), "missing source type name in {dbg:?}");
    assert!(dbg.contains("u16"), "missing target type name in {dbg:?}");

    let dbg_i = format!("{I008I016:?}");
    assert!(
        dbg_i.contains("i8"),
        "missing source type name in {dbg_i:?}"
    );
    assert!(
        dbg_i.contains("i16"),
        "missing target type name in {dbg_i:?}"
    );

    // Triple-marker unit structs render via their derived `Debug`
    // (the struct name).
    assert_eq!(format!("{F064F032:?}"), "F064F032");
}

#[test]
fn prelude_glob_brings_traits() {
    use connections::core::f064::F064F032;
    use connections::float::N5;
    use connections::prelude::*;

    // `ConnL::ceil` arrives via the prelude.
    let pi32 = F064F032
        .swap_l()
        .swap_r()
        .ceil(N5::new(std::f64::consts::PI));
    assert_eq!(pi32, N5::new(std::f32::consts::PI));

    // The bare two-sided helper `round` also arrives via the prelude.
    // 1.5 is exactly representable in f32, so the round-trip is lossless.
    let r = round(&F064F032, N5::new(1.5_f64));
    assert_eq!(r, N5::new(1.5_f32));
}
