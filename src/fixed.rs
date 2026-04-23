//! Decimal fixed-point ladder: `Uni / Deci / Centi / Milli / Micro / Nano / Pico`.
//!
//! Each type is an `i64` numerator with an implicit 10⁻ᵏ denominator:
//!
//! - `Uni(i)   = i × 10⁰`
//! - `Deci(i)  = i × 10⁻¹`
//! - `Centi(i) = i × 10⁻²`
//! - `Milli(i) = i × 10⁻³`
//! - `Micro(i) = i × 10⁻⁶`
//! - `Nano(i)  = i × 10⁻⁹`
//! - `Pico(i)  = i × 10⁻¹²`
//!
//! For every ordered pair `(Fine, Coarse)` where `Fine`'s resolution is
//! strictly smaller, there is a [`Conn`]`<Fine, Coarse>` named
//! `FxxFyy` after Haskell's `fXYfZW`:
//!
//! - `ceil:  Fine → Coarse`  smallest `c` with `inner(c) ≥ f`
//! - `inner: Coarse → Fine`  exact embedding (`c × PREC_ratio`)
//! - `floor: Fine → Coarse`  largest `c` with `inner(c) ≤ f`
//!
//! Ported from `Data.Connection.Fixed` in
//! <https://github.com/cmk/connections> (Haskell).
//!
//! Both rounding functions use [`i64::div_euclid`] / [`i64::rem_euclid`]
//! so negative inputs round consistently toward −∞ for `floor` and
//! toward +∞ for `ceil`. This matches the documented adjoint-triple
//! semantics of [`Conn`]; the Haskell `fixfix` `h` used `div` with a
//! `j − 1` fixup on nonzero remainder, which does not satisfy the
//! standard lower-adjoint Galois law and is believed to be an
//! idiosyncrasy of the Haskell implementation rather than an
//! intentional different convention. (Haskell `ratfix`'s `h` is a
//! plain `div`, matching this port.)

use crate::conn::Conn;

macro_rules! def_fixed {
    ($name:ident, $prec:expr) => {
        #[repr(transparent)]
        #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
        pub struct $name(pub i64);

        impl HasResolution for $name {
            const PREC: i64 = $prec;
        }

        impl $name {
            pub const ZERO: Self = Self(0);
        }
    };
}

/// Decimal precision marker: `PREC` is the denominator such that a
/// value `T(i)` represents `i × 10⁻ᵏ` with `PREC = 10ᵏ`.
pub trait HasResolution {
    const PREC: i64;
}

def_fixed!(Uni,   1);
def_fixed!(Deci,  10);
def_fixed!(Centi, 100);
def_fixed!(Milli, 1_000);
def_fixed!(Micro, 1_000_000);
def_fixed!(Nano,  1_000_000_000);
def_fixed!(Pico,  1_000_000_000_000);

// ────────────────────────────────────────────────────────────────────
// Fine → Coarse connection constructors.
//
// For each pair, the ratio `prec = Fine::PREC / Coarse::PREC` is the
// multiplier `inner` applies to go Coarse → Fine (e.g. 1 Uni = 1000
// Milli, so `F03F00`'s prec is 1000).
//
// The block-scoped `fn` items inside each `const` expression are
// monomorphic and get coerced to `fn(_) -> _` pointers at const-eval,
// which is all `Conn` asks for.
// ────────────────────────────────────────────────────────────────────

macro_rules! fix_fix {
    ($const_name:ident, $Fine:ident, $Coarse:ident, $prec:expr) => {
        pub const $const_name: Conn<$Fine, $Coarse> = {
            const PREC: i64 = $prec;
            fn ceil(x: $Fine) -> $Coarse {
                let q = x.0.div_euclid(PREC);
                if x.0.rem_euclid(PREC) != 0 {
                    $Coarse(q + 1)
                } else {
                    $Coarse(q)
                }
            }
            fn inner(x: $Coarse) -> $Fine {
                $Fine(x.0 * PREC)
            }
            fn floor(x: $Fine) -> $Coarse {
                $Coarse(x.0.div_euclid(PREC))
            }
            Conn::new(ceil, inner, floor)
        };
    };
}

// Adjacent (one step on the ladder).
fix_fix!(F01F00, Deci,  Uni,   10);
fix_fix!(F02F01, Centi, Deci,  10);
fix_fix!(F03F02, Milli, Centi, 10);
fix_fix!(F06F03, Micro, Milli, 1_000);
fix_fix!(F09F06, Nano,  Micro, 1_000);
fix_fix!(F12F09, Pico,  Nano,  1_000);

// Non-adjacent (direct shortcut; matches Haskell verbatim).
fix_fix!(F02F00, Centi, Uni,   100);
fix_fix!(F03F00, Milli, Uni,   1_000);
fix_fix!(F03F01, Milli, Deci,  100);
fix_fix!(F06F00, Micro, Uni,   1_000_000);
fix_fix!(F06F01, Micro, Deci,  100_000);
fix_fix!(F06F02, Micro, Centi, 10_000);
fix_fix!(F09F00, Nano,  Uni,   1_000_000_000);
fix_fix!(F09F01, Nano,  Deci,  100_000_000);
fix_fix!(F09F02, Nano,  Centi, 10_000_000);
fix_fix!(F09F03, Nano,  Milli, 1_000_000);
fix_fix!(F12F00, Pico,  Uni,   1_000_000_000_000);
fix_fix!(F12F01, Pico,  Deci,  100_000_000_000);
fix_fix!(F12F02, Pico,  Centi, 10_000_000_000);
fix_fix!(F12F03, Pico,  Milli, 1_000_000_000);
fix_fix!(F12F06, Pico,  Micro, 1_000_000);

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Sanity spot checks (hand-computed).

    #[test]
    fn spot_milli_uni_positive() {
        assert_eq!(F03F00.ceil(Milli(5)), Uni(1));
        assert_eq!(F03F00.floor(Milli(5)), Uni(0));
        assert_eq!(F03F00.ceil(Milli(1_000)), Uni(1));
        assert_eq!(F03F00.floor(Milli(1_000)), Uni(1));
        assert_eq!(F03F00.ceil(Milli(999)), Uni(1));
        assert_eq!(F03F00.floor(Milli(999)), Uni(0));
    }

    #[test]
    fn spot_milli_uni_negative() {
        // div_euclid rounds toward −∞; rem_euclid is non-negative.
        // -5 / 1000: div_euclid = -1, rem_euclid = 995.
        assert_eq!(F03F00.ceil(Milli(-5)), Uni(0));
        assert_eq!(F03F00.floor(Milli(-5)), Uni(-1));
    }

    #[test]
    fn spot_pico_uni_exact_boundary() {
        assert_eq!(F12F00.ceil(Pico(1_000_000_000_000)), Uni(1));
        assert_eq!(F12F00.floor(Pico(1_000_000_000_000)), Uni(1));
        assert_eq!(F12F00.inner(Uni(1)), Pico(1_000_000_000_000));
    }

    #[test]
    fn spot_inner_roundtrip_across_ladder() {
        // inner is exact — multiplying up and down gets us back.
        assert_eq!(F03F00.ceil(F03F00.inner(Uni(42))), Uni(42));
        assert_eq!(F03F00.floor(F03F00.inner(Uni(-42))), Uni(-42));
        assert_eq!(F12F06.ceil(F12F06.inner(Micro(987))), Micro(987));
    }

    // ────────────────────────────────────────────────────────────
    // Proptest strategies
    //
    // For each (Fine, Coarse) pair with ratio PREC, the `inner` call
    // computes `coarse * PREC` which must fit i64. Strategies clamp
    // the coarse-side input to `|x| < i64::MAX / PREC` to avoid
    // overflow inside the connection itself. The fine-side input is
    // bounded by i64 range naturally.
    // ────────────────────────────────────────────────────────────

    fn bounded_coarse(prec: i64) -> impl Strategy<Value = i64> {
        let limit = i64::MAX / prec;
        prop_oneof![
            1 => Just(0_i64),
            1 => Just(1_i64),
            1 => Just(-1_i64),
            1 => Just(limit),
            1 => Just(-limit),
            5 => -limit..=limit,
        ]
    }

    fn bounded_fine(prec: i64) -> impl Strategy<Value = i64> {
        // Fine-side can hit full i64 range safely; `floor(fine, prec)`
        // and `ceil(fine, prec)` both fit in i64. Bias toward boundaries.
        prop_oneof![
            1 => Just(0_i64),
            1 => Just(prec),
            1 => Just(-prec),
            1 => Just(prec - 1),
            1 => Just(-(prec - 1)),
            1 => Just(prec + 1),
            1 => Just(-(prec + 1)),
            1 => Just(i64::MAX),
            1 => Just(i64::MIN + 1), // i64::MIN causes overflow under negation in some checks
            5 => any::<i64>(),
        ]
    }

    // Each test is written for one Conn and one (Fine, Coarse) pair,
    // then expanded via macro across the 21 connections.

    macro_rules! props_for_pair {
        ($mod:ident, $conn:ident, $Fine:ident, $Coarse:ident, $prec:expr) => {
            mod $mod {
                use super::*;

                proptest! {
                    #[test]
                    fn inner_then_ceil_is_id(c in bounded_coarse($prec)) {
                        let b = $Coarse(c);
                        prop_assert_eq!($conn.ceil($conn.inner(b)), b);
                    }

                    #[test]
                    fn inner_then_floor_is_id(c in bounded_coarse($prec)) {
                        let b = $Coarse(c);
                        prop_assert_eq!($conn.floor($conn.inner(b)), b);
                    }

                    #[test]
                    fn ceil_monotone(x in bounded_fine($prec), y in bounded_fine($prec)) {
                        let (lo, hi) = if x <= y { ($Fine(x), $Fine(y)) } else { ($Fine(y), $Fine(x)) };
                        prop_assert!($conn.ceil(lo) <= $conn.ceil(hi));
                    }

                    #[test]
                    fn floor_monotone(x in bounded_fine($prec), y in bounded_fine($prec)) {
                        let (lo, hi) = if x <= y { ($Fine(x), $Fine(y)) } else { ($Fine(y), $Fine(x)) };
                        prop_assert!($conn.floor(lo) <= $conn.floor(hi));
                    }

                    #[test]
                    fn floor_le_ceil(x in bounded_fine($prec)) {
                        let fx = $Fine(x);
                        let c = $conn.ceil(fx);
                        let f = $conn.floor(fx);
                        prop_assert!(f <= c);
                        // And differ by ≤ 1 ULP of Coarse.
                        prop_assert!(c.0 - f.0 <= 1);
                    }

                    #[test]
                    fn galois_upper(
                        x in bounded_fine($prec),
                        c in bounded_coarse($prec),
                    ) {
                        let fx = $Fine(x);
                        let cx = $Coarse(c);
                        // ceil(x) ≤ c  ⟺  x ≤ inner(c)
                        prop_assert_eq!(
                            $conn.ceil(fx) <= cx,
                            fx <= $conn.inner(cx)
                        );
                    }

                    #[test]
                    fn galois_lower(
                        x in bounded_fine($prec),
                        c in bounded_coarse($prec),
                    ) {
                        let fx = $Fine(x);
                        let cx = $Coarse(c);
                        // inner(c) ≤ x  ⟺  c ≤ floor(x)
                        prop_assert_eq!(
                            $conn.inner(cx) <= fx,
                            cx <= $conn.floor(fx)
                        );
                    }
                }
            }
        };
    }

    // Adjacent pairs.
    props_for_pair!(p_f01f00, F01F00, Deci,  Uni,   10);
    props_for_pair!(p_f02f01, F02F01, Centi, Deci,  10);
    props_for_pair!(p_f03f02, F03F02, Milli, Centi, 10);
    props_for_pair!(p_f06f03, F06F03, Micro, Milli, 1_000);
    props_for_pair!(p_f09f06, F09F06, Nano,  Micro, 1_000);
    props_for_pair!(p_f12f09, F12F09, Pico,  Nano,  1_000);

    // Non-adjacent pairs.
    props_for_pair!(p_f02f00, F02F00, Centi, Uni,   100);
    props_for_pair!(p_f03f00, F03F00, Milli, Uni,   1_000);
    props_for_pair!(p_f03f01, F03F01, Milli, Deci,  100);
    props_for_pair!(p_f06f00, F06F00, Micro, Uni,   1_000_000);
    props_for_pair!(p_f06f01, F06F01, Micro, Deci,  100_000);
    props_for_pair!(p_f06f02, F06F02, Micro, Centi, 10_000);
    props_for_pair!(p_f09f00, F09F00, Nano,  Uni,   1_000_000_000);
    props_for_pair!(p_f09f01, F09F01, Nano,  Deci,  100_000_000);
    props_for_pair!(p_f09f02, F09F02, Nano,  Centi, 10_000_000);
    props_for_pair!(p_f09f03, F09F03, Nano,  Milli, 1_000_000);
    props_for_pair!(p_f12f00, F12F00, Pico,  Uni,   1_000_000_000_000);
    props_for_pair!(p_f12f01, F12F01, Pico,  Deci,  100_000_000_000);
    props_for_pair!(p_f12f02, F12F02, Pico,  Centi, 10_000_000_000);
    props_for_pair!(p_f12f03, F12F03, Pico,  Milli, 1_000_000_000);
    props_for_pair!(p_f12f06, F12F06, Pico,  Micro, 1_000_000);

    // Composition: the direct non-adjacent Conn agrees with climbing
    // the ladder step-by-step. Check Pico→Uni against the 4-step climb.
    proptest! {
        #[test]
        fn composition_pico_to_uni_matches_ladder_climb(
            p in bounded_fine(1_000_000_000_000i64),
        ) {
            let pico = Pico(p);
            let direct_ceil = F12F00.ceil(pico);
            let climb_ceil =
                F03F00.ceil(F06F03.ceil(F09F06.ceil(F12F09.ceil(pico))));
            prop_assert_eq!(direct_ceil, climb_ceil);

            let direct_floor = F12F00.floor(pico);
            let climb_floor =
                F03F00.floor(F06F03.floor(F09F06.floor(F12F09.floor(pico))));
            prop_assert_eq!(direct_floor, climb_floor);
        }
    }

    // Negative-value regression: every Galois property holds for i < 0.
    // (Covered inside each pair's proptest since bounded_fine / bounded_coarse
    //  emit negatives; this stand-alone confirms the exact boundary Uni(-5).)
    #[test]
    fn regression_negative_milli_uni() {
        assert_eq!(F03F00.ceil(Milli(-1_000)), Uni(-1));
        assert_eq!(F03F00.floor(Milli(-1_000)), Uni(-1));
        assert_eq!(F03F00.ceil(Milli(-1_001)), Uni(-1));
        assert_eq!(F03F00.floor(Milli(-1_001)), Uni(-2));
    }
}
