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
use crate::extended::Extended;
use crate::float_ext::FloatExt;
use crate::order::Ple;

macro_rules! def_fixed {
    ($name:ident, $prec:expr) => {
        #[repr(transparent)]
        #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
        pub struct $name(pub i64);

        impl HasResolution for $name {
            const PREC: i64 = $prec;
        }

        impl Ple for $name {
            fn ple(&self, other: &Self) -> bool {
                self.0 <= other.0
            }
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

// FloatExt<f??> → Extended<Rung>. Lawful under `PartialOrd` on both
// sides.
//
// Source lattice (`FloatExt<T>`):
//   `Bot` < `Finite(-∞)` < `Finite(finite)` < `Finite(+∞)` < `Top`,
//   with `Finite(NaN)` reflexive and incomparable with every other
//   `Finite(_)`.
//
// Target lattice (`Extended<Rung>`):
//   `NegInf` < `Finite(Rung(i64::MIN))` < … < `Finite(Rung(i64::MAX))`
//   < `PosInf`.
//
// `inner` embeds the target into the source: `NegInf → Bot`,
// `PosInf → Top`, `Finite(r) → Finite(r/PREC)`. The adjoint laws then
// fix the saturation behaviour of `ceil` and `floor`:
//
// | source input          | ceil                 | floor                 |
// |-----------------------|----------------------|-----------------------|
// | `Bot`                 | `NegInf`             | `NegInf`              |
// | `Top`                 | `PosInf`             | `PosInf`              |
// | `Finite(NaN)`         | `PosInf`             | `NegInf`              |
// | `Finite(-∞)`          | `Finite(Rung::MIN)`  | `NegInf`              |
// | `Finite(+∞)`          | `PosInf`             | `Finite(Rung::MAX)`   |
// | finite < inner(MIN)   | `Finite(Rung::MIN)`  | `NegInf`              |
// | finite > inner(MAX)   | `PosInf`             | `Finite(Rung::MAX)`   |
// | finite in range       | round-up rung        | round-down rung       |
//
// Note the asymmetry: source ±∞ maps to `Finite(Rung::MIN/MAX)` under
// the "inward" adjoint and to `±Inf` under the "outward" one. That
// falls directly out of the Galois law — target ±Inf is above/below
// every Finite, and inner(±Inf) = Bot/Top sit strictly outside the
// source's ±∞.
macro_rules! float_conn {
    ($const_name:ident, $float:ty, $Rung:ident, $prec:expr) => {
        pub const $const_name: Conn<FloatExt<$float>, Extended<$Rung>> = {
            const PREC: i64 = $prec;
            const PREC_F: f64 = PREC as f64;

            // `inner(Rung)` reinterpreted as f64 for comparisons with
            // `x as f64`. For f32 conns this narrows-then-widens so
            // the adjoint condition holds against the value f32
            // actually stores, not the f64 intermediate.
            fn inner_as_f64(c: i64) -> f64 {
                ((c as f64) / PREC_F) as $float as f64
            }

            fn ceil(x: FloatExt<$float>) -> Extended<$Rung> {
                let f = match x {
                    FloatExt::Bot => return Extended::NegInf,
                    FloatExt::Top => return Extended::PosInf,
                    FloatExt::Finite(v) => v,
                };
                if f.is_nan() {
                    return Extended::PosInf;
                }
                if f == <$float>::INFINITY {
                    return Extended::PosInf;
                }
                if f == <$float>::NEG_INFINITY {
                    return Extended::Finite($Rung(i64::MIN));
                }
                let xf = f as f64;
                let scaled = xf * PREC_F;
                if scaled > i64::MAX as f64 {
                    return Extended::PosInf;
                }
                if scaled < i64::MIN as f64 {
                    return Extended::Finite($Rung(i64::MIN));
                }
                // Initial estimate from f64 math; correct for drift
                // (bounded by ±1 ULP of the scaled product) so the
                // Galois law holds exactly.
                let mut c = scaled.ceil() as i64;
                while c < i64::MAX && inner_as_f64(c) < xf {
                    c += 1;
                }
                while c > i64::MIN + 1 && inner_as_f64(c - 1) >= xf {
                    c -= 1;
                }
                Extended::Finite($Rung(c))
            }

            fn inner(b: Extended<$Rung>) -> FloatExt<$float> {
                match b {
                    Extended::NegInf => FloatExt::Bot,
                    Extended::PosInf => FloatExt::Top,
                    Extended::Finite(r) => {
                        FloatExt::Finite(((r.0 as f64) / PREC_F) as $float)
                    }
                }
            }

            fn floor(x: FloatExt<$float>) -> Extended<$Rung> {
                let f = match x {
                    FloatExt::Bot => return Extended::NegInf,
                    FloatExt::Top => return Extended::PosInf,
                    FloatExt::Finite(v) => v,
                };
                if f.is_nan() {
                    return Extended::NegInf;
                }
                if f == <$float>::INFINITY {
                    return Extended::Finite($Rung(i64::MAX));
                }
                if f == <$float>::NEG_INFINITY {
                    return Extended::NegInf;
                }
                let xf = f as f64;
                let scaled = xf * PREC_F;
                if scaled > i64::MAX as f64 {
                    return Extended::Finite($Rung(i64::MAX));
                }
                if scaled < i64::MIN as f64 {
                    return Extended::NegInf;
                }
                let mut c = scaled.floor() as i64;
                while c > i64::MIN + 1 && inner_as_f64(c) > xf {
                    c -= 1;
                }
                while c < i64::MAX && inner_as_f64(c + 1) <= xf {
                    c += 1;
                }
                Extended::Finite($Rung(c))
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// F64Fxx only. An f32 version would have the same shape but inner
// would narrow i64 → f32, which can collapse up to ~120k consecutive
// Rung values onto the same f32 (for Pico scale). The adjoint law
// still holds, but ceil/floor would have to walk the full collapse
// class to find the smallest lawful c — O(plateau size) per call.
//
// f32 callers widen losslessly at the boundary —
// `F64F06.ceil(FloatExt::Finite(arg_f32 as f64))` — and get the
// same adjoint answer as native f64 input.
float_conn!(F64F00, f64, Uni,   1);
float_conn!(F64F01, f64, Deci,  10);
float_conn!(F64F02, f64, Centi, 100);
float_conn!(F64F03, f64, Milli, 1_000);
float_conn!(F64F06, f64, Micro, 1_000_000);
float_conn!(F64F09, f64, Nano,  1_000_000_000);
float_conn!(F64F12, f64, Pico,  1_000_000_000_000);

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

    // ── FloatExt<f??> → Extended<Rung> connections ─────────────────

    // Narrow float generators: arbitrary-bit-pattern `any::<f??>()` shrinks
    // bit-by-bit and dominates proptest runtime without finding structural
    // bugs. A bounded range plus explicit boundaries gives wide enough
    // adjoint-law coverage.
    fn arb_f64_full() -> impl Strategy<Value = f64> {
        prop_oneof![
            6 => -1.0e9_f64..1.0e9_f64,
            1 => prop_oneof![
                Just(f64::NAN),
                Just(f64::INFINITY),
                Just(f64::NEG_INFINITY),
                Just(0.0_f64),
                Just(-0.0_f64),
                Just(f64::MIN_POSITIVE),
                Just(f64::MAX),
                Just(f64::MIN),
            ],
        ]
    }

    fn arb_float_ext_f64() -> impl Strategy<Value = FloatExt<f64>> {
        prop_oneof![
            1 => Just(FloatExt::Bot),
            1 => Just(FloatExt::Top),
            8 => arb_f64_full().prop_map(FloatExt::Finite),
        ]
    }

    // Bounded rung generators: arbitrary i64 shrinks bit-by-bit over
    // pathologically large integers. Cap to `±i64::MAX / PREC` (the
    // "inside-the-ladder" region) and add explicit i64 edges as `Just`.
    fn arb_extended_micro() -> impl Strategy<Value = Extended<Micro>> {
        let limit = i64::MAX / Micro::PREC;
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            1 => Just(Extended::Finite(Micro(i64::MAX))),
            1 => Just(Extended::Finite(Micro(i64::MIN))),
            8 => (-limit..=limit).prop_map(|x| Extended::Finite(Micro(x))),
        ]
    }

    fn arb_extended_pico() -> impl Strategy<Value = Extended<Pico>> {
        let limit = i64::MAX / Pico::PREC;
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            1 => Just(Extended::Finite(Pico(i64::MAX))),
            1 => Just(Extended::Finite(Pico(i64::MIN))),
            8 => (-limit..=limit).prop_map(|x| Extended::Finite(Pico(x))),
        ]
    }

    // Spot checks with exactly-representable f64 values.
    #[test]
    fn float_conn_spot() {
        let half = FloatExt::Finite(0.5_f64);
        assert_eq!(F64F03.ceil(half), Extended::Finite(Milli(500)));
        assert_eq!(F64F03.floor(half), Extended::Finite(Milli(500)));
        assert_eq!(F64F06.ceil(half), Extended::Finite(Micro(500_000)));
        assert_eq!(F64F12.ceil(FloatExt::Finite(0.25_f64)),
                   Extended::Finite(Pico(250_000_000_000)));

        let one_and_half = FloatExt::Finite(1.5_f64);
        assert_eq!(F64F06.ceil(one_and_half), Extended::Finite(Micro(1_500_000)));
        assert_eq!(F64F06.floor(one_and_half), Extended::Finite(Micro(1_500_000)));
        assert_eq!(F64F06.inner(Extended::Finite(Micro(1_500_000))),
                   FloatExt::Finite(1.5_f64));

        // Saturation map (matches the table in the macro doc comment).
        assert_eq!(F64F06.ceil(FloatExt::Bot), Extended::NegInf);
        assert_eq!(F64F06.floor(FloatExt::Bot), Extended::NegInf);
        assert_eq!(F64F06.ceil(FloatExt::Top), Extended::PosInf);
        assert_eq!(F64F06.floor(FloatExt::Top), Extended::PosInf);

        let nan: FloatExt<f64> = FloatExt::Finite(f64::NAN);
        assert_eq!(F64F06.ceil(nan), Extended::PosInf);
        assert_eq!(F64F06.floor(nan), Extended::NegInf);

        let pos_inf: FloatExt<f64> = FloatExt::Finite(f64::INFINITY);
        assert_eq!(F64F06.ceil(pos_inf), Extended::PosInf);
        assert_eq!(F64F06.floor(pos_inf), Extended::Finite(Micro(i64::MAX)));

        let neg_inf: FloatExt<f64> = FloatExt::Finite(f64::NEG_INFINITY);
        assert_eq!(F64F06.ceil(neg_inf), Extended::Finite(Micro(i64::MIN)));
        assert_eq!(F64F06.floor(neg_inf), Extended::NegInf);

        // Inner maps target ±Inf to FloatExt's Top/Bot (synthetic
        // bounds outside the float range), NOT to Finite(±f64::INFINITY).
        assert_eq!(F64F06.inner(Extended::PosInf), FloatExt::Top);
        assert_eq!(F64F06.inner(Extended::NegInf), FloatExt::Bot);
    }

    // Helper: partial-order "less than or equal" — Galois laws read
    // cleanest phrased as `partial_cmp != Some(Greater)`, which means
    // "either less, equal, or incomparable".
    //
    // That's not the adjoint law, though. The adjoint law needs
    // *strict* ≤ — incomparable inputs return `false`, not silently
    // `true`. Use this helper everywhere and avoid `<=` (which panics
    // on `None` with some trait combos).
    fn le<T: PartialOrd>(a: &T, b: &T) -> bool {
        matches!(a.partial_cmp(b), Some(std::cmp::Ordering::Less | std::cmp::Ordering::Equal))
    }

    // Adjoint + closure + kernel + monotonicity, stated over
    // PartialOrd on both sides. Mirrors `doc/design.md §Testing`.
    macro_rules! float_conn_props {
        ($mod:ident, $conn:ident, $Rung:ident, $arb_src:ident, $arb_tgt:ident) => {
            mod $mod {
                use super::*;

                proptest! {
                    // Float-Conn shrinks on this domain are expensive:
                    // cap cases at 64 (4 conns × 7 props × 64 = 1 792)
                    // and shrink iters at 512 (default ~1M is ruinous
                    // and finds no bugs the first few hundred miss).
                    #![proptest_config(ProptestConfig {
                        cases: 64,
                        max_shrink_iters: 512,
                        .. ProptestConfig::default()
                    })]

                    // ceil(a) ≤ b ⟺ a ≤ inner(b)
                    #[test]
                    fn prop_adjoint_l(
                        a in $arb_src(),
                        b in $arb_tgt(),
                    ) {
                        let fa = $conn.ceil(a);
                        let gb = $conn.inner(b);
                        prop_assert_eq!(le(&fa, &b), le(&a, &gb));
                    }

                    // b ≤ floor(a) ⟺ inner(b) ≤ a
                    #[test]
                    fn prop_adjoint_r(
                        a in $arb_src(),
                        b in $arb_tgt(),
                    ) {
                        let ha = $conn.floor(a);
                        let gb = $conn.inner(b);
                        prop_assert_eq!(le(&b, &ha), le(&gb, &a));
                    }

                    // a ≤ inner(ceil(a))
                    #[test]
                    fn prop_closed_l(a in $arb_src()) {
                        let gfa = $conn.inner($conn.ceil(a));
                        prop_assert!(le(&a, &gfa));
                    }

                    // inner(floor(a)) ≤ a
                    #[test]
                    fn prop_closed_r(a in $arb_src()) {
                        let gha = $conn.inner($conn.floor(a));
                        prop_assert!(le(&gha, &a));
                    }

                    // ceil(inner(b)) ≤ b
                    #[test]
                    fn prop_kernel_l(b in $arb_tgt()) {
                        let fgb = $conn.ceil($conn.inner(b));
                        prop_assert!(le(&fgb, &b));
                    }

                    // b ≤ floor(inner(b))
                    #[test]
                    fn prop_kernel_r(b in $arb_tgt()) {
                        let hgb = $conn.floor($conn.inner(b));
                        prop_assert!(le(&b, &hgb));
                    }

                    // a1 ≤ a2 ⟹ ceil(a1) ≤ ceil(a2); floor likewise.
                    #[test]
                    fn prop_monotone(a1 in $arb_src(), a2 in $arb_src()) {
                        if le(&a1, &a2) {
                            prop_assert!(le(&$conn.ceil(a1), &$conn.ceil(a2)));
                            prop_assert!(le(&$conn.floor(a1), &$conn.floor(a2)));
                        }
                    }
                }

                // Type-check the rung binding so the macro input
                // doesn't silently diverge from the conn's actual
                // target.
                #[allow(dead_code)]
                fn _type_assert(x: Extended<$Rung>) -> Extended<$Rung> {
                    let _: Conn<_, Extended<$Rung>> = $conn;
                    x
                }
            }
        };
    }

    // F64F06 and F64F12 exercise the two structurally distinct cases:
    // PREC well below mantissa (F06) and PREC approaching mantissa (F12).
    // Other rungs share the adjoint-law machinery with one of these, so
    // the spot checks above are sufficient regression coverage.
    float_conn_props!(p_f64f06, F64F06, Micro, arb_float_ext_f64, arb_extended_micro);
    float_conn_props!(p_f64f12, F64F12, Pico,  arb_float_ext_f64, arb_extended_pico);
}
