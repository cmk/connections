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
use crate::conn::float::ExtendedFloat;
use crate::extended::Extended;
use crate::lattice::Ple;

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

// ExtendedFloat<f??> → Extended<Rung>. Lawful under `PartialOrd` on both
// sides.
//
// Source lattice (`ExtendedFloat<T>`):
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
        pub const $const_name: Conn<ExtendedFloat<$float>, Extended<$Rung>> = {
            const PREC: i64 = $prec;
            const PREC_F: f64 = PREC as f64;

            // `inner(Rung)` reinterpreted as f64 for the correction-loop
            // comparisons. The `as $float as f64` round-trip is a no-op
            // for f64 (the only shipped instantiation); it's kept so a
            // future F32Fxx instantiation compiles — but F32Fxx is
            // deferred precisely because that round-trip creates plateau
            // collapse classes that turn the correction loops into
            // O(plateau) walks. See §Deferred in plan-2026-04-24-01.
            fn inner_as_f64(c: i64) -> f64 {
                ((c as f64) / PREC_F) as $float as f64
            }

            fn ceil(x: ExtendedFloat<$float>) -> Extended<$Rung> {
                let f = match x {
                    ExtendedFloat::Bot => return Extended::NegInf,
                    ExtendedFloat::Top => return Extended::PosInf,
                    ExtendedFloat::Finite(v) => v,
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
                // `i64::MAX as f64` rounds to 2^63 (i64::MAX itself isn't
                // representable); the guard is therefore `scaled > 2^63`.
                // Values equal to 2^63 fall through to the correction
                // path, where `scaled.ceil() as i64` saturates to
                // `i64::MAX` — the right answer, just reached via the
                // loop rather than the early return.
                if scaled > i64::MAX as f64 {
                    return Extended::PosInf;
                }
                // `i64::MIN as f64` is exact (-2^63 is representable).
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
                // `c > i64::MIN + 1` (not `> i64::MIN`) because the
                // next iteration reads `inner_as_f64(c - 1)`. Any input
                // that would legitimately round to `c = i64::MIN` was
                // already caught by the `scaled < i64::MIN as f64`
                // early return above.
                while c > i64::MIN + 1 && inner_as_f64(c - 1) >= xf {
                    c -= 1;
                }
                Extended::Finite($Rung(c))
            }

            fn inner(b: Extended<$Rung>) -> ExtendedFloat<$float> {
                match b {
                    Extended::NegInf => ExtendedFloat::Bot,
                    Extended::PosInf => ExtendedFloat::Top,
                    Extended::Finite(r) => {
                        ExtendedFloat::Finite(((r.0 as f64) / PREC_F) as $float)
                    }
                }
            }

            fn floor(x: ExtendedFloat<$float>) -> Extended<$Rung> {
                let f = match x {
                    ExtendedFloat::Bot => return Extended::NegInf,
                    ExtendedFloat::Top => return Extended::PosInf,
                    ExtendedFloat::Finite(v) => v,
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
                // Saturation bounds mirror `ceil` — see that function
                // for why `i64::MAX as f64` is +2^63 (not exact) but
                // `i64::MIN as f64` is exact.
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
// `F64F06.ceil(ExtendedFloat::Finite(arg_f32 as f64))` — and get the
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
    use crate::property::arb::{
        extended_float_f64, extended_micro, extended_pico, fixed_coarse, fixed_fine,
        fixed_safe_fine,
    };
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

    // Each test is written for one Conn and one (Fine, Coarse) pair,
    // then expanded via macro across the 21 connections.

    macro_rules! props_for_pair {
        ($mod:ident, $conn:ident, $Fine:ident, $Coarse:ident, $prec:expr) => {
            mod $mod {
                use super::*;
                use $crate::property::laws;

                proptest! {
                    #[test]
                    fn roundtrip_ceil(c in fixed_coarse($prec)) {
                        prop_assert!(laws::conn_roundtrip_ceil(&$conn, $Coarse(c)));
                    }

                    #[test]
                    fn roundtrip_floor(c in fixed_coarse($prec)) {
                        prop_assert!(laws::conn_roundtrip_floor(&$conn, $Coarse(c)));
                    }

                    #[test]
                    fn monotone_l(x in fixed_fine($prec), y in fixed_fine($prec)) {
                        prop_assert!(laws::conn_monotone_l(&$conn, $Fine(x), $Fine(y)));
                    }

                    #[test]
                    fn floor_le_ceil(x in fixed_fine($prec)) {
                        let a = $Fine(x);
                        prop_assert!(laws::conn_floor_le_ceil(&$conn, a));
                        // Stronger: fixed-ladder ULP bound (ceil − floor ≤ 1).
                        prop_assert!(laws::conn_ulp_bound(&$conn, a, |b| b.0));
                    }

                    #[test]
                    fn galois_l(
                        x in fixed_fine($prec),
                        c in fixed_coarse($prec),
                    ) {
                        prop_assert!(laws::conn_galois_l(&$conn, $Fine(x), $Coarse(c)));
                    }

                    #[test]
                    fn galois_r(
                        x in fixed_fine($prec),
                        c in fixed_coarse($prec),
                    ) {
                        prop_assert!(laws::conn_galois_r(&$conn, $Fine(x), $Coarse(c)));
                    }

                    // Closure laws use fixed_safe_fine because the
                    // round-trip through inner multiplies by PREC and
                    // must fit i64; see fixed_safe_fine docs in
                    // crate::property::arb.
                    #[test]
                    fn closure_l(x in fixed_safe_fine($prec)) {
                        prop_assert!(laws::conn_closure_l(&$conn, $Fine(x)));
                    }

                    #[test]
                    fn closure_r(x in fixed_safe_fine($prec)) {
                        prop_assert!(laws::conn_closure_r(&$conn, $Fine(x)));
                    }

                    #[test]
                    fn idempotent(x in fixed_safe_fine($prec)) {
                        prop_assert!(laws::conn_idempotent(&$conn, $Fine(x)));
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

    // `compose!`-macro tests live in `crate::conn`'s test module,
    // alongside the macro itself. Composition is a property of the
    // `Conn` abstraction, not of any one ladder pair; keeping the
    // tests there preserves the invariant that `conn::fixed` only
    // owns laws that are specific to fixed-point connections.

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

    // ── ExtendedFloat<f??> → Extended<Rung> connections ─────────────────
    //
    // Strategies (`extended_float_f64`, `extended_micro`,
    // `extended_pico`) live in `crate::property::arb`; see the doc
    // there for the `arb_f64_bounded` rationale on why a bounded
    // range beats `any::<f64>()` for these saturation-prone inputs.

    // Spot checks with exactly-representable f64 values.
    #[test]
    fn float_conn_spot() {
        let half = ExtendedFloat::Finite(0.5_f64);
        assert_eq!(F64F03.ceil(half), Extended::Finite(Milli(500)));
        assert_eq!(F64F03.floor(half), Extended::Finite(Milli(500)));
        assert_eq!(F64F06.ceil(half), Extended::Finite(Micro(500_000)));
        assert_eq!(F64F12.ceil(ExtendedFloat::Finite(0.25_f64)),
                   Extended::Finite(Pico(250_000_000_000)));

        let one_and_half = ExtendedFloat::Finite(1.5_f64);
        assert_eq!(F64F06.ceil(one_and_half), Extended::Finite(Micro(1_500_000)));
        assert_eq!(F64F06.floor(one_and_half), Extended::Finite(Micro(1_500_000)));
        assert_eq!(F64F06.inner(Extended::Finite(Micro(1_500_000))),
                   ExtendedFloat::Finite(1.5_f64));

        // Saturation map (matches the table in the macro doc comment).
        assert_eq!(F64F06.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F64F06.floor(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F64F06.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F64F06.floor(ExtendedFloat::Top), Extended::PosInf);

        let nan: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::NAN);
        assert_eq!(F64F06.ceil(nan), Extended::PosInf);
        assert_eq!(F64F06.floor(nan), Extended::NegInf);

        let pos_inf: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::INFINITY);
        assert_eq!(F64F06.ceil(pos_inf), Extended::PosInf);
        assert_eq!(F64F06.floor(pos_inf), Extended::Finite(Micro(i64::MAX)));

        let neg_inf: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::NEG_INFINITY);
        assert_eq!(F64F06.ceil(neg_inf), Extended::Finite(Micro(i64::MIN)));
        assert_eq!(F64F06.floor(neg_inf), Extended::NegInf);

        // Inner maps target ±Inf to ExtendedFloat's Top/Bot (synthetic
        // bounds outside the float range), NOT to Finite(±f64::INFINITY).
        assert_eq!(F64F06.inner(Extended::PosInf), ExtendedFloat::Top);
        assert_eq!(F64F06.inner(Extended::NegInf), ExtendedFloat::Bot);
    }

    // F64F00 (PREC=1) is the identity-like regime — `inner(c) = c as f64`
    // with no division, so the correction loop is vacuous and saturation
    // is the only behaviour that can go wrong. Covered separately because
    // the proptest battery above exercises F64F06 and F64F12 only.
    #[test]
    fn f64f00_saturation() {
        assert_eq!(F64F00.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F64F00.floor(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F64F00.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F64F00.floor(ExtendedFloat::Top), Extended::PosInf);

        let nan: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::NAN);
        assert_eq!(F64F00.ceil(nan), Extended::PosInf);
        assert_eq!(F64F00.floor(nan), Extended::NegInf);

        let pos_inf: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::INFINITY);
        assert_eq!(F64F00.ceil(pos_inf), Extended::PosInf);
        assert_eq!(F64F00.floor(pos_inf), Extended::Finite(Uni(i64::MAX)));

        let neg_inf: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::NEG_INFINITY);
        assert_eq!(F64F00.ceil(neg_inf), Extended::Finite(Uni(i64::MIN)));
        assert_eq!(F64F00.floor(neg_inf), Extended::NegInf);

        // Identity on exact integers.
        assert_eq!(F64F00.ceil(ExtendedFloat::Finite(42.0)), Extended::Finite(Uni(42)));
        assert_eq!(F64F00.floor(ExtendedFloat::Finite(42.0)), Extended::Finite(Uni(42)));
        assert_eq!(F64F00.ceil(ExtendedFloat::Finite(-42.0)), Extended::Finite(Uni(-42)));
        assert_eq!(F64F00.floor(ExtendedFloat::Finite(-42.0)), Extended::Finite(Uni(-42)));

        // Non-integer: ceil up, floor down.
        assert_eq!(F64F00.ceil(ExtendedFloat::Finite(0.25)), Extended::Finite(Uni(1)));
        assert_eq!(F64F00.floor(ExtendedFloat::Finite(0.25)), Extended::Finite(Uni(0)));
        assert_eq!(F64F00.ceil(ExtendedFloat::Finite(-0.25)), Extended::Finite(Uni(0)));
        assert_eq!(F64F00.floor(ExtendedFloat::Finite(-0.25)), Extended::Finite(Uni(-1)));

        // Very large finite: saturating, into Finite at the ceil/floor
        // boundary rather than flowing to ±Inf on the target.
        let huge = ExtendedFloat::Finite(2.0_f64.powi(70));  // > i64::MAX
        assert_eq!(F64F00.ceil(huge), Extended::PosInf);
        assert_eq!(F64F00.floor(huge), Extended::Finite(Uni(i64::MAX)));

        let tiny = ExtendedFloat::Finite(-2.0_f64.powi(70));  // < i64::MIN
        assert_eq!(F64F00.ceil(tiny), Extended::Finite(Uni(i64::MIN)));
        assert_eq!(F64F00.floor(tiny), Extended::NegInf);
    }

    // Adjoint + closure + kernel + monotonicity, stated over
    // PartialOrd on both sides. Mirrors `doc/design.md §Testing`.
    macro_rules! float_conn_props {
        ($mod:ident, $conn:ident, $Rung:ident, $arb_src:ident, $arb_tgt:ident) => {
            mod $mod {
                use super::*;
                use $crate::property::laws;

                proptest! {
                    // Float-Conn shrinks on this domain are expensive:
                    // cap cases at 64 and shrink iters at 512 (default
                    // ~1M is ruinous and finds no bugs the first few
                    // hundred miss).
                    #![proptest_config(ProptestConfig {
                        cases: 64,
                        max_shrink_iters: 512,
                        .. ProptestConfig::default()
                    })]

                    #[test]
                    fn galois_l(a in $arb_src(), b in $arb_tgt()) {
                        prop_assert!(laws::conn_galois_l(&$conn, a, b));
                    }

                    #[test]
                    fn galois_r(a in $arb_src(), b in $arb_tgt()) {
                        prop_assert!(laws::conn_galois_r(&$conn, a, b));
                    }

                    #[test]
                    fn closure_l(a in $arb_src()) {
                        prop_assert!(laws::conn_closure_l(&$conn, a));
                    }

                    #[test]
                    fn closure_r(a in $arb_src()) {
                        prop_assert!(laws::conn_closure_r(&$conn, a));
                    }

                    #[test]
                    fn kernel_l(b in $arb_tgt()) {
                        prop_assert!(laws::conn_kernel_l(&$conn, b));
                    }

                    #[test]
                    fn kernel_r(b in $arb_tgt()) {
                        prop_assert!(laws::conn_kernel_r(&$conn, b));
                    }

                    #[test]
                    fn monotone_l(a1 in $arb_src(), a2 in $arb_src()) {
                        prop_assert!(laws::conn_monotone_l(&$conn, a1, a2));
                    }

                    // Idempotence: inner∘ceil is idempotent on its
                    // image. ExtendedFloat<f64>'s PartialEq treats
                    // Finite(NaN) == Finite(NaN) as true, so the
                    // Eq-bound `conn_idempotent` predicate is the
                    // right comparison here.
                    #[test]
                    fn idempotent(a in $arb_src()) {
                        prop_assert!(laws::conn_idempotent(&$conn, a));
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
    float_conn_props!(p_f64f06, F64F06, Micro, extended_float_f64, extended_micro);
    float_conn_props!(p_f64f12, F64F12, Pico,  extended_float_f64, extended_pico);
}
