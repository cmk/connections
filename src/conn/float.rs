//! `ExtendedFloat<T>` extends an IEEE float type with synthetic `Bot` and
//! `Top` elements outside the float range, recovering the N5 lattice
//! structure the Galois-connection machinery requires.
//!
//! Rust's built-in float `PartialOrd` is a partial order: NaN is
//! incomparable with every value including itself, and there are no
//! canonical top/bottom elements. `ExtendedFloat` addresses both:
//!
//! - `Bot ≤ x` and `x ≤ Top` for every `x` (including `NaN`, `±∞`).
//! - `Extend(NaN)` is reflexive: `Extend(NaN) == Extend(NaN)` and
//!   `Extend(NaN).partial_cmp(&Extend(NaN)) == Some(Equal)`.
//! - `Extend(NaN)` remains incomparable with every other `Extend(_)`
//!   value (including `±∞`) — that comparison returns `None`.
//!
//! The N5 lattice (`-∞ ≤ NaN ≤ +∞`, NaN incomparable with finites) is
//! obtained from this shape: the synthetic `Bot` / `Top` form the
//! lattice's bottom/top; NaN's reflexivity closes the preorder; its
//! incomparability with finites is inherited unchanged from
//! `PartialOrd` on the wrapped `T`.
//!
//! Per-source-tier Conns live in submodules:
//!
//! - [`f64`] — Conns originating at [`F064`] (currently `F064F032`).
//! - [`f32`] — Conns originating at [`F032`] (currently `F032F016`).
//!
//! Cross-tier float→decimal Conns (`F064FD00`..`F064FD12`, …) live with
//! the FD ladder in [`super::fixed::decimal`].

pub mod f32;
pub mod f64;

use std::cmp::Ordering;

/// Three-element extension of a (possibly partial) order:
/// `Bot < Extend(_) < Top`.
///
/// The wrapped variant is named `Extend`, not `Finite`, because for
/// IEEE floats the wrapped value can be `NaN` or `±∞` — neither of
/// which is finite. The variant name reflects the lattice-theoretic
/// role (the *extension* slot between `Bot` and `Top`), not a numeric
/// property of the inhabitant. Sister type [`crate::extended::Extended`]
/// keeps `Finite` since its wrapped values really are finite.
#[derive(Copy, Clone, Debug)]
pub enum ExtendedFloat<T> {
    Bot,
    Extend(T),
    Top,
}

macro_rules! impl_float_ext {
    ($T:ty) => {
        impl PartialEq for ExtendedFloat<$T> {
            fn eq(&self, other: &Self) -> bool {
                use ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => true,
                    (Extend(a), Extend(b)) => {
                        if a.is_nan() && b.is_nan() {
                            true
                        } else {
                            a == b
                        }
                    }
                    _ => false,
                }
            }
        }

        impl PartialOrd for ExtendedFloat<$T> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                use ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => Some(Ordering::Equal),
                    (Bot, _) => Some(Ordering::Less),
                    (_, Bot) => Some(Ordering::Greater),
                    (_, Top) => Some(Ordering::Less),
                    (Top, _) => Some(Ordering::Greater),
                    (Extend(a), Extend(b)) => {
                        if a.is_nan() && b.is_nan() {
                            Some(Ordering::Equal)
                        } else {
                            a.partial_cmp(b)
                        }
                    }
                }
            }
        }

        // The `PartialEq` above is reflexive (`Extend(NaN) == Extend(NaN)`
        // is true), so `Eq`'s contract is satisfied. Adding the marker
        // lets `ExtendedFloat<$T>` flow through any `T: Eq + PartialOrd`
        // bound — which is the lawful framework the Galois-connection
        // laws use.
        impl Eq for ExtendedFloat<$T> {}
    };
}

impl_float_ext!(f32);
impl_float_ext!(f64);
impl_float_ext!(half::f16);
impl_float_ext!(half::bf16);

/// IEEE binary16 (half-precision) wrapped under the N5 lattice.
///
/// **Software-emulated** via the [`half`](https://docs.rs/half) crate;
/// when native `f16` stabilizes the inner type swaps without changing
/// `F016`'s public surface or any `F<src>F016` Conn name.
pub type F016 = ExtendedFloat<half::f16>;

/// IEEE binary32 wrapped under the N5 lattice.
pub type F032 = ExtendedFloat<f32>;

/// IEEE binary64 wrapped under the N5 lattice.
pub type F064 = ExtendedFloat<f64>;

/// Google bfloat16 (Brain Floating Point) wrapped under the N5 lattice.
///
/// **Software-emulated** via the [`half`](https://docs.rs/half) crate.
/// `bf16` shares `f32`'s 8-bit exponent (same dynamic range) but has
/// only a 7-bit mantissa — preferred over IEEE `f16` for ML
/// workloads where range matters more than precision. There is no
/// stable Rust native bf16 today.
pub type B016 = ExtendedFloat<half::bf16>;

// ── ULP machinery ──────────────────────────────────────────────────

/// Shift a float by `n` ULPs (units of least precision) in the
/// sign-magnitude total order.
///
/// NaN maps to +∞ for positive shifts and -∞ for negative shifts.
/// ±∞ are clamped (shifting past ±∞ stays at ±∞).
pub(crate) fn shift32(n: i32, x: f32) -> f32 {
    if x.is_nan() {
        return match n.signum() {
            -1 => f32::NEG_INFINITY,
            1 => f32::INFINITY,
            _ => f32::NAN,
        };
    }
    let i = float_to_int32(x);
    int32_to_float(clamp32(i.saturating_add(n)))
}

/// Convert f32 to a sign-magnitude integer where the total order on
/// integers matches the total order on floats (excluding NaN).
///
/// Maps: -∞ → INT_MIN+1, -0 → -1, +0 → 0, +∞ → INT_MAX-1 (approx)
fn float_to_int32(x: f32) -> i32 {
    signed32(x.to_bits())
}

fn int32_to_float(i: i32) -> f32 {
    f32::from_bits(unsigned32(i))
}

/// Word32 (IEEE bit pattern) → sign-magnitude Int32.
///
/// Maps the float bit-space onto integers so that the integer order
/// matches the float total order (excluding NaN):
///   +0 → 0, +inf → 2139095040, -0 → -1, -inf → -2139095041
fn signed32(x: u32) -> i32 {
    if x < 0x80000000 {
        x as i32
    } else {
        // Haskell: fromIntegral (maxBound @Word32 - (x - 0x80000000))
        (u32::MAX - (x - 0x80000000)) as i32
    }
}

/// Sign-magnitude Int32 → Word32 (IEEE bit pattern).
fn unsigned32(x: i32) -> u32 {
    if x >= 0 {
        x as u32
    } else {
        // Haskell: 0x80000000 + (maxBound @Word32 - fromIntegral x)
        0x80000000u32.wrapping_add(u32::MAX - (x as u32))
    }
}

/// Clamp between the int representations of -∞ and +∞.
fn clamp32(x: i32) -> i32 {
    // f32::INFINITY.to_bits()  = 0x7F800000 → signed32 = 2139095040
    // f32::NEG_INFINITY bits   = 0xFF800000 → signed32 = -2139095041
    x.clamp(-2139095041, 2139095040)
}

// ── 16-bit ULP machinery (shared between half::f16 and half::bf16) ──
//
// Both half-precision types are u16-backed sign-magnitude with the
// sign at the MSB, so the bit-pattern → total-order int mapping
// (`signed16` / `unsigned16`) is identical. Only the ±∞ clamp values
// differ — `clamp16_f16` vs `clamp16_bf16` — because IEEE binary16
// and bfloat16 have different exponent fields.

/// Word16 (sign-magnitude bit pattern) → sign-magnitude i32.
///
/// Maps the 16-bit float bit-space onto integers so that integer
/// order matches the float total order (excluding NaN):
///   +0 → 0, +inf-bits → small positive, -0 → -1, -inf-bits → large negative.
#[allow(dead_code)] // exercised by shift16_* helpers + their tests
pub(crate) fn signed16(x: u16) -> i32 {
    if x < 0x8000 {
        x as i32
    } else {
        // Mirror signed32's Haskell-style mapping at 16-bit width.
        // u16::MAX - (x - 0x8000) maps the negative half symmetrically;
        // simpler equivalent: 0x7FFF - x as i32.
        0x7FFF_i32 - (x as i32)
    }
}

/// Sign-magnitude i32 → Word16 (bit pattern).
#[allow(dead_code)] // exercised by shift16_* helpers + their tests
pub(crate) fn unsigned16(i: i32) -> u16 {
    if i >= 0 {
        i as u16
    } else {
        (0x7FFF_i32 - i) as u16
    }
}

/// Clamp between the i32 representations of f16's ±∞.
#[allow(dead_code)]
pub(crate) fn clamp16_f16(x: i32) -> i32 {
    // half::f16::INFINITY.to_bits() = 0x7C00 → signed16 = 31744
    // half::f16::NEG_INFINITY bits  = 0xFC00 → signed16 = -31745
    x.clamp(-31745, 31744)
}

/// Clamp between the i32 representations of bf16's ±∞.
#[allow(dead_code)]
pub(crate) fn clamp16_bf16(x: i32) -> i32 {
    // half::bf16::INFINITY.to_bits() = 0x7F80 → signed16 = 32640
    // half::bf16::NEG_INFINITY bits  = 0xFF80 → signed16 = -32641
    x.clamp(-32641, 32640)
}

/// Shift a [`half::f16`] by `n` ULPs in the sign-magnitude total order.
///
/// NaN maps to ±∞ for non-zero shifts (matches `shift32`); ±∞ are
/// clamped (shifting past stays at ±∞).
#[allow(dead_code)] // first consumer lands with F032F016 / F064F016
pub(crate) fn shift16_f16(n: i32, x: half::f16) -> half::f16 {
    if x.is_nan() {
        return match n.signum() {
            -1 => half::f16::NEG_INFINITY,
            1 => half::f16::INFINITY,
            _ => half::f16::NAN,
        };
    }
    let i = signed16(x.to_bits());
    half::f16::from_bits(unsigned16(clamp16_f16(i.saturating_add(n))))
}

/// Shift a [`half::bf16`] by `n` ULPs in the sign-magnitude total order.
#[allow(dead_code)] // first consumer lands with F032B016 / F064B016
pub(crate) fn shift16_bf16(n: i32, x: half::bf16) -> half::bf16 {
    if x.is_nan() {
        return match n.signum() {
            -1 => half::bf16::NEG_INFINITY,
            1 => half::bf16::INFINITY,
            _ => half::bf16::NAN,
        };
    }
    let i = signed16(x.to_bits());
    half::bf16::from_bits(unsigned16(clamp16_bf16(i.saturating_add(n))))
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── ULP sanity ─────────────────────────────────────────────────

    #[test]
    fn shift32_from_zero() {
        let z = shift32(1, 0.0);
        assert!(z > 0.0);
        assert_eq!(z, f32::from_bits(1));
    }

    #[test]
    fn shift32_nan_to_inf() {
        assert_eq!(shift32(1, f32::NAN), f32::INFINITY);
        assert_eq!(shift32(-1, f32::NAN), f32::NEG_INFINITY);
        assert!(shift32(0, f32::NAN).is_nan());
    }

    #[test]
    fn shift32_inf_clamped() {
        assert_eq!(shift32(1, f32::INFINITY), f32::INFINITY);
        assert_eq!(shift32(-1, f32::NEG_INFINITY), f32::NEG_INFINITY);
    }

    // ── 16-bit ULP machinery sanity ────────────────────────────────

    #[test]
    fn signed16_round_trip() {
        // Sweep every u16 → i32 → u16 must be the identity.
        for x in 0u16..=u16::MAX {
            assert_eq!(unsigned16(signed16(x)), x, "round-trip failed at {x:#x}");
        }
    }

    #[test]
    fn signed16_total_order_matches_float_order_f16() {
        // For non-NaN f16 values, signed16(a.to_bits()) <= signed16(b.to_bits())
        // iff a.total_cmp(&b) is Less or Equal.
        let samples = [
            half::f16::NEG_INFINITY,
            half::f16::MIN,
            half::f16::from_f32(-1.0),
            half::f16::from_f32(-0.5),
            half::f16::NEG_ZERO,
            half::f16::ZERO,
            half::f16::MIN_POSITIVE,
            half::f16::from_f32(0.5),
            half::f16::ONE,
            half::f16::MAX,
            half::f16::INFINITY,
        ];
        for w in samples.windows(2) {
            let (a, b) = (w[0], w[1]);
            let (ia, ib) = (signed16(a.to_bits()), signed16(b.to_bits()));
            assert!(
                ia < ib,
                "signed16 order broken: {a:?} ({ia}) </ {b:?} ({ib})"
            );
        }
    }

    #[test]
    fn shift16_f16_from_zero() {
        let z = shift16_f16(1, half::f16::ZERO);
        assert!(z > half::f16::ZERO);
        assert_eq!(z, half::f16::from_bits(1));
    }

    #[test]
    fn shift16_f16_nan_to_inf() {
        assert_eq!(shift16_f16(1, half::f16::NAN), half::f16::INFINITY);
        assert_eq!(shift16_f16(-1, half::f16::NAN), half::f16::NEG_INFINITY);
        assert!(shift16_f16(0, half::f16::NAN).is_nan());
    }

    #[test]
    fn shift16_f16_inf_clamped() {
        assert_eq!(shift16_f16(1, half::f16::INFINITY), half::f16::INFINITY);
        assert_eq!(
            shift16_f16(-1, half::f16::NEG_INFINITY),
            half::f16::NEG_INFINITY
        );
    }

    #[test]
    fn shift16_bf16_from_zero() {
        let z = shift16_bf16(1, half::bf16::ZERO);
        assert!(z > half::bf16::ZERO);
        assert_eq!(z, half::bf16::from_bits(1));
    }

    #[test]
    fn shift16_bf16_nan_to_inf() {
        assert_eq!(shift16_bf16(1, half::bf16::NAN), half::bf16::INFINITY);
        assert_eq!(shift16_bf16(-1, half::bf16::NAN), half::bf16::NEG_INFINITY);
        assert!(shift16_bf16(0, half::bf16::NAN).is_nan());
    }

    #[test]
    fn shift16_bf16_inf_clamped() {
        assert_eq!(shift16_bf16(1, half::bf16::INFINITY), half::bf16::INFINITY);
        assert_eq!(
            shift16_bf16(-1, half::bf16::NEG_INFINITY),
            half::bf16::NEG_INFINITY
        );
    }

    #[test]
    fn clamp16_constants_match_inf_bits() {
        assert_eq!(signed16(half::f16::INFINITY.to_bits()), 31744);
        assert_eq!(signed16(half::f16::NEG_INFINITY.to_bits()), -31745);
        assert_eq!(signed16(half::bf16::INFINITY.to_bits()), 32640);
        assert_eq!(signed16(half::bf16::NEG_INFINITY.to_bits()), -32641);
    }

    // ── ExtendedFloat tests (folded in from former src/float_ext.rs) ────

    #[test]
    fn bot_below_everything_f64() {
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::Extend(0.0));
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::Extend(f64::NEG_INFINITY));
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::Extend(f64::NAN));
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::<f64>::Top);
    }

    #[test]
    fn top_above_everything_f64() {
        assert!(ExtendedFloat::Extend(0.0_f64) < ExtendedFloat::<f64>::Top);
        assert!(ExtendedFloat::Extend(f64::INFINITY) < ExtendedFloat::<f64>::Top);
        assert!(ExtendedFloat::Extend(f64::NAN) < ExtendedFloat::<f64>::Top);
    }

    #[test]
    fn nan_reflexive_f64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(n, ExtendedFloat::Extend(f64::NAN));
        assert_eq!(
            n.partial_cmp(&ExtendedFloat::Extend(f64::NAN)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn nan_incomparable_with_finite_f64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::NAN);
        assert!(n.partial_cmp(&ExtendedFloat::Extend(1.0)).is_none());
        assert!(ExtendedFloat::Extend(1.0_f64).partial_cmp(&n).is_none());
    }

    #[test]
    fn nan_incomparable_with_infinity_f64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::NAN);
        let i: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::INFINITY);
        assert!(n.partial_cmp(&i).is_none());
        assert!(i.partial_cmp(&n).is_none());
    }

    #[test]
    fn standard_order_preserved_f64() {
        assert!(ExtendedFloat::Extend(1.0_f64) < ExtendedFloat::Extend(2.0));
        assert!(ExtendedFloat::Extend(f64::NEG_INFINITY) < ExtendedFloat::Extend(0.0_f64));
        assert!(ExtendedFloat::Extend(0.0_f64) < ExtendedFloat::Extend(f64::INFINITY));
    }

    #[test]
    fn f32_same_shape() {
        let n: ExtendedFloat<f32> = ExtendedFloat::Extend(f32::NAN);
        assert_eq!(n, ExtendedFloat::Extend(f32::NAN));
        assert!(ExtendedFloat::<f32>::Bot < n);
        assert!(n < ExtendedFloat::<f32>::Top);
        assert!(n.partial_cmp(&ExtendedFloat::Extend(1.0_f32)).is_none());
    }

    #[test]
    fn f16_same_shape() {
        let n: ExtendedFloat<half::f16> = ExtendedFloat::Extend(half::f16::NAN);
        assert_eq!(n, ExtendedFloat::Extend(half::f16::NAN));
        assert!(ExtendedFloat::<half::f16>::Bot < n);
        assert!(n < ExtendedFloat::<half::f16>::Top);
        assert!(
            n.partial_cmp(&ExtendedFloat::Extend(half::f16::ONE))
                .is_none()
        );
    }

    #[test]
    fn bf16_same_shape() {
        let n: ExtendedFloat<half::bf16> = ExtendedFloat::Extend(half::bf16::NAN);
        assert_eq!(n, ExtendedFloat::Extend(half::bf16::NAN));
        assert!(ExtendedFloat::<half::bf16>::Bot < n);
        assert!(n < ExtendedFloat::<half::bf16>::Top);
        assert!(
            n.partial_cmp(&ExtendedFloat::Extend(half::bf16::ONE))
                .is_none()
        );
    }
}
