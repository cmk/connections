//! IEEE float Conns built on [`N5<T>`], a transparent wrapper that gives
//! IEEE floats the N5 preorder used by the Galois-connection machinery.
//!
//! ## Constants
//!
//! Peer float Conns live with their source side after semantic
//! specificity is considered:
//!
//! | Const          | Conn                                  | Module                 |
//! |----------------|---------------------------------------|------------------------|
//! | `F064F032`     | `Conn<F064, F032>` (lossy narrowing)  | [`crate::core::f064`]  |
//! | `F064F016`     | `Conn<F064, F016>` (`f16` feature)    | `crate::core::f064`    |
//! | `F032F016`     | `Conn<F032, F016>` (`f16` feature)    | `crate::core::f032`    |
//!
//! ## Example
//!
//! ```rust
//! use connections::conn::{ConnL, ConnR};
//! use connections::core::f064::F064F032;
//! use connections::float::F064;
//!
//! // f64 → f32 narrowing rounds in two directions.
//! let pi64 = F064::new(std::f64::consts::PI);
//! let lo = F064F032.floor(pi64);   // largest f32 ≤ π
//! let hi = F064F032.ceil(pi64);    // smallest f32 ≥ π
//! assert!(lo != hi);               // π is not exactly representable in f32
//! ```
//!
//! ## Why N5?
//!
//! Rust's built-in float `PartialOrd` is a partial order: NaN is
//! incomparable with every value including itself. `N5` keeps the same
//! underlying IEEE value and changes only the comparison relation:
//!
//! - `N5(NaN)` is reflexive.
//! - `N5(-∞) ≤ N5(NaN) ≤ N5(+∞)`.
//! - `N5(NaN)` remains incomparable with finite values.
//!
//! This is the five-element modular lattice pattern in the IEEE setting:
//! see the [N5 examples][n5].
//!
//! [n5]: https://en.wikipedia.org/wiki/Modular_lattice#Examples

// Per-IEEE-width Conn modules moved to `crate::core::{f016,f032,f064}`
// in Plan 26. This module retains the `N5<T>` wrapper type and the
// float-only infrastructure (ULP machinery, `BitsToF64Rd`,
// `RoundDownFromF64`, `def_walk_helpers!`, `float_ext_int!` macros)
// that the relocated Conn submodules depend on.

use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

/// IEEE float value ordered by the N5 preorder.
///
/// `N5<T>` is a transparent newtype over the IEEE value. It does not add
/// synthetic top or bottom values: `T::NEG_INFINITY` and `T::INFINITY`
/// are the bottom and top of the float side. The only non-standard order
/// rule is the N5 placement of NaN:
///
/// - `NaN == NaN` for the wrapper's `Eq` relation.
/// - `-∞ < NaN < +∞`.
/// - `NaN` is incomparable with finite values.
///
/// This is the N5 lattice shape described in the
/// [modular lattice examples][n5].
///
/// [n5]: https://en.wikipedia.org/wiki/Modular_lattice#Examples
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Default)]
pub struct N5<T>(pub T);

impl<T> N5<T> {
    /// Wrap an IEEE float under the N5 preorder.
    #[inline]
    pub const fn new(value: T) -> Self {
        Self(value)
    }

    /// Unwrap the underlying IEEE float.
    #[inline]
    pub fn into_inner(self) -> T {
        self.0
    }

    /// Map the underlying value, preserving the N5 wrapper.
    #[inline]
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> N5<U> {
        N5(f(self.0))
    }
}

macro_rules! impl_float_ext {
    ($T:ty) => {
        impl PartialEq for $crate::float::N5<$T> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                let a = self.0;
                let b = other.0;
                if a.is_nan() && b.is_nan() {
                    true
                } else {
                    a == b
                }
            }
        }

        impl PartialOrd for $crate::float::N5<$T> {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<::core::cmp::Ordering> {
                let a = self.0;
                let b = other.0;
                if a.is_nan() && b.is_nan() {
                    Some(::core::cmp::Ordering::Equal)
                } else if a.is_nan() {
                    if b == <$T>::INFINITY {
                        Some(::core::cmp::Ordering::Less)
                    } else if b == <$T>::NEG_INFINITY {
                        Some(::core::cmp::Ordering::Greater)
                    } else {
                        None
                    }
                } else if b.is_nan() {
                    if a == <$T>::NEG_INFINITY {
                        Some(::core::cmp::Ordering::Less)
                    } else if a == <$T>::INFINITY {
                        Some(::core::cmp::Ordering::Greater)
                    } else {
                        None
                    }
                } else {
                    a.partial_cmp(&b)
                }
            }
        }

        // The wrapper's `PartialEq` is reflexive for NaN, so `Eq`'s
        // contract is satisfied.
        impl Eq for $crate::float::N5<$T> {}
    };
}

pub(crate) use impl_float_ext;

impl_float_ext!(f32);
impl_float_ext!(f64);

// ── `?`-support (nightly `try_trait` feature) ──────────────────────
//
// `N5` has no failure branch. `?` extracts the wrapped IEEE value and
// never short-circuits; `NaN` and infinities are ordinary payloads.

/// Residual type for [`N5`]'s infallible `Try` implementation.
#[cfg(feature = "try_trait")]
#[derive(Copy, Clone, Debug)]
pub enum N5Residual {}

/// `?` extracts the wrapped IEEE value. Requires the nightly
/// `try_trait` feature.
#[cfg(feature = "try_trait")]
impl<T> core::ops::Try for N5<T> {
    type Output = T;
    type Residual = N5Residual;

    #[inline]
    fn from_output(output: Self::Output) -> Self {
        N5(output)
    }

    #[inline]
    fn branch(self) -> core::ops::ControlFlow<Self::Residual, Self::Output> {
        core::ops::ControlFlow::Continue(self.0)
    }
}

#[cfg(feature = "try_trait")]
impl<T> core::ops::FromResidual<N5Residual> for N5<T> {
    #[inline]
    fn from_residual(residual: N5Residual) -> Self {
        match residual {}
    }
}

#[cfg(feature = "try_trait")]
impl<O> core::ops::Residual<O> for N5Residual {
    type TryType = N5<O>;
}

// ── Numeric impls for `N5<f32 | f64>`.
//
// Arithmetic is ordinary IEEE arithmetic on the wrapped value. N5 only
// changes equality/order so the Conn laws can quantify over NaN.

macro_rules! impl_float_arith {
    ($T:ident) => {
        impl Add for N5<$T> {
            type Output = Self;
            #[inline]
            fn add(self, other: Self) -> Self {
                N5(self.0 + other.0)
            }
        }

        impl Sub for N5<$T> {
            type Output = Self;
            #[inline]
            fn sub(self, other: Self) -> Self {
                N5(self.0 - other.0)
            }
        }

        impl Mul for N5<$T> {
            type Output = Self;
            #[inline]
            fn mul(self, other: Self) -> Self {
                N5(self.0 * other.0)
            }
        }

        impl Div for N5<$T> {
            type Output = Self;
            #[inline]
            fn div(self, other: Self) -> Self {
                N5(self.0 / other.0)
            }
        }

        impl Rem for N5<$T> {
            type Output = Self;
            #[inline]
            fn rem(self, other: Self) -> Self {
                N5(self.0 % other.0)
            }
        }

        impl Neg for N5<$T> {
            type Output = Self;
            #[inline]
            fn neg(self) -> Self {
                N5(-self.0)
            }
        }

        impl AddAssign for N5<$T> {
            #[inline]
            fn add_assign(&mut self, other: Self) {
                *self = *self + other;
            }
        }
        impl SubAssign for N5<$T> {
            #[inline]
            fn sub_assign(&mut self, other: Self) {
                *self = *self - other;
            }
        }
        impl MulAssign for N5<$T> {
            #[inline]
            fn mul_assign(&mut self, other: Self) {
                *self = *self * other;
            }
        }
        impl DivAssign for N5<$T> {
            #[inline]
            fn div_assign(&mut self, other: Self) {
                *self = *self / other;
            }
        }
        impl RemAssign for N5<$T> {
            #[inline]
            fn rem_assign(&mut self, other: Self) {
                *self = *self % other;
            }
        }

        impl From<u8> for N5<$T> {
            #[inline]
            fn from(n: u8) -> Self {
                N5(<$T>::from(n))
            }
        }

        impl From<i8> for N5<$T> {
            #[inline]
            fn from(n: i8) -> Self {
                N5(<$T>::from(n))
            }
        }

        impl From<i16> for N5<$T> {
            #[inline]
            fn from(n: i16) -> Self {
                N5(<$T>::from(n))
            }
        }

        impl From<u16> for N5<$T> {
            #[inline]
            fn from(n: u16) -> Self {
                N5(<$T>::from(n))
            }
        }

        impl From<$T> for N5<$T> {
            #[inline]
            fn from(v: $T) -> Self {
                N5(v)
            }
        }

        impl N5<$T> {
            pub const PI: Self = N5(::core::$T::consts::PI);
            pub const TAU: Self = N5(::core::$T::consts::TAU);
            pub const E: Self = N5(::core::$T::consts::E);
            pub const FRAC_PI_2: Self = N5(::core::$T::consts::FRAC_PI_2);
            pub const NAN: Self = N5(<$T>::NAN);
            pub const INFINITY: Self = N5(<$T>::INFINITY);
            pub const NEG_INFINITY: Self = N5(<$T>::NEG_INFINITY);
            pub const ZERO: Self = N5(0.0);
            pub const ONE: Self = N5(1.0);

            /// `true` iff the wrapped IEEE value is NaN.
            #[inline]
            pub fn is_nan(self) -> bool {
                self.0.is_nan()
            }

            /// `true` iff the wrapped IEEE value is finite.
            #[inline]
            pub fn is_finite(self) -> bool {
                self.0.is_finite()
            }

            /// `true` iff the wrapped IEEE value is infinite.
            #[inline]
            pub fn is_infinite(self) -> bool {
                self.0.is_infinite()
            }

            // ── Transcendentals + utilities ───────────────────────────

            #[inline]
            pub fn abs(self) -> Self {
                N5(self.0.abs())
            }

            #[inline]
            pub fn signum(self) -> Self {
                N5(self.0.signum())
            }

            #[inline]
            pub fn recip(self) -> Self {
                N5(self.0.recip())
            }

            #[inline]
            pub fn sqrt(self) -> Self {
                N5(self.0.sqrt())
            }

            #[inline]
            pub fn cbrt(self) -> Self {
                N5(self.0.cbrt())
            }

            #[inline]
            pub fn sin(self) -> Self {
                N5(self.0.sin())
            }

            #[inline]
            pub fn cos(self) -> Self {
                N5(self.0.cos())
            }

            #[inline]
            pub fn tan(self) -> Self {
                N5(self.0.tan())
            }

            #[inline]
            pub fn asin(self) -> Self {
                N5(self.0.asin())
            }

            #[inline]
            pub fn acos(self) -> Self {
                N5(self.0.acos())
            }

            #[inline]
            pub fn atan(self) -> Self {
                N5(self.0.atan())
            }

            /// `atan2(y, x)`.
            #[inline]
            pub fn atan2(self, other: Self) -> Self {
                N5(self.0.atan2(other.0))
            }

            #[inline]
            pub fn exp(self) -> Self {
                N5(self.0.exp())
            }

            #[inline]
            pub fn exp2(self) -> Self {
                N5(self.0.exp2())
            }

            #[inline]
            pub fn ln(self) -> Self {
                N5(self.0.ln())
            }

            #[inline]
            pub fn log2(self) -> Self {
                N5(self.0.log2())
            }

            #[inline]
            pub fn log10(self) -> Self {
                N5(self.0.log10())
            }

            /// Integer power.
            #[inline]
            pub fn powi(self, n: i32) -> Self {
                N5(self.0.powi(n))
            }

            /// Float power.
            #[inline]
            pub fn powf(self, p: Self) -> Self {
                N5(self.0.powf(p.0))
            }

            /// Fused multiply-add.
            #[inline]
            pub fn mul_add(self, a: Self, b: Self) -> Self {
                N5(self.0.mul_add(a.0, b.0))
            }
        }
    };
}

impl_float_arith!(f32);
impl_float_arith!(f64);

// f64-only `From<i32>` / `From<u32>` (lossless casts; i32/u32 don't
// fit in f32's 24-bit mantissa).
impl From<i32> for N5<f64> {
    #[inline]
    fn from(n: i32) -> Self {
        N5(f64::from(n))
    }
}
impl From<u32> for N5<f64> {
    #[inline]
    fn from(n: u32) -> Self {
        N5(f64::from(n))
    }
}

/// IEEE binary16 wrapped under the N5 lattice.
#[cfg(feature = "f16")]
#[cfg_attr(docsrs, doc(cfg(feature = "f16")))]
pub type F016 = N5<f16>;

/// IEEE binary32 wrapped under the N5 lattice.
pub type F032 = N5<f32>;

/// IEEE binary64 wrapped under the N5 lattice.
pub type F064 = N5<f64>;

// ── 32-bit ULP machinery ───────────────────────────────────────────

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

/// Widen `f32` to `f64`. Used by [`def_walk_helpers!`] to give the
/// `F064F032` Conn a uniform `widen` shape (`as` casts can't be
/// passed as fn pointers, so we wrap in a free fn).
pub(crate) fn widen_f32_f64(x: f32) -> f64 {
    x as f64
}

// ── 64-bit ULP machinery ───────────────────────────────────────────

/// Word64 (IEEE bit pattern) → sign-magnitude Int64. Mirrors
/// [`signed32`].
fn signed64(x: u64) -> i64 {
    if x < 0x8000000000000000 {
        x as i64
    } else {
        (u64::MAX - (x - 0x8000000000000000)) as i64
    }
}

/// Sign-magnitude Int64 → Word64 (IEEE bit pattern). Mirrors
/// [`unsigned32`].
fn unsigned64(x: i64) -> u64 {
    if x >= 0 {
        x as u64
    } else {
        0x8000000000000000u64.wrapping_add(u64::MAX - (x as u64))
    }
}

/// Clamp between the int representations of -∞ and +∞ for `f64`.
fn clamp64(x: i64) -> i64 {
    // f64::INFINITY.to_bits()  = 0x7FF0000000000000 → signed64 = 9218868437227405312
    // f64::NEG_INFINITY        = 0xFFF0000000000000 → signed64 = -9218868437227405313
    x.clamp(-9218868437227405313, 9218868437227405312)
}

fn float_to_int64(x: f64) -> i64 {
    signed64(x.to_bits())
}

fn int64_to_float(i: i64) -> f64 {
    f64::from_bits(unsigned64(i))
}

/// Shift an `f64` by `n` ULPs (units of least precision) in the
/// sign-magnitude total order. NaN maps to ±∞ on non-zero shifts; ±∞
/// are clamped.
pub(crate) fn shift64(n: i64, x: f64) -> f64 {
    if x.is_nan() {
        return match n.signum() {
            -1 => f64::NEG_INFINITY,
            1 => f64::INFINITY,
            _ => f64::NAN,
        };
    }
    let i = float_to_int64(x);
    int64_to_float(clamp64(i.saturating_add(n)))
}

// ── Int → Float round-toward-negative-infinity ────────────────────
//
// Used by `float_ext_int_l!` (and the planned `float_fixed_l!`) so
// the `inner` direction is order-correct: `inner(b)` returns the
// largest float ≤ b. Rust's stock `b as f32` / `b as f64` casts use
// round-to-nearest-even, which can over-round and break the
// L-Galois `ceil(inner(b)) ≤ b` (kernel) law at integer values
// not exactly representable in the float.

/// `i128 → f32` with round-toward-negative-infinity.
///
/// All integer types up to `i128` are accepted via `i as i128`
/// up-cast; this single helper covers `i32`, `u32`, `i64`, `u64`,
/// and the planned Q-format `bits` types.
pub(crate) fn round_down_to_f32(b: i128) -> f32 {
    let approx = b as f32;
    if approx.is_nan() {
        return approx;
    }
    if approx == f32::INFINITY {
        // Positive overflow: largest finite f32 below `b`.
        return f32::MAX;
    }
    if approx == f32::NEG_INFINITY {
        // Negative overflow: -∞ is already the round-down direction
        // (every finite f32 is greater than `b`).
        return f32::NEG_INFINITY;
    }
    // Finite, integer-valued: `approx as i128` is exact.
    if (approx as i128) > b {
        shift32(-1, approx)
    } else {
        approx
    }
}

/// `i128 → f64` with round-toward-negative-infinity.
pub(crate) fn round_down_to_f64(b: i128) -> f64 {
    let approx = b as f64;
    if approx.is_nan() {
        return approx;
    }
    if approx == f64::INFINITY {
        return f64::MAX;
    }
    if approx == f64::NEG_INFINITY {
        return f64::NEG_INFINITY;
    }
    if (approx as i128) > b {
        shift64(-1, approx)
    } else {
        approx
    }
}

/// **Internal dispatch shim** for the `float_ext_int_l!` /
/// `float_fixed_l!` macros — picks the right `round_down_to_*` per
/// source float type. Hidden from the rendered docs and **not part
/// of the crate's stable API surface**: this trait is `pub` only
/// because the macros it backs are `#[macro_export]`ed under
/// `feature = "macros"`, and the macro expansion path
/// `$crate::float::RoundDownFromI128` must resolve in the
/// downstream crate.
///
/// The trait is **sealed** via the `private::Sealed` supertrait,
/// so external impls are a compile error rather than a silent
/// L-Galois-breaking foot-gun: `connections` ships the only three
/// valid impls (`f32`, `f64`, and — under `f16` feature — `f16`),
/// matching the round-down semantics described in
/// [`round_down_to_f32`] / [`round_down_to_f64`] /
/// [`round_down_to_f16`].
#[doc(hidden)]
pub trait RoundDownFromI128: private::Sealed + Sized {
    /// Cast `b: i128` to this float type, rounding toward `-∞`.
    fn from_i128_rd(b: i128) -> Self;
}

mod private {
    /// Sealed-trait pattern: only types listed in this module can
    /// implement [`super::RoundDownFromI128`]. Keeps the trait
    /// `pub` (so macro expansion in downstream crates resolves
    /// `$crate::float::RoundDownFromI128`) while preventing
    /// downstream impls that would silently break the L-Galois
    /// kernel law the macros depend on.
    pub trait Sealed {}
    impl Sealed for f32 {}
    impl Sealed for f64 {}
    #[cfg(feature = "f16")]
    impl Sealed for f16 {}
}

impl RoundDownFromI128 for f32 {
    #[inline]
    fn from_i128_rd(b: i128) -> Self {
        round_down_to_f32(b)
    }
}

impl RoundDownFromI128 for f64 {
    #[inline]
    fn from_i128_rd(b: i128) -> Self {
        round_down_to_f64(b)
    }
}

#[cfg(feature = "f16")]
impl RoundDownFromI128 for f16 {
    #[inline]
    fn from_i128_rd(b: i128) -> Self {
        round_down_to_f16(b)
    }
}

/// `i128 → f16` with round-toward-negative-infinity. Gated on the
/// `f16` cargo feature.
#[cfg(feature = "f16")]
pub(crate) fn round_down_to_f16(b: i128) -> f16 {
    // f16's finite range is ±65504; any `b` outside that saturates
    // to ±∞ on the cast.
    let approx: f16 = b as f16;
    if approx.is_nan() {
        return approx;
    }
    if approx == f16::INFINITY {
        return f16::MAX;
    }
    if approx == f16::NEG_INFINITY {
        return f16::NEG_INFINITY;
    }
    // `approx as i128`: f16 finite values fit in i128 exactly.
    if (approx as i128) > b {
        crate::core::f016::shift16_f16(-1, approx)
    } else {
        approx
    }
}

// ── Power-of-two scaling helpers for Q-format Conns ────────────────
//
// `float_fixed!` and `float_fixed_l!` (Phase 2) need `2^F` and `2^-F`
// as f64 values to bridge between Q-format bit-storage and float
// real-values. F can be up to 128 in our rung set, well within
// f64's exponent range (normal: −1022..1023; denormal extends to
// −1074), so both scales are exactly representable in f64. Computed
// via direct bit-pattern construction so the helpers are `const fn`.

/// `2^frac` as `f64`, exact for `frac ≤ 1023` (covers our `frac ≤ 128`
/// rung cadence with room to spare).
///
/// Bias-1023 exponent encoding: `2^F` has biased exponent `1023 + F`,
/// mantissa zero. `f64::from_bits` materialises the value at compile
/// time.
#[inline]
#[cfg(feature = "fixed")]
pub(crate) const fn scale_pow2_f64(frac: u32) -> f64 {
    let biased = (1023u64 + frac as u64) << 52;
    f64::from_bits(biased)
}

/// `2^-frac` as `f64`, exact for `frac ≤ 1022` (normal range).
/// Returns `0.0` for `frac > 1074` (true mathematical underflow); we
/// only use `frac ≤ 128`, far inside the normal regime.
///
/// Splits at the normal/denormal boundary because f64 denormals have
/// a different bit-pattern structure (implicit leading bit becomes
/// zero, exponent field stays at zero). For our `frac ≤ 128` use
/// case only the normal branch fires.
#[inline]
#[cfg(feature = "fixed")]
pub(crate) const fn scale_pow2_f64_neg(frac: u32) -> f64 {
    if frac <= 1022 {
        // Normal: biased exponent (1023 - frac).
        let biased = (1023u64 - frac as u64) << 52;
        f64::from_bits(biased)
    } else if frac <= 1074 {
        // Denormal: exponent = 0, mantissa = 1 << (1074 - frac).
        let mantissa = 1u64 << (1074 - frac as u64);
        f64::from_bits(mantissa)
    } else {
        0.0
    }
}

// ── f64 → narrower float, round-toward-negative-infinity ───────────
//
// Used by `float_fixed_l!`'s `inner` so the f64 → source-float
// downcast is order-correct in the L-Galois sense. Rust's stock
// `v as f32` / `v as f16` rounds-to-nearest-even, which can
// over-round at the f32/f16 ULP grid and break
// `ceil(inner(b)) ≤ b`.

/// `u128 → f64` with round-toward-negative-infinity.
///
/// Mirrors [`round_down_to_f64`] but for the unsigned 128-bit case
/// where `b as i128` would wrap for `b > i128::MAX`. Used by the
/// `float_fixed_l!` macro's `inner` to bridge u128 Q-format storage
/// to its real-value f64 representation.
pub(crate) fn round_down_to_f64_u128(b: u128) -> f64 {
    let approx = b as f64;
    if approx.is_nan() {
        return approx;
    }
    if approx == f64::INFINITY {
        // Defensive — `b as f64` rounds to at most 2^128 (exact
        // f64), never +∞. Mirrors `round_down_to_f64`.
        return f64::MAX;
    }
    // Top-end saturation: when `approx == 2^128` (the f64 image of
    // any `b` in roughly `[2^128 - 2^75, u128::MAX]`), the cast
    // back via `approx as u128` saturates to `u128::MAX`. Equal-
    // bits comparison can't distinguish round-up from exact, so
    // shift unconditionally — `2^128 > u128::MAX` in real terms.
    if approx == (u128::MAX as f64) {
        return shift64(-1, approx);
    }
    // Below the saturation threshold, `approx as u128` is exact;
    // detect round-up and step down by one ULP if so.
    if (approx as u128) > b {
        shift64(-1, approx)
    } else {
        approx
    }
}

/// `f64 → f32` with round-toward-negative-infinity. Mirrors
/// [`round_down_to_f32`] but operates on a finite f64 value rather
/// than an `i128` integer.
pub(crate) fn round_down_f64_to_f32(v: f64) -> f32 {
    let approx = v as f32;
    if approx.is_nan() {
        return approx;
    }
    if approx == f32::INFINITY {
        // Positive overflow: largest f32 ≤ v is f32::MAX (when v is
        // strictly above f32::MAX) or +∞ (when v is +∞ itself).
        return if v > f32::MAX as f64 {
            f32::MAX
        } else {
            f32::INFINITY
        };
    }
    if approx == f32::NEG_INFINITY {
        return f32::NEG_INFINITY;
    }
    // Finite f32: compare via exact f32→f64 upcast.
    if (approx as f64) > v {
        shift32(-1, approx)
    } else {
        approx
    }
}

/// `f64 → f16` with round-toward-negative-infinity. Gated on `f16`.
#[cfg(feature = "f16")]
pub(crate) fn round_down_f64_to_f16(v: f64) -> f16 {
    let approx: f16 = v as f16;
    if approx.is_nan() {
        return approx;
    }
    if approx == f16::INFINITY {
        return if v > f16::MAX as f64 {
            f16::MAX
        } else {
            f16::INFINITY
        };
    }
    if approx == f16::NEG_INFINITY {
        return f16::NEG_INFINITY;
    }
    if (approx as f64) > v {
        crate::core::f016::shift16_f16(-1, approx)
    } else {
        approx
    }
}

/// **Internal dispatch shim** for the `float_fixed!` / `float_fixed_l!`
/// macros — picks the right `round_down_f64_to_*` per source float
/// type. Hidden from the rendered docs and **not part of the
/// crate's stable API surface**: same `pub`-but-sealed pattern as
/// [`RoundDownFromI128`].
///
/// The trait is sealed via the `private::Sealed` supertrait, so
/// downstream impls are a compile error rather than a silent
/// L-Galois-breaking foot-gun.
#[doc(hidden)]
pub trait RoundDownFromF64: private::Sealed + Sized {
    /// Cast `v: f64` to this float type, rounding toward `-∞`.
    fn from_f64_rd(v: f64) -> Self;
}

impl RoundDownFromF64 for f64 {
    #[inline]
    fn from_f64_rd(v: f64) -> Self {
        v
    }
}

impl RoundDownFromF64 for f32 {
    #[inline]
    fn from_f64_rd(v: f64) -> Self {
        round_down_f64_to_f32(v)
    }
}

#[cfg(feature = "f16")]
impl RoundDownFromF64 for f16 {
    #[inline]
    fn from_f64_rd(v: f64) -> Self {
        round_down_f64_to_f16(v)
    }
}

/// **Internal dispatch shim** for the `float_fixed!` /
/// `float_fixed_l!` macros — converts a Q-format host bit-pattern
/// (`i8`/`u8`/.../`i128`/`u128`) to its f64 round-toward-negative-
/// infinity representation. Same `pub`-but-sealed pattern as
/// [`RoundDownFromI128`].
///
/// For host bit-widths ≤ 53 (`i8..i32`, `u8..u32`), `as f64` is
/// exact; the impls return the identity cast. For 64-bit hosts
/// (`i64`/`u64`), bits fit in `i128` and the i128-side
/// [`round_down_to_f64`] is the right tool. For 128-bit signed
/// (`i128`), the bits already are i128. For 128-bit unsigned
/// (`u128`), bits exceed i128 range; dispatch to
/// [`round_down_to_f64_u128`] which handles the
/// `u128::MAX as f64 == 2^128` saturation explicitly.
#[doc(hidden)]
pub trait BitsToF64Rd: bits_private::Sealed + Sized {
    /// Cast `self` to `f64`, rounding toward `-∞`.
    fn to_f64_rd(self) -> f64;
}

mod bits_private {
    pub trait Sealed {}
    impl Sealed for i8 {}
    impl Sealed for u8 {}
    impl Sealed for i16 {}
    impl Sealed for u16 {}
    impl Sealed for i32 {}
    impl Sealed for u32 {}
    impl Sealed for i64 {}
    impl Sealed for u64 {}
    impl Sealed for i128 {}
    impl Sealed for u128 {}
}

// 8-bit / 16-bit / 32-bit hosts: `as f64` is exact (bits ≤ 32 < 53).
impl BitsToF64Rd for i8 {
    #[inline]
    fn to_f64_rd(self) -> f64 {
        self as f64
    }
}
impl BitsToF64Rd for u8 {
    #[inline]
    fn to_f64_rd(self) -> f64 {
        self as f64
    }
}
impl BitsToF64Rd for i16 {
    #[inline]
    fn to_f64_rd(self) -> f64 {
        self as f64
    }
}
impl BitsToF64Rd for u16 {
    #[inline]
    fn to_f64_rd(self) -> f64 {
        self as f64
    }
}
impl BitsToF64Rd for i32 {
    #[inline]
    fn to_f64_rd(self) -> f64 {
        self as f64
    }
}
impl BitsToF64Rd for u32 {
    #[inline]
    fn to_f64_rd(self) -> f64 {
        self as f64
    }
}

// 64-bit hosts: bits fit in i128 losslessly; reuse the i128 helper.
impl BitsToF64Rd for i64 {
    #[inline]
    fn to_f64_rd(self) -> f64 {
        round_down_to_f64(self as i128)
    }
}
impl BitsToF64Rd for u64 {
    #[inline]
    fn to_f64_rd(self) -> f64 {
        round_down_to_f64(self as i128)
    }
}

// 128-bit hosts: signed already is i128; unsigned needs the
// u128-specific top-end saturation handling.
impl BitsToF64Rd for i128 {
    #[inline]
    fn to_f64_rd(self) -> f64 {
        round_down_to_f64(self)
    }
}
impl BitsToF64Rd for u128 {
    #[inline]
    fn to_f64_rd(self) -> f64 {
        round_down_to_f64_u128(self)
    }
}

/// Generate the four ULP-walk helpers (`ascend_to_ceil`,
/// `descend_to_ceil`, `ascend_to_floor`, `descend_to_floor`) for one
/// `Src → Dst` precision-narrowing Conn, packaged in a private
/// submodule named `$mod_name`. The 6-arg variant additionally emits
/// `solve_to_ceil` for instantiations whose `$dst` has 1 ns
/// resolution (durations / epochs); see below.
///
/// Each helper returns `(Dst, u32)` — the corrected target value and
/// the number of ULP-shift iterations consumed. Production callers
/// throw the count away (`let (z, _) = …`); the `ulp_steps_bounded`
/// proptest reads it to assert the loop converges in ≤ 2 iterations.
///
/// Parameters (4-arg form, float-narrowing):
/// - `$mod_name` — the private submodule wrapping this Conn's
///   helpers, e.g. `f064_f016_walks`.
/// - `$src` — the wider float type (`f32`, `f64`).
/// - `$dst` — the narrower float type (`f32`, or `f16` when the
///   `f16` cargo feature is enabled).
/// - `$shift` — a `fn(i32, $dst) -> $dst` that shifts `n` ULPs in
///   sign-magnitude total order.
/// - `$widen` — a `fn($dst) -> $src` that widens losslessly. Always
///   a free fn wrapper around `as` casts (since `as` casts can't be
///   passed as fn pointers).
///
/// 6-arg form (duration / epoch destinations) adds:
/// - `$to_ns: fn($dst) -> i128` — extract the `$dst` value's
///   nanosecond-integer encoding.
/// - `$from_ns: fn(i128) -> $dst` — saturating reconstruction from
///   nanoseconds; clamps at `$dst`'s representable range.
///
/// In the 6-arg form, `solve_to_ceil` replaces the (unbounded at
/// extreme magnitudes) `ascend_to_ceil` / `descend_to_ceil` pair with
/// a binary-search cut-finder in `i128`-ns space — `O(log
/// plateau_width)` ≤ 51 iterations vs. up to ~2 × 10¹² for the walk.
/// The walk helpers are still emitted (used by Kani harnesses and as
/// a cross-check in proptests), but production code calls only
/// `solve_to_ceil`.
///
/// The generated module's helpers are `pub(super)` — visible to the
/// owning Conn's `ceil`/`floor` functions and to `#[cfg(test)]` code
/// in the same parent file, but not exposed beyond.
macro_rules! def_walk_helpers {
    ($mod_name:ident, $src:ty, $dst:ty, $shift:path, $widen:path) => {
        $crate::float::def_walk_helpers!(
            @inner $mod_name, $src, $dst, $shift, $widen,
        );
    };
    ($mod_name:ident, $src:ty, $dst:ty, $shift:path, $widen:path, $to_ns:path, $from_ns:path) => {
        $crate::float::def_walk_helpers!(
            @inner $mod_name, $src, $dst, $shift, $widen,
            @solve $to_ns, $from_ns
        );
    };
    (@inner $mod_name:ident, $src:ty, $dst:ty, $shift:path, $widen:path,
        $(@solve $to_ns:path, $from_ns:path)?) => {
        mod $mod_name {
            #[allow(unused_imports)]
            use super::*;

            /// Walk up (toward +∞) until `widen(z) >= x`, returning `(z, steps)`.
            #[allow(dead_code)]
            pub(super) fn ascend_to_ceil(start: $dst, x: $src) -> ($dst, u32) {
                let mut z = start;
                let mut steps = 0;
                loop {
                    let next = $shift(1, z);
                    if next <= z {
                        return (z, steps);
                    }
                    steps += 1;
                    z = next;
                    if x <= $widen(z) {
                        return (z, steps);
                    }
                }
            }

            /// Walk down (toward -∞) while `widen(z) >= x` still holds.
            #[allow(dead_code)]
            pub(super) fn descend_to_ceil(start: $dst, x: $src) -> ($dst, u32) {
                let mut z = start;
                let mut steps = 0;
                loop {
                    let next = $shift(-1, z);
                    if z <= next {
                        return (z, steps);
                    }
                    let next_up = $widen(next);
                    // Inputs are non-NaN by construction, so `>` is
                    // equivalent to `!(x <= next_up)` here.
                    if x > next_up {
                        return (z, steps);
                    }
                    steps += 1;
                    z = next;
                }
            }

            /// Walk up (toward +∞) while `widen(z) <= x` still holds.
            // (Plan 32) Currently unused: the `*_floor` functions that
            // called these were dropped along with the float↔duration
            // ConnL demotion. `pub(super)` only — kept inside the macro
            // expansion so a future reinstatement of a per-rung floor
            // walker in the same module doesn't have to re-derive the
            // shift loop.
            #[allow(dead_code)]
            pub(super) fn ascend_to_floor(start: $dst, x: $src) -> ($dst, u32) {
                let mut z = start;
                let mut steps = 0;
                loop {
                    let next = $shift(1, z);
                    if next <= z {
                        return (z, steps);
                    }
                    let next_up = $widen(next);
                    if next_up > x {
                        return (z, steps);
                    }
                    steps += 1;
                    z = next;
                }
            }

            /// Walk down (toward -∞) until `widen(z) <= x`.
            #[allow(dead_code)]
            pub(super) fn descend_to_floor(start: $dst, x: $src) -> ($dst, u32) {
                let mut z = start;
                let mut steps = 0;
                loop {
                    let next = $shift(-1, z);
                    if z <= next {
                        return (z, steps);
                    }
                    steps += 1;
                    z = next;
                    if $widen(z) <= x {
                        return (z, steps);
                    }
                }
            }

            $(
                /// Solve directly for the smallest `z` such that
                /// `widen(z) >= x`, by binary search in `i128`-ns
                /// space.
                ///
                /// Replaces `descend_to_ceil` / `ascend_to_ceil` for
                /// `$dst` types with 1 ns resolution. Bound is
                /// `⌈log₂(2 × 2⁵⁰)⌉ = 51` iterations; production
                /// callers bound by `SOLVE_STEP_BOUND = 52` (one
                /// extra slot for the terminal `lo == hi` check).
                ///
                /// ## Bracket sizing
                ///
                /// The search bracket `n_start ± 2⁵⁰ ns` (≈
                /// `±1.13 × 10¹⁵` ns ≈ `±13` days) must contain
                /// the true ceil for the result to be correct. The
                /// upper bound on `|n_start − true_ceil|` is the
                /// f64 plateau width at the input magnitude (≤ 1
                /// ULP-of-`v` in seconds, expressed in ns).
                ///
                /// At each `$dst`'s rim-guarded magnitude:
                ///
                /// | `$dst`             | `max_secs`     | ULP-in-ns         | bracket / ULP |
                /// |--------------------|----------------|-------------------|---------------|
                /// | `Duration` (time)  | ≈ 9.22 × 10¹⁸  | ≈ 2.05 × 10¹²     | ≈ 550×        |
                /// | `StdDuration`      | ≈ 1.84 × 10¹⁹  | ≈ 4.1 × 10¹²      | ≈ 275×        |
                /// | `HD` (hifitime)    | ≈ 1.03 × 10¹⁴  | ≈ 2.3 × 10⁷       | ≈ 5 × 10⁷×    |
                /// | `Epoch` (hifitime) | (HD-bounded)   | ≈ 2.3 × 10⁷       | ≈ 5 × 10⁷×    |
                ///
                /// `StdDuration` is the tight side: the bracket is
                /// 275 × ULP-in-ns at MAX, so even a `from_secs_f64`
                /// implementation that rounded to 200 ULPs would
                /// stay inside. The pre-Plan-2026-05-08-05 bracket
                /// of `2⁴²` (~7% margin) was flagged as insufficient
                /// in `claude-review` discussion `dea66ea8` on
                /// MR !86; this is the fix.
                #[allow(dead_code)]
                pub(super) fn solve_to_ceil(start: $dst, x: $src) -> ($dst, u32) {
                    let n_start: i128 = $to_ns(start);
                    let mut lo: i128 = n_start.saturating_sub(1i128 << 50);
                    let mut hi: i128 = n_start.saturating_add(1i128 << 50);
                    let mut steps: u32 = 0;
                    while lo < hi {
                        let mid = lo + (hi - lo) / 2;
                        if $widen($from_ns(mid)) >= x {
                            hi = mid;
                        } else {
                            lo = mid + 1;
                        }
                        steps += 1;
                    }
                    let z = $from_ns(lo);
                    // Guard the bracket-correctness invariant: if the
                    // true ceil ever falls outside `n_start ± 2⁵⁰`, the
                    // search returns the upper bracket boundary and
                    // `widen(z) < x` — silently violating the `ceil`
                    // contract. The headroom table above proves this
                    // can't happen for the in-tree instantiations, but
                    // a future Conn or a stdlib drift in
                    // `from_secs_f64` could break the assumption; the
                    // debug-only check keeps it auditable. (Defense
                    // raised by `claude-review` discussion 733bf488 on
                    // MR !86.)
                    debug_assert!(
                        $widen(z) >= x,
                        "solve_to_ceil bracket too narrow: widen(lo) < x"
                    );
                    (z, steps)
                }
            )?
        }
    };
}

pub(crate) use def_walk_helpers;

// ── Float → Extended<intN> macros ────────────────────────────────────
//
// `float_ext_int!` emits a full Galois adjoint triple
// (`ConnL` + `ConnR` impls via `conn_k!`) for the cases where the
// target integer fits losslessly in the source float's mantissa.
// `float_ext_int_l!` emits a left-only `Conn` for the cases where it
// doesn't (target precision exceeds source mantissa, so `floor` and
// `ceil` would alias on the same `int` value at large magnitudes,
// violating `order_reflecting`).
//
// Saturation policy (mirrors Haskell `fxxext` in
// `connections-haskell/src/Data/Connection/Float.hs:393-405`):
//
// - `N5(NaN)`          → `PosInf` on `ceil`, `NegInf` on `floor`
// - `N5(NEG_INFINITY)` → `NegInf`
// - `N5(INFINITY)`     → `PosInf`
// - `N5(v)` with `v >  hi` → `PosInf` (ceil) / `Finite(<int>::MAX)` (floor)
// - `N5(v)` with `v <  lo` → `Finite(<int>::MIN)` (ceil) / `NegInf` (floor)
// - `N5(v)` with `lo ≤ v ≤ hi` → `Finite(v.ceil() as int)` / `Finite(v.floor() as int)`
//
// `inner` always materialises a finite float for `Finite(i)` and
// emits ±INFINITY for `NegInf` / `PosInf` (matching Haskell's
// `extended (-1/0) (1/0) fromIntegral` at Float.hs:398).
//
// The `floor ≤ ceil` invariant holds in every branch by construction.

// `#[macro_export]` is mandatory even though the macro is internal:
// the public-facing `float_ext_int_l!` / `float_ext_int_r!` macros —
// used in this crate's own `src/core/{i,u}NNN.rs` files even when the
// `macros` cargo feature is off — expand into
// `$crate::__float_ext_int_*_body!` invocations, which only resolve
// when the helper sits at the crate root. The `__` prefix and
// `#[doc(hidden)]` mark it as not part of the public surface;
// downstream callers should never invoke it directly.
#[doc(hidden)]
#[macro_export]
macro_rules! __float_ext_int_ceil_body {
    ($float:ty, $int:ty, $v:ident) => {{
        // NaN is below +∞ and incomparable with finite values, so the
        // smallest Extended<int> whose upper image is >= NaN is PosInf.
        if $v.is_nan() {
            $crate::extended::Extended::PosInf
        } else if $v == <$float>::NEG_INFINITY {
            $crate::extended::Extended::NegInf
        } else if $v == <$float>::INFINITY {
            // Explicit +∞ → PosInf so f16 sources (where
            // `<$int>::MAX as f16` saturates to +∞ for any target
            // wider than `u8`/`i8`) classify +∞ correctly: the
            // unified `v > hi` branch can't distinguish +∞ from
            // saturated `hi`.
            $crate::extended::Extended::PosInf
        } else {
            let lo = <$int>::MIN as $float;
            let hi = <$int>::MAX as $float;
            // With NaN and infinities handled above, this branch sees
            // finite payloads only. For finite `lo`, values below the
            // target range ceil to `Finite(MIN)`. If `lo` itself
            // saturated to `-∞` (f16 sources with wide integer
            // targets), no finite source can fall below it, so the
            // cast path remains the in-range case.
            if $v > hi {
                $crate::extended::Extended::PosInf
            } else if $v < lo {
                $crate::extended::Extended::Finite(<$int>::MIN)
            } else {
                let scaled_ceil_float: $float = $v.ceil();
                let bits: $int = scaled_ceil_float as $int;
                // Boundary-saturation overflow detection: when
                // `<$int>::MAX` rounds up in the source float (host
                // bits > source mantissa bits), the strict
                // `$v > hi` guard above misses the case where
                // `$v == hi` while `real_v > real_max`. The
                // saturating cast pinned `bits` to `MAX`; verify via
                // the round-down image of `MAX` whether the cast
                // actually overflowed. For hosts where `MAX` is
                // f64-exact (host bits ≤ 32, where 32-bit ints fit
                // in f64's 53-bit mantissa), `to_f64_rd(MAX) ==
                // hi as f64` and this check is a no-op; for wider
                // hosts (i64/u64/i128/u128) it's a live guard.
                // Mirrors `__float_fix_ceil_body!` in `src/fixed.rs`.
                if bits == <$int>::MAX
                    && <$int as $crate::float::BitsToF64Rd>::to_f64_rd(<$int>::MAX)
                        < scaled_ceil_float as f64
                {
                    $crate::extended::Extended::PosInf
                } else {
                    $crate::extended::Extended::Finite(bits)
                }
            }
        }
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __float_ext_int_floor_body {
    ($float:ty, $int:ty, $v:ident) => {{
        if $v.is_nan() {
            $crate::extended::Extended::NegInf
        } else if $v == <$float>::NEG_INFINITY {
            $crate::extended::Extended::NegInf
        } else if $v == <$float>::INFINITY {
            $crate::extended::Extended::PosInf
        } else {
            let lo = <$int>::MIN as $float;
            let hi = <$int>::MAX as $float;
            if $v > hi {
                $crate::extended::Extended::Finite(<$int>::MAX)
            } else if $v < lo {
                $crate::extended::Extended::NegInf
            } else {
                $crate::extended::Extended::Finite($v.floor() as $int)
            }
        }
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __float_ext_int_inner_body {
    ($float:ty, $int:ty, $b:ident) => {
        // The `Finite` arm uses round-toward-negative-infinity for
        // the int → float cast. For full-triple Conns (target fits
        // in source mantissa) the cast is exact and round-down is
        // a no-op; for L-only Conns it preserves
        // `ceil(inner(b)) ≤ b` (the L-Galois kernel law), which a
        // round-to-nearest cast can break when an `int` value
        // round-trips up rather than down through the float.
        match $b {
            $crate::extended::Extended::NegInf => $crate::float::N5::new(<$float>::NEG_INFINITY),
            $crate::extended::Extended::PosInf => $crate::float::N5::new(<$float>::INFINITY),
            $crate::extended::Extended::Finite(i) => $crate::float::N5::new(
                <$float as $crate::float::RoundDownFromI128>::from_i128_rd(i as i128),
            ),
        }
    };
}

/// Emit a full adjoint-triple Conn `Conn<N5<$float>,
/// Extended<$int>>` (impls `ConnL` + `ConnR`) via
/// [`conn_k!`](crate::conn_k).
///
/// Use when `<$int>::BITS ≤ <$float>::MANTISSA_DIGITS + 1` so that
/// every `int` value embeds losslessly into the float — only then is
/// `inner` order-reflecting and a true triple exists.
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! float_ext_int {
    ($(#[$meta:meta])* $vis:vis $name:ident, $float:ty, $int:ty) => {
        $crate::conn_k! {
            $(#[$meta])*
            $vis $name : $crate::float::N5<$float> => $crate::extended::Extended<$int> {
                ceil:  {
                    fn ceil(x: $crate::float::N5<$float>)
                        -> $crate::extended::Extended<$int>
                    {
                        let v = x.into_inner();
                        $crate::__float_ext_int_ceil_body!($float, $int, v)
                    }
                    ceil
                },
                inner: {
                    fn inner(b: $crate::extended::Extended<$int>)
                        -> $crate::float::N5<$float>
                    {
                        $crate::__float_ext_int_inner_body!($float, $int, b)
                    }
                    inner
                },
                floor: {
                    fn floor(x: $crate::float::N5<$float>)
                        -> $crate::extended::Extended<$int>
                    {
                        let v = x.into_inner();
                        $crate::__float_ext_int_floor_body!($float, $int, v)
                    }
                    floor
                },
            }
        }
    };
}

/// Emit an L-only Conn `Conn<N5<$float>, Extended<$int>, L>`.
///
/// Use when `<$int>::BITS > <$float>::MANTISSA_DIGITS + 1` so that
/// `inner: Extended<int> → N5<float>` aliases distinct
/// `int` values onto the same float at large magnitudes — the L-Galois
/// adjunction `ceil ⊣ inner` still holds, but `order_reflecting` and
/// hence `floor_le_ceil` (as a triple) do not.
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! float_ext_int_l {
    ($(#[$meta:meta])* $vis:vis $name:ident, $float:ty, $int:ty) => {
        $(#[$meta])*
        $vis const $name: $crate::conn::Conn<
            $crate::float::N5<$float>,
            $crate::extended::Extended<$int>,
        > = {
            fn ceil(x: $crate::float::N5<$float>)
                -> $crate::extended::Extended<$int>
            {
                let v = x.into_inner();
                $crate::__float_ext_int_ceil_body!($float, $int, v)
            }
            fn inner(b: $crate::extended::Extended<$int>)
                -> $crate::float::N5<$float>
            {
                $crate::__float_ext_int_inner_body!($float, $int, b)
            }
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

pub(crate) use float_ext_int;
pub(crate) use float_ext_int_l;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extended::Extended;
    use crate::prop::arb::extended_float_f64;
    use proptest::prelude::*;

    // ── 32-bit ULP sanity ──────────────────────────────────────────

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

    #[test]
    fn shift64_from_zero() {
        let z = shift64(1, 0.0);
        assert!(z > 0.0);
        assert_eq!(z, f64::from_bits(1));
    }

    #[test]
    fn shift64_nan_to_inf() {
        assert_eq!(shift64(1, f64::NAN), f64::INFINITY);
        assert_eq!(shift64(-1, f64::NAN), f64::NEG_INFINITY);
        assert!(shift64(0, f64::NAN).is_nan());
    }

    #[test]
    fn shift64_inf_clamped() {
        assert_eq!(shift64(1, f64::INFINITY), f64::INFINITY);
        assert_eq!(shift64(-1, f64::NEG_INFINITY), f64::NEG_INFINITY);
    }

    // ── N5 tests ────────────────────────────────────────

    #[test]
    fn nan_reflexive_f64() {
        let n: N5<f64> = N5::new(f64::NAN);
        assert_eq!(n, N5::new(f64::NAN));
        assert_eq!(
            n.partial_cmp(&N5::new(f64::NAN)),
            Some(core::cmp::Ordering::Equal)
        );
    }

    #[test]
    fn float_ext_int_helper_boundary_policy() {
        let v = f32::NAN;
        assert_eq!(
            crate::__float_ext_int_ceil_body!(f32, u8, v),
            Extended::PosInf
        );
        assert_eq!(
            crate::__float_ext_int_floor_body!(f32, u8, v),
            Extended::NegInf
        );

        let v = f32::NEG_INFINITY;
        assert_eq!(
            crate::__float_ext_int_ceil_body!(f32, u8, v),
            Extended::NegInf
        );
        assert_eq!(
            crate::__float_ext_int_floor_body!(f32, u8, v),
            Extended::NegInf
        );

        let v = f32::INFINITY;
        assert_eq!(
            crate::__float_ext_int_ceil_body!(f32, u8, v),
            Extended::PosInf
        );
        assert_eq!(
            crate::__float_ext_int_floor_body!(f32, u8, v),
            Extended::PosInf
        );
    }

    #[cfg(feature = "f16")]
    #[test]
    fn float_ext_int_helper_f16_wide_boundary_policy() {
        let v = f16::NAN;
        assert_eq!(
            crate::__float_ext_int_ceil_body!(f16, i16, v),
            Extended::PosInf
        );
        assert_eq!(
            crate::__float_ext_int_floor_body!(f16, i16, v),
            Extended::NegInf
        );

        let v = f16::NEG_INFINITY;
        assert_eq!(
            crate::__float_ext_int_ceil_body!(f16, i16, v),
            Extended::NegInf
        );
        assert_eq!(
            crate::__float_ext_int_floor_body!(f16, i16, v),
            Extended::NegInf
        );

        let v = f16::INFINITY;
        assert_eq!(
            crate::__float_ext_int_ceil_body!(f16, i16, v),
            Extended::PosInf
        );
        assert_eq!(
            crate::__float_ext_int_floor_body!(f16, i16, v),
            Extended::PosInf
        );
    }

    #[test]
    fn nan_incomparable_with_finite_f64() {
        let n: N5<f64> = N5::new(f64::NAN);
        assert!(n.partial_cmp(&N5::new(1.0)).is_none());
        assert!(N5::new(1.0_f64).partial_cmp(&n).is_none());
    }

    #[test]
    fn nan_between_infinities_f64() {
        let n: N5<f64> = N5::new(f64::NAN);
        assert!(N5::new(f64::NEG_INFINITY) < n);
        assert!(n < N5::new(f64::INFINITY));
    }

    #[test]
    fn standard_order_preserved_f64() {
        assert!(N5::new(1.0_f64) < N5::new(2.0));
        assert!(N5::new(f64::NEG_INFINITY) < N5::new(0.0_f64));
        assert!(N5::new(0.0_f64) < N5::new(f64::INFINITY));
    }

    #[test]
    fn f32_same_shape() {
        let n: N5<f32> = N5::new(f32::NAN);
        assert_eq!(n, N5::new(f32::NAN));
        assert!(N5::new(f32::NEG_INFINITY) < n);
        assert!(n < N5::new(f32::INFINITY));
        assert!(n.partial_cmp(&N5::new(1.0_f32)).is_none());
    }

    proptest! {
        #[test]
        fn n5_reflexive(x in extended_float_f64()) {
            prop_assert_eq!(x, x);
            prop_assert_eq!(x.partial_cmp(&x), Some(core::cmp::Ordering::Equal));
        }
    }

    // ── Numeric impls for N5<f32 | f64> ────────────────

    #[test]
    fn add_extends_passes_through_f64() {
        let a: N5<f64> = N5::new(1.5);
        let b: N5<f64> = N5::new(2.25);
        assert_eq!(a + b, N5::new(3.75));
    }

    #[test]
    fn sub_zero_is_id_f64() {
        let a: N5<f64> = N5::new(std::f64::consts::PI);
        let zero: N5<f64> = N5::from(0u8);
        assert_eq!(a - zero, a);
    }

    #[test]
    fn div_by_two_halves_f64() {
        let a: N5<f64> = N5::new(8.0);
        let two: N5<f64> = N5::from(2u8);
        assert_eq!(a / two, N5::new(4.0));
    }

    #[test]
    fn from_u8_round_trips_f32_f64() {
        for n in [0u8, 1, 2, 7, 42, u8::MAX] {
            assert_eq!(N5::<f64>::from(n), N5::new(n as f64));
            assert_eq!(N5::<f32>::from(n), N5::new(n as f32));
        }
    }

    #[test]
    fn sub_delegates_to_ieee_f64() {
        let a: N5<f64> = N5::new(5.5);
        let b: N5<f64> = N5::new(1.25);
        assert_eq!(a - b, N5::new(4.25));
    }

    #[test]
    fn arithmetic_delegates_to_ieee_at_infinities() {
        let neg_inf: N5<f64> = N5::new(f64::NEG_INFINITY);
        let pos_inf: N5<f64> = N5::new(f64::INFINITY);
        let nan: N5<f64> = N5::new(f64::NAN);

        assert!((neg_inf + pos_inf).is_nan());
        assert!((pos_inf - pos_inf).is_nan());
        assert!((nan + N5::new(1.0)).is_nan());
        assert_eq!((-neg_inf), pos_inf);
    }

    // ── T1: Mul / Neg / Rem + *Assign ─────────────────────────────

    #[test]
    fn mul_extends_passes_through_f64() {
        let a: N5<f64> = N5::new(2.5);
        let b: N5<f64> = N5::new(4.0);
        assert_eq!(a * b, N5::new(10.0));
    }

    #[test]
    fn neg_double_is_id_f64() {
        let a: N5<f64> = N5::new(std::f64::consts::PI);
        assert_eq!(-(-a), a);
    }

    #[test]
    fn neg_infinities_flip() {
        assert_eq!(-N5::new(f64::NEG_INFINITY), N5::new(f64::INFINITY));
        assert_eq!(-N5::new(f64::INFINITY), N5::new(f64::NEG_INFINITY));
        let one: N5<f64> = N5::new(1.0);
        assert_eq!(-one, N5::new(-1.0));
    }

    #[test]
    fn rem_zero_inner_passes_through_f64() {
        // N5 arithmetic forwards to inner f64 % f64, which is NaN for
        // divisor 0.0 — IEEE 754 semantics, no lattice arm involved.
        let a: N5<f64> = N5::new(7.5);
        let zero: N5<f64> = N5::new(0.0);
        assert!((a % zero).is_nan());
    }

    #[test]
    fn rem_infinity_arms_f64() {
        // ∞ % anything is NaN per IEEE.
        let one: N5<f64> = N5::new(1.0);
        assert!((N5::new(f64::NEG_INFINITY) % one).is_nan());
        assert!((N5::new(f64::INFINITY) % one).is_nan());
        // finite % ∞ = finite (the divisor is larger in magnitude than
        // any finite, so the remainder is the dividend itself).
        let a: N5<f64> = N5::new(7.5);
        assert_eq!(a % N5::new(f64::INFINITY), a);
        assert_eq!(a % N5::new(f64::NEG_INFINITY), a);
    }

    #[test]
    fn div_infinity_arms_f64() {
        assert!((N5::new(f64::NEG_INFINITY) / N5::new(f64::INFINITY)).is_nan());
        let three: N5<f64> = N5::new(3.0);
        assert_eq!((three / N5::new(f64::INFINITY)).into_inner(), 0.0);
        assert_eq!((three / N5::new(f64::NEG_INFINITY)).into_inner(), -0.0);
    }

    #[test]
    fn add_assign_matches_add_f64() {
        let a: N5<f64> = N5::new(3.5);
        let b: N5<f64> = N5::new(1.25);
        let by_value = a + b;
        let mut by_assign = a;
        by_assign += b;
        assert_eq!(by_assign, by_value);
    }

    #[test]
    fn sub_assign_matches_sub_f64() {
        let a: N5<f64> = N5::new(3.5);
        let b: N5<f64> = N5::new(1.25);
        let by_value = a - b;
        let mut by_assign = a;
        by_assign -= b;
        assert_eq!(by_assign, by_value);
    }

    #[test]
    fn mul_assign_matches_mul_f64() {
        let a: N5<f64> = N5::new(3.0);
        let b: N5<f64> = N5::new(4.0);
        let by_value = a * b;
        let mut by_assign = a;
        by_assign *= b;
        assert_eq!(by_assign, by_value);
    }

    #[test]
    fn div_assign_matches_div_f64() {
        let a: N5<f64> = N5::new(8.0);
        let b: N5<f64> = N5::new(2.0);
        let by_value = a / b;
        let mut by_assign = a;
        by_assign /= b;
        assert_eq!(by_assign, by_value);
    }

    #[test]
    fn rem_assign_matches_rem_f64() {
        let a: N5<f64> = N5::new(7.5);
        let b: N5<f64> = N5::new(2.0);
        let by_value = a % b;
        let mut by_assign = a;
        by_assign %= b;
        assert_eq!(by_assign, by_value);
    }

    // ── T2: Inherent transcendentals + constants + predicates ─────

    #[test]
    fn pi_constant_round_trips_f32_f64() {
        assert_eq!(N5::<f32>::PI, N5::new(std::f32::consts::PI));
        assert_eq!(N5::<f64>::PI, N5::new(std::f64::consts::PI));
    }

    #[test]
    fn nan_infinity_constants_f64() {
        assert!(N5::<f64>::NAN.is_nan());
        assert_eq!(N5::<f64>::INFINITY, N5::new(f64::INFINITY));
        assert_eq!(N5::<f64>::NEG_INFINITY, N5::new(f64::NEG_INFINITY));
        assert_eq!(N5::<f64>::ZERO, N5::new(0.0));
        assert_eq!(N5::<f64>::ONE, N5::new(1.0));
    }

    #[test]
    fn predicates_classify_correctly_f64() {
        let neg_inf = N5::<f64>::NEG_INFINITY;
        let pos_inf = N5::<f64>::INFINITY;
        let nan = N5::<f64>::NAN;
        let pi = N5::<f64>::PI;

        assert!(!neg_inf.is_nan() && !pos_inf.is_nan() && nan.is_nan() && !pi.is_nan());
        assert!(!neg_inf.is_finite() && !pos_inf.is_finite() && !nan.is_finite() && pi.is_finite());
        assert!(neg_inf.is_infinite() && pos_inf.is_infinite() && !pi.is_infinite());
    }

    #[test]
    fn sin_extends_passes_through_f64() {
        // sin(0) is exactly 0 in the inner f64.
        assert_eq!(N5::new(0.0_f64).sin(), N5::new(0.0));
        assert!(N5::<f64>::NEG_INFINITY.sin().is_nan());
        assert!(N5::<f64>::INFINITY.sin().is_nan());
    }

    #[test]
    fn atan_endpoints_are_finite() {
        // atan has finite limits at ±∞: atan(-∞) = -π/2, atan(+∞) = π/2.
        assert_eq!(
            N5::<f64>::NEG_INFINITY.atan(),
            N5::new(-std::f64::consts::FRAC_PI_2)
        );
        assert_eq!(
            N5::<f64>::INFINITY.atan(),
            N5::new(std::f64::consts::FRAC_PI_2)
        );
    }

    #[test]
    fn exp_endpoints_f64() {
        assert_eq!(N5::<f64>::NEG_INFINITY.exp(), N5::new(0.0));
        assert_eq!(N5::<f64>::INFINITY.exp(), N5::<f64>::INFINITY);
    }

    #[test]
    fn sqrt_endpoints_f64() {
        assert_eq!(N5::<f64>::INFINITY.sqrt(), N5::<f64>::INFINITY);
        assert!(N5::<f64>::NEG_INFINITY.sqrt().is_nan());
    }

    #[test]
    fn ln_endpoints_f64() {
        assert!(N5::<f64>::NEG_INFINITY.ln().is_nan());
        assert_eq!(N5::<f64>::INFINITY.ln(), N5::<f64>::INFINITY);
    }

    #[test]
    fn abs_endpoints_to_top_f64() {
        assert_eq!(N5::<f64>::NEG_INFINITY.abs(), N5::<f64>::INFINITY);
        assert_eq!(N5::<f64>::INFINITY.abs(), N5::<f64>::INFINITY);
    }

    // ── T3: Additional From<integer> conversions ────────────────────

    #[test]
    fn from_i8_round_trips_f64() {
        let a: N5<f64> = (-3i8).into();
        assert_eq!(a, N5::new(-3.0));
    }

    #[test]
    fn from_i16_u16_round_trips_f64() {
        let a: N5<f64> = (-12345i16).into();
        assert_eq!(a, N5::new(-12345.0));
        let b: N5<f64> = 65535u16.into();
        assert_eq!(b, N5::new(65535.0));
    }

    #[test]
    fn from_i32_u32_round_trips_f64_only() {
        let a: N5<f64> = i32::MIN.into();
        assert_eq!(a, N5::new(i32::MIN as f64));
        let b: N5<f64> = u32::MAX.into();
        assert_eq!(b, N5::new(u32::MAX as f64));
    }

    #[test]
    fn from_inner_t_wraps_extend() {
        let a: N5<f32> = std::f32::consts::PI.into();
        assert_eq!(a, N5::new(std::f32::consts::PI));
        let b: N5<f64> = std::f64::consts::E.into();
        assert_eq!(b, N5::new(std::f64::consts::E));
    }
}

// ── solve_to_ceil step-count bound ───────────────────────────────────
//
// Plan-2026-05-08-05 Verification table: `solve_to_ceil` returns
// `steps ≤ 52` (= ⌈log₂(2 × 2⁵⁰)⌉ + 1) for any input. The bound is
// structural to the binary-search loop — it doesn't depend on the
// `$dst`/`$src`/`$widen`/etc. macro args — but exercising the macro
// here on a toy `i64`-ns rung is the cheapest way to lock the
// guarantee in `cargo test` (the per-Conn proptests in
// `time::duration` / `hifi::*` cover the production instantiations,
// and the Kani harnesses cover the bound formally on a slice; this
// test plugs the gap for `cargo test` without those features).
#[cfg(test)]
mod solve_step_bound_tests {
    use proptest::prelude::*;

    #[inline]
    fn shift_i64(n: i32, x: i64) -> i64 {
        x.saturating_add(n as i64)
    }

    #[inline]
    fn widen_i64_ns(x: i64) -> f64 {
        // Treat the i64 value as a count of nanoseconds; widen to
        // seconds so the comparison frame is float-seconds, mirroring
        // production instantiations.
        (x as f64) * 1e-9
    }

    #[inline]
    fn i64_to_ns(x: i64) -> i128 {
        x as i128
    }

    #[inline]
    fn i64_from_ns(n: i128) -> i64 {
        if n > i64::MAX as i128 {
            i64::MAX
        } else if n < i64::MIN as i128 {
            i64::MIN
        } else {
            n as i64
        }
    }

    crate::float::def_walk_helpers!(
        toy_ns_walks,
        f64,
        i64,
        shift_i64,
        widen_i64_ns,
        i64_to_ns,
        i64_from_ns
    );

    /// Helper: compute a production-shaped initial estimate for the
    /// toy `i64`-ns rung. Mirrors the way real callers seed the
    /// solver via `$dst::saturating_seconds_f$N`. Saturating because
    /// `i64::MAX` ns ≈ 9.22 × 10⁹ s; inputs larger than that are
    /// clamped at the rung's representable max, mimicking a real
    /// `from_secs_f64` saturating cast.
    #[inline]
    fn toy_start_from(x: f64) -> i64 {
        let n = (x * 1e9) as i128;
        if n > i64::MAX as i128 {
            i64::MAX
        } else if n < i64::MIN as i128 {
            i64::MIN
        } else {
            n as i64
        }
    }

    #[test]
    fn solve_to_ceil_step_bound_at_zero() {
        let (_z, steps) = toy_ns_walks::solve_to_ceil(0_i64, 0.0_f64);
        assert!(steps <= 52, "got {steps}");
    }

    #[test]
    fn solve_to_ceil_step_bound_at_high_magnitude() {
        // Production-shaped: `start ≈ from_secs_f64(x)`. At |x| ≈ 1e9
        // s the toy bracket of `±2⁵⁰` ns comfortably contains the
        // true ceil; the search runs ⌈log₂ 2⁵¹⌉ = 51 iterations.
        let x = 1.0e9_f64;
        let start = toy_start_from(x);
        let (_z, steps) = toy_ns_walks::solve_to_ceil(start, x);
        assert!(steps <= 52, "got {steps}");
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        // |x| ≤ 1e9 s keeps the toy-i64-ns instantiation away from
        // its `i64::MAX ns ≈ 9.22 × 10⁹ s` saturation rim, so
        // `toy_start_from(x)` produces a faithful initial estimate
        // and the bracket-correctness invariant
        // (`widen(from_ns(lo)) ≥ x` after the search) holds — the
        // same invariant the production callers rely on. The toy
        // never trips the `debug_assert` in `solve_to_ceil`.
        #[test]
        fn solve_to_ceil_step_bound_holds(x in -1.0e9_f64..1.0e9_f64) {
            let start = toy_start_from(x);
            let (_z, steps) = toy_ns_walks::solve_to_ceil(start, x);
            prop_assert!(steps <= 52, "got {steps}");
        }
    }
}
