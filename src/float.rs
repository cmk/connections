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
//! Per-destination-tier Conns live in submodules (right-hand side
//! wins under the placement rule when both endpoints sit at the same
//! specificity tier — see CLAUDE.md § Conn placement):
//!
//! - [`mod@f32`] — Conns whose target is `ExtendedFloat<f32>`
//!   (`F064F032`).
//! - `f16` — Conns whose target is `ExtendedFloat<f16>`
//!   (`F032F016`, `F064F016`) along with the `F016` type alias
//!   and 16-bit ULP machinery. Gated on the `f16` cargo feature
//!   (nightly required); the module name resolves only when the
//!   feature is enabled.

#[cfg(feature = "f16")]
pub mod f16;
pub mod f32;

use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

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
        impl PartialEq for $crate::float::ExtendedFloat<$T> {
            fn eq(&self, other: &Self) -> bool {
                use $crate::float::ExtendedFloat::*;
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

        impl PartialOrd for $crate::float::ExtendedFloat<$T> {
            fn partial_cmp(&self, other: &Self) -> Option<::core::cmp::Ordering> {
                use $crate::float::ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => Some(::core::cmp::Ordering::Equal),
                    (Bot, _) => Some(::core::cmp::Ordering::Less),
                    (_, Bot) => Some(::core::cmp::Ordering::Greater),
                    (_, Top) => Some(::core::cmp::Ordering::Less),
                    (Top, _) => Some(::core::cmp::Ordering::Greater),
                    (Extend(a), Extend(b)) => {
                        if a.is_nan() && b.is_nan() {
                            Some(::core::cmp::Ordering::Equal)
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
        impl Eq for $crate::float::ExtendedFloat<$T> {}
    };
}

pub(crate) use impl_float_ext;

impl_float_ext!(f32);
impl_float_ext!(f64);

// ── Numeric impls for `ExtendedFloat<f32 | f64>`.
//
// The Extend × Extend arms route through the inner T's arithmetic.
// The Bot/Top arms follow a conservative simplification rule:
// `Add`/`Sub`/`Neg` preserve the lattice endpoints when the result
// is unambiguous (e.g. `Bot + Bot = Bot`, `-Bot = Top`); every other
// Bot/Top combination collapses to `Extend(NaN)`. The chain
// combinators in `crate::conn` (`interval`/`midpoint`/`round`/
// `truncate`) only ever pass `Extend(_)` brackets to these ops, so
// the simplification has no effect on in-tree usage; deterministic
// tests in `mod tests` pin the Bot/Top arms for direct callers.
//
// | Op | (Bot, Bot)  | (Top, Top)  | mixed Bot/Top   | endpoint, Extend(_) | (Extend(a), Extend(b)) |
// |----|-------------|-------------|-----------------|---------------------|------------------------|
// |  + |  Bot        |  Top        |  Extend(NaN)    |  endpoint absorbs   |  Extend(a + b)         |
// |  - |  Extend(NaN)|  Extend(NaN)|  endpoint of LHS|  endpoint of LHS;   |  Extend(a - b)         |
// |    |             |             |                 |  flipped for Extend |                        |
// |  * |  Extend(NaN)|  Extend(NaN)|  Extend(NaN)    |  Extend(NaN)        |  Extend(a * b)         |
// |  / |  Extend(NaN)|  Extend(NaN)|  Extend(NaN)    |  Extend(NaN)        |  Extend(a / b)         |
// |  % |  Extend(NaN)|  Extend(NaN)|  Extend(NaN)    |  Extend(NaN)        |  Extend(a % b)         |
// | -x | Top (Bot)   | Bot (Top)   | —               | —                   |  Extend(-a)            |
//
// `From<u8>(n)` always returns `Extend(T::from(n))`.
//
// `*Assign` impls all delegate to the by-value op (`*self = (*self) op other`).
// User-facing transcendentals (`sin`, `cos`, `sqrt`, etc.) are inherent
// methods on `ExtendedFloat<f32 | f64>` further below.

macro_rules! impl_float_arith {
    ($T:ident) => {
        impl Add for ExtendedFloat<$T> {
            type Output = Self;
            fn add(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) => Bot,
                    (Top, Top) => Top,
                    (Bot, Top) | (Top, Bot) => Extend(<$T>::NAN),
                    (Bot, Extend(_)) | (Extend(_), Bot) => Bot,
                    (Top, Extend(_)) | (Extend(_), Top) => Top,
                    (Extend(a), Extend(b)) => Extend(a + b),
                }
            }
        }

        impl Sub for ExtendedFloat<$T> {
            type Output = Self;
            fn sub(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => Extend(<$T>::NAN),
                    (Bot, Top) => Bot,
                    (Top, Bot) => Top,
                    (Bot, Extend(_)) => Bot,
                    (Top, Extend(_)) => Top,
                    (Extend(_), Bot) => Top,
                    (Extend(_), Top) => Bot,
                    (Extend(a), Extend(b)) => Extend(a - b),
                }
            }
        }

        impl Mul for ExtendedFloat<$T> {
            type Output = Self;
            fn mul(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    (Extend(a), Extend(b)) => Extend(a * b),
                    _ => Extend(<$T>::NAN),
                }
            }
        }

        impl Div for ExtendedFloat<$T> {
            type Output = Self;
            fn div(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    (Extend(a), Extend(b)) => Extend(a / b),
                    _ => Extend(<$T>::NAN),
                }
            }
        }

        impl Rem for ExtendedFloat<$T> {
            type Output = Self;
            fn rem(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    (Extend(a), Extend(b)) => Extend(a % b),
                    _ => Extend(<$T>::NAN),
                }
            }
        }

        impl Neg for ExtendedFloat<$T> {
            type Output = Self;
            fn neg(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot => Top,
                    Top => Bot,
                    Extend(a) => Extend(-a),
                }
            }
        }

        impl AddAssign for ExtendedFloat<$T> {
            fn add_assign(&mut self, other: Self) { *self = *self + other; }
        }
        impl SubAssign for ExtendedFloat<$T> {
            fn sub_assign(&mut self, other: Self) { *self = *self - other; }
        }
        impl MulAssign for ExtendedFloat<$T> {
            fn mul_assign(&mut self, other: Self) { *self = *self * other; }
        }
        impl DivAssign for ExtendedFloat<$T> {
            fn div_assign(&mut self, other: Self) { *self = *self / other; }
        }
        impl RemAssign for ExtendedFloat<$T> {
            fn rem_assign(&mut self, other: Self) { *self = *self % other; }
        }

        impl From<u8> for ExtendedFloat<$T> {
            fn from(n: u8) -> Self {
                ExtendedFloat::Extend(<$T>::from(n))
            }
        }

        impl From<i8> for ExtendedFloat<$T> {
            fn from(n: i8) -> Self {
                ExtendedFloat::Extend(<$T>::from(n))
            }
        }

        impl From<i16> for ExtendedFloat<$T> {
            fn from(n: i16) -> Self {
                ExtendedFloat::Extend(<$T>::from(n))
            }
        }

        impl From<u16> for ExtendedFloat<$T> {
            fn from(n: u16) -> Self {
                ExtendedFloat::Extend(<$T>::from(n))
            }
        }

        impl From<$T> for ExtendedFloat<$T> {
            fn from(v: $T) -> Self {
                ExtendedFloat::Extend(v)
            }
        }

        impl ExtendedFloat<$T> {
            pub const PI: Self = ExtendedFloat::Extend(::core::$T::consts::PI);
            pub const TAU: Self = ExtendedFloat::Extend(::core::$T::consts::TAU);
            pub const E: Self = ExtendedFloat::Extend(::core::$T::consts::E);
            pub const FRAC_PI_2: Self = ExtendedFloat::Extend(::core::$T::consts::FRAC_PI_2);
            pub const NAN: Self = ExtendedFloat::Extend(<$T>::NAN);
            pub const INFINITY: Self = ExtendedFloat::Top;
            pub const NEG_INFINITY: Self = ExtendedFloat::Bot;
            pub const ZERO: Self = ExtendedFloat::Extend(0.0);
            pub const ONE: Self = ExtendedFloat::Extend(1.0);

            /// `true` iff `self` is `Extend(v)` with `v.is_nan()`.
            /// `Bot` and `Top` are the lattice's synthetic endpoints
            /// and report `false`.
            pub fn is_nan(self) -> bool {
                matches!(self, ExtendedFloat::Extend(v) if v.is_nan())
            }

            /// `true` iff `self` is `Extend(v)` with `v.is_finite()`.
            /// `Bot` / `Top` and `Extend(±∞)` / `Extend(NaN)` report
            /// `false`.
            pub fn is_finite(self) -> bool {
                matches!(self, ExtendedFloat::Extend(v) if v.is_finite())
            }

            /// `true` iff `self` is `Bot`, `Top`, or `Extend(±∞)`. The
            /// lattice has *two* infinity-like elements per side
            /// (synthetic and IEEE); both report infinite.
            pub fn is_infinite(self) -> bool {
                use ExtendedFloat::*;
                match self {
                    Bot | Top => true,
                    Extend(v) => v.is_infinite(),
                }
            }

            // ── Transcendentals + utilities ───────────────────────────
            //
            // Each method dispatches on the lattice variant: Extend(v)
            // routes through the inner T's method; Bot/Top arms apply
            // the function's limit at ±∞ where it's well-defined and
            // collapse to `Extend(NaN)` where it isn't (sin/cos/tan
            // oscillate at infinity; sqrt(-∞) is undefined).

            pub fn abs(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot | Top => Top,
                    Extend(v) => Extend(v.abs()),
                }
            }

            pub fn signum(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot => Extend(-1.0),
                    Top => Extend(1.0),
                    Extend(v) => Extend(v.signum()),
                }
            }

            pub fn recip(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot | Top => Extend(0.0),
                    Extend(v) => Extend(v.recip()),
                }
            }

            pub fn sqrt(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot => Extend(<$T>::NAN),
                    Top => Top,
                    Extend(v) => Extend(v.sqrt()),
                }
            }

            pub fn cbrt(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot => Bot,
                    Top => Top,
                    Extend(v) => Extend(v.cbrt()),
                }
            }

            pub fn sin(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot | Top => Extend(<$T>::NAN),
                    Extend(v) => Extend(v.sin()),
                }
            }

            pub fn cos(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot | Top => Extend(<$T>::NAN),
                    Extend(v) => Extend(v.cos()),
                }
            }

            pub fn tan(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot | Top => Extend(<$T>::NAN),
                    Extend(v) => Extend(v.tan()),
                }
            }

            pub fn asin(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot | Top => Extend(<$T>::NAN),
                    Extend(v) => Extend(v.asin()),
                }
            }

            pub fn acos(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot | Top => Extend(<$T>::NAN),
                    Extend(v) => Extend(v.acos()),
                }
            }

            pub fn atan(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot => Extend(-::core::$T::consts::FRAC_PI_2),
                    Top => Extend(::core::$T::consts::FRAC_PI_2),
                    Extend(v) => Extend(v.atan()),
                }
            }

            /// `atan2(y, x)`. Routes through the inner T when both
            /// operands are `Extend(_)`; any `Bot`/`Top` argument
            /// collapses the result to `Extend(NaN)` (atan2's two-argument
            /// limit at infinity is direction-dependent and not the
            /// kind of corner case in-tree callers want to lean on).
            pub fn atan2(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    (Extend(y), Extend(x)) => Extend(y.atan2(x)),
                    _ => Extend(<$T>::NAN),
                }
            }

            pub fn exp(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot => Extend(0.0),
                    Top => Top,
                    Extend(v) => Extend(v.exp()),
                }
            }

            pub fn exp2(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot => Extend(0.0),
                    Top => Top,
                    Extend(v) => Extend(v.exp2()),
                }
            }

            pub fn ln(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot => Extend(<$T>::NAN),
                    Top => Top,
                    Extend(v) => Extend(v.ln()),
                }
            }

            pub fn log2(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot => Extend(<$T>::NAN),
                    Top => Top,
                    Extend(v) => Extend(v.log2()),
                }
            }

            pub fn log10(self) -> Self {
                use ExtendedFloat::*;
                match self {
                    Bot => Extend(<$T>::NAN),
                    Top => Top,
                    Extend(v) => Extend(v.log10()),
                }
            }

            /// Integer power. Only defined for `Extend(_)` operands;
            /// `Bot`/`Top` collapse to `Extend(NaN)` since `powi` is
            /// sign-and-parity-sensitive at infinity in ways most
            /// callers don't want as a default.
            pub fn powi(self, n: i32) -> Self {
                use ExtendedFloat::*;
                match self {
                    Extend(v) => Extend(v.powi(n)),
                    _ => Extend(<$T>::NAN),
                }
            }

            /// Float power. Only defined for `(Extend, Extend)`;
            /// any endpoint operand collapses to `Extend(NaN)`.
            pub fn powf(self, p: Self) -> Self {
                use ExtendedFloat::*;
                match (self, p) {
                    (Extend(v), Extend(q)) => Extend(v.powf(q)),
                    _ => Extend(<$T>::NAN),
                }
            }

            /// Fused multiply-add. Only defined for all-`Extend`;
            /// any endpoint operand collapses to `Extend(NaN)`.
            pub fn mul_add(self, a: Self, b: Self) -> Self {
                use ExtendedFloat::*;
                match (self, a, b) {
                    (Extend(s), Extend(x), Extend(y)) => Extend(s.mul_add(x, y)),
                    _ => Extend(<$T>::NAN),
                }
            }
        }
    };
}

impl_float_arith!(f32);
impl_float_arith!(f64);

// f64-only `From<i32>` / `From<u32>` (lossless casts; i32/u32 don't
// fit in f32's 24-bit mantissa).
impl From<i32> for ExtendedFloat<f64> {
    fn from(n: i32) -> Self {
        ExtendedFloat::Extend(f64::from(n))
    }
}
impl From<u32> for ExtendedFloat<f64> {
    fn from(n: u32) -> Self {
        ExtendedFloat::Extend(f64::from(n))
    }
}

/// IEEE binary32 wrapped under the N5 lattice.
pub type F032 = ExtendedFloat<f32>;

/// IEEE binary64 wrapped under the N5 lattice.
pub type F064 = ExtendedFloat<f64>;

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

/// Generate the four ULP-walk helpers (`ascend_to_ceil`,
/// `descend_to_ceil`, `ascend_to_floor`, `descend_to_floor`) for one
/// `Src → Dst` precision-narrowing Conn, packaged in a private
/// submodule named `$mod_name`.
///
/// Each helper returns `(Dst, u32)` — the corrected target value and
/// the number of ULP-shift iterations consumed. Production callers
/// throw the count away (`let (z, _) = …`); the `ulp_steps_bounded`
/// proptest reads it to assert the loop converges in ≤ 2 iterations.
///
/// Parameters:
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
/// The generated module's helpers are `pub(super)` — visible to the
/// owning Conn's `ceil`/`floor` functions and to `#[cfg(test)]` code
/// in the same parent file, but not exposed beyond.
macro_rules! def_walk_helpers {
    ($mod_name:ident, $src:ty, $dst:ty, $shift:path, $widen:path) => {
        mod $mod_name {
            #[allow(unused_imports)]
            use super::*;

            /// Walk up (toward +∞) until `widen(z) >= x`, returning `(z, steps)`.
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
        }
    };
}

pub(crate) use def_walk_helpers;

#[cfg(test)]
mod tests {
    use super::*;

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

    // ── ExtendedFloat tests ────────────────────────────────────────

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
            Some(core::cmp::Ordering::Equal)
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

    // ── Numeric impls for ExtendedFloat<f32 | f64> ────────────────

    #[test]
    fn add_extends_passes_through_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(1.5);
        let b: ExtendedFloat<f64> = ExtendedFloat::Extend(2.25);
        assert_eq!(a + b, ExtendedFloat::Extend(3.75));
    }

    #[test]
    fn sub_zero_is_id_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(std::f64::consts::PI);
        let zero: ExtendedFloat<f64> = ExtendedFloat::from(0u8);
        assert_eq!(a - zero, a);
    }

    #[test]
    fn div_by_two_halves_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(8.0);
        let two: ExtendedFloat<f64> = ExtendedFloat::from(2u8);
        assert_eq!(a / two, ExtendedFloat::Extend(4.0));
    }

    #[test]
    fn from_u8_round_trips_f32_f64() {
        for n in [0u8, 1, 2, 7, 42, u8::MAX] {
            assert_eq!(
                ExtendedFloat::<f64>::from(n),
                ExtendedFloat::Extend(n as f64)
            );
            assert_eq!(
                ExtendedFloat::<f32>::from(n),
                ExtendedFloat::Extend(n as f32)
            );
        }
    }

    #[test]
    fn add_endpoints_absorb() {
        let bot: ExtendedFloat<f64> = ExtendedFloat::Bot;
        let top: ExtendedFloat<f64> = ExtendedFloat::Top;
        let one: ExtendedFloat<f64> = ExtendedFloat::Extend(1.0);
        assert_eq!(bot + one, ExtendedFloat::Bot);
        assert_eq!(top + one, ExtendedFloat::Top);
        assert_eq!(bot + bot, ExtendedFloat::Bot);
        assert_eq!(top + top, ExtendedFloat::Top);
        // Mixed Bot/Top is undefined → NaN payload.
        match bot + top {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            other => panic!("expected Extend(NaN), got {other:?}"),
        }
    }

    #[test]
    fn sub_extends_passes_through_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(5.5);
        let b: ExtendedFloat<f64> = ExtendedFloat::Extend(1.25);
        assert_eq!(a - b, ExtendedFloat::Extend(4.25));
    }

    // ── T1: Mul / Neg / Rem + *Assign ─────────────────────────────

    #[test]
    fn mul_extends_passes_through_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(2.5);
        let b: ExtendedFloat<f64> = ExtendedFloat::Extend(4.0);
        assert_eq!(a * b, ExtendedFloat::Extend(10.0));
    }

    #[test]
    fn neg_double_is_id_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(std::f64::consts::PI);
        assert_eq!(-(-a), a);
    }

    #[test]
    fn neg_endpoints_flip() {
        assert_eq!(-ExtendedFloat::<f64>::Bot, ExtendedFloat::Top);
        assert_eq!(-ExtendedFloat::<f64>::Top, ExtendedFloat::Bot);
        let one: ExtendedFloat<f64> = ExtendedFloat::Extend(1.0);
        assert_eq!(-one, ExtendedFloat::Extend(-1.0));
    }

    #[test]
    fn rem_zero_pin_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(7.5);
        let zero: ExtendedFloat<f64> = ExtendedFloat::Extend(0.0);
        // f64 7.5 % 0.0 produces NaN; the lattice impl mirrors that.
        match a % zero {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            other => panic!("expected Extend(NaN), got {other:?}"),
        }
    }

    #[test]
    fn rem_endpoint_pin_f64() {
        // Any Bot/Top arm collapses to Extend(NaN), matching the
        // documented conservative simplification.
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(7.5);
        match a % ExtendedFloat::<f64>::Top {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            other => panic!("expected Extend(NaN), got {other:?}"),
        }
    }

    #[test]
    fn add_assign_matches_add_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(3.5);
        let b: ExtendedFloat<f64> = ExtendedFloat::Extend(1.25);
        let by_value = a + b;
        let mut by_assign = a;
        by_assign += b;
        assert_eq!(by_assign, by_value);
    }

    #[test]
    fn sub_assign_matches_sub_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(3.5);
        let b: ExtendedFloat<f64> = ExtendedFloat::Extend(1.25);
        let by_value = a - b;
        let mut by_assign = a;
        by_assign -= b;
        assert_eq!(by_assign, by_value);
    }

    #[test]
    fn mul_assign_matches_mul_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(3.0);
        let b: ExtendedFloat<f64> = ExtendedFloat::Extend(4.0);
        let by_value = a * b;
        let mut by_assign = a;
        by_assign *= b;
        assert_eq!(by_assign, by_value);
    }

    #[test]
    fn div_assign_matches_div_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(8.0);
        let b: ExtendedFloat<f64> = ExtendedFloat::Extend(2.0);
        let by_value = a / b;
        let mut by_assign = a;
        by_assign /= b;
        assert_eq!(by_assign, by_value);
    }

    #[test]
    fn rem_assign_matches_rem_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(7.5);
        let b: ExtendedFloat<f64> = ExtendedFloat::Extend(2.0);
        let by_value = a % b;
        let mut by_assign = a;
        by_assign %= b;
        assert_eq!(by_assign, by_value);
    }

    // ── T2: Inherent transcendentals + constants + predicates ─────

    #[test]
    fn pi_constant_round_trips_f32_f64() {
        assert_eq!(
            ExtendedFloat::<f32>::PI,
            ExtendedFloat::Extend(std::f32::consts::PI)
        );
        assert_eq!(
            ExtendedFloat::<f64>::PI,
            ExtendedFloat::Extend(std::f64::consts::PI)
        );
    }

    #[test]
    fn nan_infinity_constants_f64() {
        assert!(ExtendedFloat::<f64>::NAN.is_nan());
        assert_eq!(ExtendedFloat::<f64>::INFINITY, ExtendedFloat::<f64>::Top);
        assert_eq!(
            ExtendedFloat::<f64>::NEG_INFINITY,
            ExtendedFloat::<f64>::Bot
        );
        assert_eq!(ExtendedFloat::<f64>::ZERO, ExtendedFloat::Extend(0.0));
        assert_eq!(ExtendedFloat::<f64>::ONE, ExtendedFloat::Extend(1.0));
    }

    #[test]
    fn predicates_classify_correctly_f64() {
        let bot = ExtendedFloat::<f64>::Bot;
        let top = ExtendedFloat::<f64>::Top;
        let nan = ExtendedFloat::<f64>::NAN;
        let pi = ExtendedFloat::<f64>::PI;
        let inf = ExtendedFloat::Extend(f64::INFINITY);

        assert!(!bot.is_nan() && !top.is_nan() && nan.is_nan() && !pi.is_nan());
        assert!(!bot.is_finite() && !top.is_finite() && !nan.is_finite() && pi.is_finite());
        assert!(bot.is_infinite() && top.is_infinite() && !pi.is_infinite() && inf.is_infinite());
    }

    #[test]
    fn sin_extends_passes_through_f64() {
        // sin(0) is exactly 0 in the inner f64.
        assert_eq!(
            ExtendedFloat::Extend(0.0_f64).sin(),
            ExtendedFloat::Extend(0.0)
        );
        // sin's value at endpoints isn't well-defined; it should NaN.
        assert!(ExtendedFloat::<f64>::Bot.sin().is_nan());
        assert!(ExtendedFloat::<f64>::Top.sin().is_nan());
    }

    #[test]
    fn atan_endpoints_are_finite() {
        // atan has finite limits at ±∞: atan(-∞) = -π/2, atan(+∞) = π/2.
        assert_eq!(
            ExtendedFloat::<f64>::Bot.atan(),
            ExtendedFloat::Extend(-std::f64::consts::FRAC_PI_2)
        );
        assert_eq!(
            ExtendedFloat::<f64>::Top.atan(),
            ExtendedFloat::Extend(std::f64::consts::FRAC_PI_2)
        );
    }

    #[test]
    fn exp_endpoints_f64() {
        assert_eq!(
            ExtendedFloat::<f64>::Bot.exp(),
            ExtendedFloat::Extend(0.0)
        );
        assert_eq!(ExtendedFloat::<f64>::Top.exp(), ExtendedFloat::<f64>::Top);
    }

    #[test]
    fn sqrt_endpoints_f64() {
        assert_eq!(ExtendedFloat::<f64>::Top.sqrt(), ExtendedFloat::<f64>::Top);
        assert!(ExtendedFloat::<f64>::Bot.sqrt().is_nan());
    }

    #[test]
    fn ln_endpoints_f64() {
        assert!(ExtendedFloat::<f64>::Bot.ln().is_nan());
        assert_eq!(ExtendedFloat::<f64>::Top.ln(), ExtendedFloat::<f64>::Top);
    }

    #[test]
    fn abs_endpoints_to_top_f64() {
        assert_eq!(ExtendedFloat::<f64>::Bot.abs(), ExtendedFloat::<f64>::Top);
        assert_eq!(ExtendedFloat::<f64>::Top.abs(), ExtendedFloat::<f64>::Top);
    }

    // ── T3: Additional From<integer> conversions ────────────────────

    #[test]
    fn from_i8_round_trips_f64() {
        let a: ExtendedFloat<f64> = (-3i8).into();
        assert_eq!(a, ExtendedFloat::Extend(-3.0));
    }

    #[test]
    fn from_i16_u16_round_trips_f64() {
        let a: ExtendedFloat<f64> = (-12345i16).into();
        assert_eq!(a, ExtendedFloat::Extend(-12345.0));
        let b: ExtendedFloat<f64> = 65535u16.into();
        assert_eq!(b, ExtendedFloat::Extend(65535.0));
    }

    #[test]
    fn from_i32_u32_round_trips_f64_only() {
        let a: ExtendedFloat<f64> = i32::MIN.into();
        assert_eq!(a, ExtendedFloat::Extend(i32::MIN as f64));
        let b: ExtendedFloat<f64> = u32::MAX.into();
        assert_eq!(b, ExtendedFloat::Extend(u32::MAX as f64));
    }

    #[test]
    fn from_inner_t_wraps_extend() {
        let a: ExtendedFloat<f32> = std::f32::consts::PI.into();
        assert_eq!(a, ExtendedFloat::Extend(std::f32::consts::PI));
        let b: ExtendedFloat<f64> = std::f64::consts::E.into();
        assert_eq!(b, ExtendedFloat::Extend(std::f64::consts::E));
    }
}
