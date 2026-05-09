//! IEEE float Conns built on [`ExtendedFloat<T>`], an N5-lattice
//! extension of an IEEE float that recovers a total-enough preorder
//! for the Galois-connection machinery to apply.
//!
//! ## Constants
//!
//! Peer float Conns live with their source side after semantic
//! specificity is considered:
//!
//! | Const          | Conn                                  | Module       |
//! |----------------|---------------------------------------|--------------|
//! | `F064F032`     | `Conn<F064, F032>` (lossy narrowing)  | [`mod@f064`] |
//! | `F064F016`     | `Conn<F064, F016>` (`f16` feature)    | `f064`       |
//! | `F032F016`     | `Conn<F032, F016>` (`f16` feature)    | `f032`       |
//!
//! ## Example
//!
//! ```rust
//! use connections::conn::{ConnL, ConnR};  // brings .ceil/.floor in via default methods
//! use connections::float::f064::F064F032;
//! use connections::float::F064;
//!
//! // f64 → f32 narrowing rounds in two directions.
//! let pi64 = F064::Extend(std::f64::consts::PI);
//! let lo = F064F032.floor(pi64);   // largest f32 ≤ π
//! let hi = F064F032.ceil(pi64);    // smallest f32 ≥ π
//! assert!(lo != hi);               // π is not exactly representable in f32
//! ```
//!
//! ## Why ExtendedFloat?
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

#[cfg(feature = "f16")]
pub mod f016;
pub mod f032;
pub mod f064;

use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

/// Three-element extension of a (possibly partial) order:
/// `Bot < Extend(_) < Top`.
///
/// `ExtendedFloat<T>` represents `Maybe R̄` — the extended real line
/// `R̄ = R ∪ {-∞, +∞}` plus an undefined / NaN slot. Concretely
/// `Bot` ↔ `-∞`, `Top` ↔ `+∞`, and `Extend(v)` wraps any real
/// (or IEEE NaN). The arithmetic impls below give every Bot/Top
/// arm its extended-real-line answer; see the table above
/// `impl_float_arith!` for the full per-op dispatch.
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

// Generic `impl<T>` block — the catamorphism extractors don't touch
// inner-T arithmetic, so they live outside the per-T
// `impl_float_arith!` macro below and apply to any `ExtendedFloat<T>`.
impl<T> ExtendedFloat<T> {
    /// Catamorphism: collapse an `ExtendedFloat<T>` to a `U` by
    /// supplying one value per variant.
    ///
    /// The Rust analogue of Haskell's
    /// `extendedFloat :: ExtendedFloat a -> b -> b -> (a -> b) -> b`.
    /// Argument order follows Rust's closure-last convention
    /// (`Iterator::fold`, `Option::map_or`).
    ///
    /// Endpoint arms are evaluated eagerly. For lazy endpoints, see
    /// [`ExtendedFloat::fold_with`].
    ///
    /// ```
    /// use connections::float::ExtendedFloat;
    ///
    /// fn classify(x: ExtendedFloat<f64>) -> &'static str {
    ///     x.fold("below", "above", |_| "in range")
    /// }
    /// assert_eq!(classify(ExtendedFloat::Bot), "below");
    /// assert_eq!(classify(ExtendedFloat::Extend(1.5)), "in range");
    /// assert_eq!(classify(ExtendedFloat::Top), "above");
    /// ```
    pub fn fold<U>(self, bot: U, top: U, f: impl FnOnce(T) -> U) -> U {
        match self {
            ExtendedFloat::Bot => bot,
            ExtendedFloat::Extend(t) => f(t),
            ExtendedFloat::Top => top,
        }
    }

    /// Lazy variant of [`ExtendedFloat::fold`]: all three arms are
    /// wrapped in [`FnOnce`] closures and only the matched arm is
    /// called. Use when any endpoint default is expensive to compute.
    pub fn fold_with<U>(
        self,
        bot: impl FnOnce() -> U,
        top: impl FnOnce() -> U,
        f: impl FnOnce(T) -> U,
    ) -> U {
        match self {
            ExtendedFloat::Bot => bot(),
            ExtendedFloat::Extend(t) => f(t),
            ExtendedFloat::Top => top(),
        }
    }
}

// ── Numeric impls for `ExtendedFloat<f32 | f64>`.
//
// `ExtendedFloat<T>` represents `Maybe R̄` — the extended real line
// `R̄ = R ∪ {-∞, +∞}` with `Extend(NaN)` standing in for the
// undefined / "Nothing" case. Concretely:
//
//   Bot     ↔  -∞
//   Extend  ↔  any finite real (or IEEE NaN, the undefined case)
//   Top     ↔  +∞
//
// The arithmetic dispatches on this reading: the Extend × Extend
// arm routes through the inner T's IEEE arithmetic; every Bot/Top
// arm computes the extended-real-line answer rather than punting
// to `Extend(NaN)`. Returning NaN from two non-NaN inputs when the
// answer is unambiguous would be lossy; we don't.
//
// Operation table under `Bot = -∞, Top = +∞`. NaN inputs in any
// `Extend(v)` arm propagate to `Extend(NaN)` per IEEE (the cells
// below describe the *non-NaN* case for the finite operand).
//
// | Op | (Bot, Bot) | (Top, Top) | (Bot, Top) | (Top, Bot) | (Bot, Extend(v))                     | (Top, Extend(v))                     | (Extend(v), Bot)                                | (Extend(v), Top)                                | (Extend(a), Extend(b)) |
// |----|-----------|-----------|-----------|-----------|--------------------------------------|--------------------------------------|-------------------------------------------------|-------------------------------------------------|------------------------|
// |  + | Bot       | Top       | NaN       | NaN       | Bot (NaN if v is NaN)                | Top (NaN if v is NaN)                | Bot (NaN if v is NaN)                           | Top (NaN if v is NaN)                           | Extend(a + b)          |
// |  - | NaN       | NaN       | Bot       | Top       | Bot (NaN if v is NaN)                | Top (NaN if v is NaN)                | Top (NaN if v is NaN)                           | Bot (NaN if v is NaN)                           | Extend(a - b)          |
// |  * | Top       | Top       | Bot       | Bot       | sign-of-v: Bot/Top/NaN at +/-/0/NaN  | sign-of-v: Top/Bot/NaN at +/-/0/NaN  | sign-of-v: Bot/Top/NaN at +/-/0/NaN             | sign-of-v: Top/Bot/NaN at +/-/0/NaN             | Extend(a * b)          |
// |  / | NaN       | NaN       | NaN       | NaN       | sign-of-v: Bot/Top/NaN at +/-/0/NaN  | sign-of-v: Top/Bot/NaN at +/-/0/NaN  | finite / ∞ = ±0 (IEEE signed zero); NaN→NaN     | finite / ∞ = ±0 (IEEE signed zero); NaN→NaN     | Extend(a / b)          |
// |  % | NaN       | NaN       | NaN       | NaN       | NaN                                  | NaN                                  | Extend(v) — passes NaN through (finite mod ∞=v) | Extend(v) — passes NaN through (finite mod ∞=v) | Extend(a % b)          |
// | -x | Top       | Bot       | —         | —         | —                                    | —                                    | —                                               | —                                               | Extend(-a)             |
//
// NaN propagation: IEEE 754 requires `NaN op anything = NaN`
// regardless of operand magnitude. The N5 lattice's order-theoretic
// fact that `Extend(NaN)` sits between Bot and Top (via the
// synthetic-endpoint rule) governs `partial_cmp` / lub / glb only;
// it has nothing to say about arithmetic. So IEEE is the sole
// guide here, and each `Extend(v)` arm in Add and Sub inspects
// `v.is_nan()` first — if true, the result is `Extend(NaN)`; if
// not, the endpoint absorption rule fires (Bot + finite = Bot,
// etc.). No "lattice vs IEEE" tradeoff — they apply to different
// operations.
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
                    // NaN propagates through endpoint absorption (IEEE).
                    (Bot, Extend(v)) | (Extend(v), Bot) => {
                        if v.is_nan() { Extend(<$T>::NAN) } else { Bot }
                    }
                    (Top, Extend(v)) | (Extend(v), Top) => {
                        if v.is_nan() { Extend(<$T>::NAN) } else { Top }
                    }
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
                    // NaN propagates (IEEE), else endpoint absorbs.
                    (Bot, Extend(v)) => {
                        if v.is_nan() { Extend(<$T>::NAN) } else { Bot }
                    }
                    (Top, Extend(v)) => {
                        if v.is_nan() { Extend(<$T>::NAN) } else { Top }
                    }
                    (Extend(v), Bot) => {
                        if v.is_nan() { Extend(<$T>::NAN) } else { Top }
                    }
                    (Extend(v), Top) => {
                        if v.is_nan() { Extend(<$T>::NAN) } else { Bot }
                    }
                    (Extend(a), Extend(b)) => Extend(a - b),
                }
            }
        }

        impl Mul for ExtendedFloat<$T> {
            type Output = Self;
            fn mul(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    // Same-sign endpoints: (-∞)·(-∞) = (+∞)·(+∞) = +∞.
                    (Bot, Bot) | (Top, Top) => Top,
                    // Opposite-sign endpoints: (-∞)·(+∞) = -∞.
                    (Bot, Top) | (Top, Bot) => Bot,
                    // Endpoint × Extend: dispatch on the finite operand's
                    // sign. Zero / NaN make the product NaN per IEEE.
                    (Bot, Extend(v)) | (Extend(v), Bot) => {
                        if v > 0.0 { Bot } else if v < 0.0 { Top } else { Extend(<$T>::NAN) }
                    }
                    (Top, Extend(v)) | (Extend(v), Top) => {
                        if v > 0.0 { Top } else if v < 0.0 { Bot } else { Extend(<$T>::NAN) }
                    }
                    (Extend(a), Extend(b)) => Extend(a * b),
                }
            }
        }

        impl Div for ExtendedFloat<$T> {
            type Output = Self;
            fn div(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    // ∞/∞ is genuinely indeterminate per IEEE.
                    (Bot, Bot) | (Top, Top) | (Bot, Top) | (Top, Bot) => Extend(<$T>::NAN),
                    // Endpoint / Extend: sign of the finite operand picks
                    // the result endpoint.
                    (Bot, Extend(v)) => {
                        if v > 0.0 { Bot } else if v < 0.0 { Top } else { Extend(<$T>::NAN) }
                    }
                    (Top, Extend(v)) => {
                        if v > 0.0 { Top } else if v < 0.0 { Bot } else { Extend(<$T>::NAN) }
                    }
                    // finite / ∞ = 0 per IEEE (sign by signed-zero rule);
                    // route through the inner T's Div with the sign-bearing
                    // infinity so the IEEE result is preserved.
                    (Extend(v), Bot) => Extend(v / <$T>::NEG_INFINITY),
                    (Extend(v), Top) => Extend(v / <$T>::INFINITY),
                    (Extend(a), Extend(b)) => Extend(a / b),
                }
            }
        }

        impl Rem for ExtendedFloat<$T> {
            type Output = Self;
            fn rem(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    // ∞ % anything is NaN per IEEE.
                    (Bot, _) | (Top, _) => Extend(<$T>::NAN),
                    // finite % ∞ = the finite per IEEE — the divisor is
                    // larger in magnitude than any finite, so the
                    // remainder is the dividend itself.
                    (Extend(v), Bot) | (Extend(v), Top) => Extend(v),
                    (Extend(a), Extend(b)) => Extend(a % b),
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
        crate::float::f016::shift16_f16(-1, approx)
    } else {
        approx
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
// - `ExtendedFloat::Bot`            → `Extended::NegInf`  (pass-through)
// - `ExtendedFloat::Top`            → `Extended::PosInf`  (pass-through)
// - `Extend(v)` with `v.is_nan()`   → `PosInf` on `ceil`, `NegInf` on `floor`
// - `Extend(NEG_INFINITY)`          → `NegInf`
// - `Extend(INFINITY)`              → `PosInf`
// - `Extend(v)` with `v >  hi`      → `PosInf` (ceil) /  `Finite(<int>::MAX)` (floor)
// - `Extend(v)` with `v <  lo`      → `Finite(<int>::MIN)` (ceil) / `NegInf` (floor)
// - `Extend(v)` with `lo ≤ v ≤ hi`  → `Finite(v.ceil() as int)` / `Finite(v.floor() as int)`
//
// `inner` always materialises a finite float for `Finite(i)` and
// emits ±INFINITY for `NegInf` / `PosInf` (matching Haskell's
// `extended (-1/0) (1/0) fromIntegral` at Float.hs:398).
//
// The `floor ≤ ceil` invariant holds in every branch by construction.

#[doc(hidden)]
#[macro_export]
macro_rules! __float_ext_int_ceil_body {
    ($float:ty, $int:ty, $v:ident) => {{
        // NaN: incomparable with every finite Extend(_), and with Bot;
        // ≤ Top in the N5 order. So ceil(Extend(NaN)) = PosInf (the
        // smallest b such that upper(b) ≥ Extend(NaN)).
        if $v.is_nan() {
            $crate::extended::Extended::PosInf
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
            // For `Extend(-∞)` the routing splits by source mantissa
            // vs target width. With a finite `lo` (f32/f64 sources, or
            // f16 sources with `i8`/`u8` targets) the `v < lo` arm
            // fires and returns `Finite(MIN)`. With a saturated `lo`
            // (f16 sources with `i16+`/`u16+` targets, where
            // `<$int>::MIN as f16 = -∞`) the comparison `-∞ < -∞`
            // is `false`, so execution falls through to the `else`
            // arm; Rust's saturating float-to-int cast then resolves
            // `(-∞).ceil() as $int` to `<$int>::MIN`. Both paths
            // produce the same value, but the routing differs — keep
            // both arms in mind before introducing an explicit
            // `v == NEG_INFINITY` short-circuit symmetric to the
            // `+∞` guard above (it would be a no-op for the finite-`lo`
            // case and a redundant double-classify for the saturated-
            // `lo` case).
            if $v > hi {
                $crate::extended::Extended::PosInf
            } else if $v < lo {
                $crate::extended::Extended::Finite(<$int>::MIN)
            } else {
                $crate::extended::Extended::Finite($v.ceil() as $int)
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
        // Map `Extended` sentinels to the matching `ExtendedFloat`
        // sentinels (not `Extend(±INFINITY)`): the N5 ordering puts
        // `Top > Extend(+∞)` and `Bot < Extend(-∞)`, so emitting the
        // float-side `±INFINITY` here would break the Galois law at
        // the `(Top, PosInf)` and `(Bot, NegInf)` boundaries.
        //
        // The `Finite` arm uses round-toward-negative-infinity for
        // the int → float cast. For full-triple Conns (target fits
        // in source mantissa) the cast is exact and round-down is
        // a no-op; for L-only Conns it preserves
        // `ceil(inner(b)) ≤ b` (the L-Galois kernel law), which a
        // round-to-nearest cast can break when an `int` value
        // round-trips up rather than down through the float.
        match $b {
            $crate::extended::Extended::NegInf => $crate::float::ExtendedFloat::Bot,
            $crate::extended::Extended::PosInf => $crate::float::ExtendedFloat::Top,
            $crate::extended::Extended::Finite(i) => $crate::float::ExtendedFloat::Extend(
                <$float as $crate::float::RoundDownFromI128>::from_i128_rd(i as i128),
            ),
        }
    };
}

/// Emit a full adjoint-triple Conn `Conn<ExtendedFloat<$float>,
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
            $vis $name : $crate::float::ExtendedFloat<$float> => $crate::extended::Extended<$int> {
                ceil:  {
                    fn ceil(x: $crate::float::ExtendedFloat<$float>)
                        -> $crate::extended::Extended<$int>
                    {
                        match x {
                            $crate::float::ExtendedFloat::Bot => $crate::extended::Extended::NegInf,
                            $crate::float::ExtendedFloat::Top => $crate::extended::Extended::PosInf,
                            $crate::float::ExtendedFloat::Extend(v) =>
                                $crate::__float_ext_int_ceil_body!($float, $int, v),
                        }
                    }
                    ceil
                },
                inner: {
                    fn inner(b: $crate::extended::Extended<$int>)
                        -> $crate::float::ExtendedFloat<$float>
                    {
                        $crate::__float_ext_int_inner_body!($float, $int, b)
                    }
                    inner
                },
                floor: {
                    fn floor(x: $crate::float::ExtendedFloat<$float>)
                        -> $crate::extended::Extended<$int>
                    {
                        match x {
                            $crate::float::ExtendedFloat::Bot => $crate::extended::Extended::NegInf,
                            $crate::float::ExtendedFloat::Top => $crate::extended::Extended::PosInf,
                            $crate::float::ExtendedFloat::Extend(v) =>
                                $crate::__float_ext_int_floor_body!($float, $int, v),
                        }
                    }
                    floor
                },
            }
        }
    };
}

/// Emit an L-only Conn `Conn<ExtendedFloat<$float>, Extended<$int>, L>`.
///
/// Use when `<$int>::BITS > <$float>::MANTISSA_DIGITS + 1` so that
/// `inner: Extended<int> → ExtendedFloat<float>` aliases distinct
/// `int` values onto the same float at large magnitudes — the L-Galois
/// adjunction `ceil ⊣ inner` still holds, but `order_reflecting` and
/// hence `floor_le_ceil` (as a triple) do not.
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! float_ext_int_l {
    ($(#[$meta:meta])* $vis:vis $name:ident, $float:ty, $int:ty) => {
        $(#[$meta])*
        $vis const $name: $crate::conn::Conn<
            $crate::float::ExtendedFloat<$float>,
            $crate::extended::Extended<$int>,
        > = {
            fn ceil(x: $crate::float::ExtendedFloat<$float>)
                -> $crate::extended::Extended<$int>
            {
                match x {
                    $crate::float::ExtendedFloat::Bot => $crate::extended::Extended::NegInf,
                    $crate::float::ExtendedFloat::Top => $crate::extended::Extended::PosInf,
                    $crate::float::ExtendedFloat::Extend(v) =>
                        $crate::__float_ext_int_ceil_body!($float, $int, v),
                }
            }
            fn inner(b: $crate::extended::Extended<$int>)
                -> $crate::float::ExtendedFloat<$float>
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
    use crate::prop::arb::extended_float_f64;
    use proptest::prelude::*;
    use std::cell::Cell;

    // ── ExtendedFloat::fold / fold_with ────────────────────────────

    #[test]
    fn extfloat_fold_bot() {
        assert_eq!(ExtendedFloat::<f64>::Bot.fold(-1, 1, |_| 0), -1);
    }

    #[test]
    fn extfloat_fold_extend() {
        assert_eq!(ExtendedFloat::Extend(3.0_f64).fold(-1, 1, |v| v as i32), 3);
    }

    #[test]
    fn extfloat_fold_top() {
        assert_eq!(ExtendedFloat::<f64>::Top.fold(-1, 1, |_| 0), 1);
    }

    #[test]
    fn extfloat_fold_with_skips_unselected_arms() {
        let variants: [ExtendedFloat<f64>; 3] = [
            ExtendedFloat::Bot,
            ExtendedFloat::Extend(2.5),
            ExtendedFloat::Top,
        ];
        for x in variants {
            let bot_called = Cell::new(false);
            let top_called = Cell::new(false);
            let ext_called = Cell::new(false);
            let _ = x.fold_with(
                || {
                    bot_called.set(true);
                    0i32
                },
                || {
                    top_called.set(true);
                    0
                },
                |_| {
                    ext_called.set(true);
                    0
                },
            );
            match x {
                ExtendedFloat::Bot => {
                    assert!(bot_called.get());
                    assert!(!top_called.get() && !ext_called.get());
                }
                ExtendedFloat::Extend(_) => {
                    assert!(ext_called.get());
                    assert!(!bot_called.get() && !top_called.get());
                }
                ExtendedFloat::Top => {
                    assert!(top_called.get());
                    assert!(!bot_called.get() && !ext_called.get());
                }
            }
        }
    }

    proptest! {
        // `fold_with (const gx) (const gy) f` agrees with
        // `fold gx gy f`. Codomain is `i64` (via `to_bits`) so NaN
        // doesn't break PartialEq on the result.
        #[test]
        fn extfloat_fold_with_const_agrees_with_fold(
            x in extended_float_f64(),
            gx in any::<i64>(),
            gy in any::<i64>(),
        ) {
            let f = |v: f64| v.to_bits() as i64;
            let lazy = x.fold_with(|| gx, || gy, f);
            let strict = x.fold(gx, gy, f);
            prop_assert_eq!(lazy, strict);
        }
    }

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

    #[test]
    fn add_endpoint_propagates_nan_f64() {
        // IEEE: NaN op anything = NaN. The endpoint absorption rule
        // (Bot + finite = Bot, etc.) defers to NaN-propagation when
        // the finite operand is NaN.
        let nan: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::NAN);
        assert!((ExtendedFloat::<f64>::Bot + nan).is_nan());
        assert!((nan + ExtendedFloat::<f64>::Bot).is_nan());
        assert!((ExtendedFloat::<f64>::Top + nan).is_nan());
        assert!((nan + ExtendedFloat::<f64>::Top).is_nan());
    }

    #[test]
    fn sub_endpoint_propagates_nan_f64() {
        let nan: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::NAN);
        assert!((ExtendedFloat::<f64>::Bot - nan).is_nan());
        assert!((ExtendedFloat::<f64>::Top - nan).is_nan());
        assert!((nan - ExtendedFloat::<f64>::Bot).is_nan());
        assert!((nan - ExtendedFloat::<f64>::Top).is_nan());
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
    fn rem_zero_inner_passes_through_f64() {
        // Extend × Extend forwards to inner f64 % f64, which is NaN
        // for divisor 0.0 — IEEE 754 semantics, no lattice arm
        // involved. (See `rem_endpoint_pin_f64` for the Bot/Top arm.)
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(7.5);
        let zero: ExtendedFloat<f64> = ExtendedFloat::Extend(0.0);
        match a % zero {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            other => panic!("expected Extend(NaN), got {other:?}"),
        }
    }

    #[test]
    fn rem_endpoint_arms_f64() {
        // ∞ % anything is NaN per IEEE.
        let one: ExtendedFloat<f64> = ExtendedFloat::Extend(1.0);
        assert!((ExtendedFloat::<f64>::Bot % one).is_nan());
        assert!((ExtendedFloat::<f64>::Top % one).is_nan());
        // finite % ∞ = finite (the divisor is larger in magnitude than
        // any finite, so the remainder is the dividend itself).
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(7.5);
        assert_eq!(a % ExtendedFloat::<f64>::Top, a);
        assert_eq!(a % ExtendedFloat::<f64>::Bot, a);
    }

    #[test]
    fn mul_endpoint_arms_f64() {
        // (-∞)·(-∞) = (+∞)·(+∞) = +∞ = Top.
        assert_eq!(
            ExtendedFloat::<f64>::Bot * ExtendedFloat::<f64>::Bot,
            ExtendedFloat::<f64>::Top
        );
        assert_eq!(
            ExtendedFloat::<f64>::Top * ExtendedFloat::<f64>::Top,
            ExtendedFloat::<f64>::Top
        );
        // (-∞)·(+∞) = -∞ = Bot.
        assert_eq!(
            ExtendedFloat::<f64>::Bot * ExtendedFloat::<f64>::Top,
            ExtendedFloat::<f64>::Bot
        );
        assert_eq!(
            ExtendedFloat::<f64>::Top * ExtendedFloat::<f64>::Bot,
            ExtendedFloat::<f64>::Bot
        );
        // Endpoint × Extend dispatches on the finite operand's sign.
        let pos: ExtendedFloat<f64> = ExtendedFloat::Extend(3.5);
        let neg: ExtendedFloat<f64> = ExtendedFloat::Extend(-3.5);
        let zero: ExtendedFloat<f64> = ExtendedFloat::Extend(0.0);
        assert_eq!(ExtendedFloat::<f64>::Bot * pos, ExtendedFloat::<f64>::Bot);
        assert_eq!(ExtendedFloat::<f64>::Bot * neg, ExtendedFloat::<f64>::Top);
        assert_eq!(ExtendedFloat::<f64>::Top * pos, ExtendedFloat::<f64>::Top);
        assert_eq!(ExtendedFloat::<f64>::Top * neg, ExtendedFloat::<f64>::Bot);
        // Zero × ∞ is the one genuinely indeterminate Mul case.
        assert!((ExtendedFloat::<f64>::Bot * zero).is_nan());
        assert!((ExtendedFloat::<f64>::Top * zero).is_nan());
    }

    #[test]
    fn div_endpoint_arms_f64() {
        // ∞ / ∞ is genuinely indeterminate.
        assert!((ExtendedFloat::<f64>::Bot / ExtendedFloat::<f64>::Bot).is_nan());
        assert!((ExtendedFloat::<f64>::Bot / ExtendedFloat::<f64>::Top).is_nan());
        assert!((ExtendedFloat::<f64>::Top / ExtendedFloat::<f64>::Bot).is_nan());
        assert!((ExtendedFloat::<f64>::Top / ExtendedFloat::<f64>::Top).is_nan());
        // Endpoint / Extend dispatches on the finite operand's sign.
        let pos: ExtendedFloat<f64> = ExtendedFloat::Extend(2.0);
        let neg: ExtendedFloat<f64> = ExtendedFloat::Extend(-2.0);
        let zero: ExtendedFloat<f64> = ExtendedFloat::Extend(0.0);
        assert_eq!(ExtendedFloat::<f64>::Bot / pos, ExtendedFloat::<f64>::Bot);
        assert_eq!(ExtendedFloat::<f64>::Bot / neg, ExtendedFloat::<f64>::Top);
        assert_eq!(ExtendedFloat::<f64>::Top / pos, ExtendedFloat::<f64>::Top);
        assert_eq!(ExtendedFloat::<f64>::Top / neg, ExtendedFloat::<f64>::Bot);
        // ∞ / 0 is indeterminate (sign of zero matters; we let inner
        // IEEE handle and propagate as NaN here for safety).
        assert!((ExtendedFloat::<f64>::Bot / zero).is_nan());
        // Extend / ∞ = signed zero per IEEE.
        let three: ExtendedFloat<f64> = ExtendedFloat::Extend(3.0);
        match three / ExtendedFloat::<f64>::Top {
            ExtendedFloat::Extend(v) => assert_eq!(v, 0.0),
            other => panic!("expected Extend(±0.0), got {other:?}"),
        }
        match three / ExtendedFloat::<f64>::Bot {
            ExtendedFloat::Extend(v) => assert_eq!(v, 0.0),
            other => panic!("expected Extend(±0.0), got {other:?}"),
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
        assert_eq!(ExtendedFloat::<f64>::Bot.exp(), ExtendedFloat::Extend(0.0));
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
