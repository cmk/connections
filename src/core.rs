//! Connections among **Rust core/std primitive types** —
//! `iN`/`uN` std integers, IEEE floats (`f16`/`f32`/`f64`), `bool`,
//! `char`, and [`core::num::NonZero<T>`]. The crate's only top-level
//! domain split is between this module (Conns whose endpoints all
//! ship in `core` / `std`) and [`crate::fixed`] (Conns where at least
//! one endpoint is a [`fixed`]-crate Q-format wrapper).
//!
//! [`fixed`]: https://docs.rs/fixed
//! [`core::num::NonZero<T>`]: https://doc.rust-lang.org/core/num/struct.NonZero.html
//!
//! ## Submodules
//!
//! - [`mod@i008`] / [`mod@i016`] / [`mod@i032`] / [`mod@i064`] / [`mod@i128`] —
//!   signed-source std-int Conns plus `NonZeroI<N>` host surfaces.
//! - [`mod@u008`] / [`mod@u016`] / [`mod@u032`] / [`mod@u064`] / [`mod@u128`] —
//!   unsigned-source std-int Conns plus `NonZeroU<N>` host surfaces.
//! - `f016` (gated on `f16`) / [`mod@f032`] / [`mod@f064`] —
//!   IEEE-float Conns; the [`ExtendedFloat<T>`](crate::float::ExtendedFloat)
//!   wrapper and float-only infrastructure live in [`crate::float`].
//! - [`mod@char`] — `Extended<u32> → Extended<char>` codepoint projection.
//! - [`mod@bool`] — bool ↔ `[u8;1]` / `LE<1>` projections.
//!
//! ## Conn-name prefix conventions
//!
//! The prefix letter alone tells you which world a side belongs to:
//!
//! | Prefix | Shape | Side meaning                                            |
//! |--------|-------|---------------------------------------------------------|
//! | `I`    | 1L+3D | signed std primitive (`iN`). Digits = bit-width.        |
//! | `U`    | 1L+3D | unsigned std primitive (`uN`). Digits = bit-width.      |
//! | `F`    | 1L+3D | IEEE binary float (`f16`/`f32`/`f64`). Digits = bit-width. |
//! | `N`    | 1L+3D | `NonZero<iN>` / `NonZero<uN>`. Sign implicit by module path; digits = bit-width. |
//! | `BE`/`LE` | 2L+2D | big-/little-endian byte array `[u8; N]` / [`LE`]. Digits = byte count. |
//!
//! Cross-module name collisions are allowed and resolved by qualified import.
//!
//! ## Macros
//!
//! Nine macro families generate the std-int Conns; all live in this
//! parent module and are `pub(crate)`-imported by the per-primitive
//! submodules:
//!
//! | macro | direction | Galois | constructor |
//! |---|---|---|---|
//! | `uint_uint!`        | U→U widening    | left  | `new_l` |
//! | `int_uint!`         | I→U widening    | left  | `new_l` |
//! | `ext_int!`          | I→I, U→I widening (Extended source) | left  | `new_l` |
//! | `int_int_narrow!`   | I→I narrowing   | left  | `new_l` |
//! | `uint_uint_narrow!` | U→U narrowing   | left  | `new_l` |
//! | `int_uint_narrow!`  | I→U narrowing   | left  | `new_l` |
//! | `uint_int_sat!`     | U→I non-widening | right | `new_r` |
//! | `nz_int_ext!`       | `iN ↔ NonZero<iN>`  | adjoint triple | both |
//! | `nz_uint_ext!`      | `uN ↔ NonZero<uN>`  | left | `new_l` |
//!
//! The four narrowing/non-widening macros use a **FINE_MAX
//! boundary fixup** in `inner` (`inner(Coarse::MAX) =
//! Source::MAX`) so the relevant Galois bi-implication holds at
//! the source-side saturation plateau. The right-Galois
//! `uint_int_sat!` macro doesn't need the fixup: its plateau lives
//! on the target side.

/// Little-endian byte array wrapper with numeric-sort ordering.
///
/// Plain `[u8; N]` uses lexicographic order from index 0 upward, which
/// makes big-endian byte arrays sortable but breaks little-endian numeric
/// order for multi-byte widths. `LE<N>` keeps the little-endian storage
/// shape while ordering from the most-significant byte down to the
/// least-significant byte.
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct LE<const N: usize>(pub [u8; N]);

impl<const N: usize> Ord for LE<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.iter().rev().cmp(other.0.iter().rev())
    }
}

impl<const N: usize> PartialOrd for LE<N> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> From<[u8; N]> for LE<N> {
    #[inline]
    fn from(bytes: [u8; N]) -> Self {
        Self(bytes)
    }
}

impl<const N: usize> From<LE<N>> for [u8; N] {
    #[inline]
    fn from(bytes: LE<N>) -> Self {
        bytes.0
    }
}

impl<const N: usize> AsRef<[u8; N]> for LE<N> {
    #[inline]
    fn as_ref(&self) -> &[u8; N] {
        &self.0
    }
}

#[cfg(test)]
mod le_tests {
    use super::LE;

    #[test]
    fn le_order_compares_most_significant_byte_first() {
        assert!(LE([1]) < LE([2]));
        assert!(LE([1, 0]) < LE([2, 0]));
        assert!(LE([255, 0]) < LE([0, 1]));
        assert!(LE([255, 255, 0, 0]) < LE([0, 0, 1, 0]));
    }

    #[test]
    fn le_equality_matches_inner_bytes() {
        assert_eq!(LE([1, 2, 3, 4]), LE([1, 2, 3, 4]));
        assert_ne!(LE([1, 2, 3, 4]), LE([1, 2, 3, 5]));
    }
}

// ── std-int Conn macros ────────────────────────────────────────────

/// `Conn<u_N, u_M>` widening (`bits(u_N) < bits(u_M)`).
///
/// `ceil` is the lossless `as`-upcast; `inner` saturates targets
/// above `u_N::MAX` down to `u_N::MAX` before downcasting.
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! uint_uint {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating cast.")]
        pub const $NAME: $crate::conn::Conn<$A, $B> = {
            fn ceil(x: $A) -> $B {
                x as $B
            }
            fn inner(x: $B) -> $A {
                let cap = <$A>::MAX as $B;
                let clipped = if x > cap { cap } else { x };
                clipped as $A
            }
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}
pub(crate) use uint_uint;

/// `Conn<i_N, u_M>` widening or same-width cross-sign
/// (`bits(i_N) ≤ bits(u_M)`).
///
/// `ceil` clips negatives to `0` then upcasts (lossless on the
/// non-negative half by the bit-width constraint); `inner`
/// saturates targets above `i_N::MAX` down to `i_N::MAX`.
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! int_uint {
    ($NAME:ident, $A:ty, $B:ty) => {
        // rustfmt's indent-instability bug with `#[doc = concat!(...)]`
        // means each fmt round pushes the args further right.
        // `#[rustfmt::skip]` pins the layout. See ext_int! below for
        // the same workaround.
#[rustfmt::skip]
        #[doc = concat!(
            "`",
            stringify!($A),
            " → ",
            stringify!($B),
            "` saturating cast: negatives clip to 0; `inner` saturates at source max."
        )]
        pub const $NAME: $crate::conn::Conn<$A, $B> = {
            fn ceil(x: $A) -> $B {
                if x < 0 { 0 } else { x as $B }
            }
            fn inner(x: $B) -> $A {
                let cap = <$A>::MAX as $B;
                let clipped = if x > cap { cap } else { x };
                clipped as $A
            }
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}
pub(crate) use int_uint;

/// `Conn<Extended<$A>, $B>` widening with Extended source (left-Galois).
/// Covers both `I??I??` (signed widening) and `U??I??`
/// (unsigned-into-signed widening) — the body is identical, only
/// the source's `MIN`/`MAX` differ.
///
/// Constraints (verified at the call site, not at compile time):
/// - `(<$A>::MIN as $B) - 1` and `(<$A>::MAX as $B) + 1` must fit
///   in `$B` — guaranteed by `bits($A) < bits($B)` (signed source)
///   or `bits($A) ≤ bits($B) - 1` (unsigned source, equivalent).
/// - `<$B>::MIN < BELOW` and `<$B>::MAX > ABOVE` (i.e. target has
///   room beyond the source range so saturation values are
///   distinct).
///
/// **One-sided.** `_inner` collapses every rung value `≤ BELOW` onto
/// `Extended::NegInf` and every rung value `≥ ABOVE` onto
/// `Extended::PosInf` — non-injective at the saturation regions, so
/// not order-reflecting, so no true adjoint triple exists. The
/// L-Galois adjunction `ceil ⊣ inner` holds on the full domain;
/// shipped as `ConnL` accordingly. (Plan 32.)
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! ext_int {
    ($NAME:ident, $A:ty, $B:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`Extended<",
            stringify!($A),
            "> → ",
            stringify!($B),
            "` left-Galois widening."
        )]
        pub const $NAME: $crate::conn::Conn<$crate::extended::Extended<$A>, $B> = {
            const BELOW: $B = (<$A>::MIN as $B) - 1;
            const ABOVE: $B = (<$A>::MAX as $B) + 1;
            fn ceil(x: $crate::extended::Extended<$A>) -> $B {
                match x {
                    $crate::extended::Extended::NegInf => <$B>::MIN,
                    $crate::extended::Extended::Finite(a) => a as $B,
                    $crate::extended::Extended::PosInf => ABOVE,
                }
            }
            fn inner(x: $B) -> $crate::extended::Extended<$A> {
                if x <= BELOW {
                    $crate::extended::Extended::NegInf
                } else if x >= ABOVE {
                    $crate::extended::Extended::PosInf
                } else {
                    $crate::extended::Extended::Finite(x as $A)
                }
            }

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}
pub(crate) use ext_int;

// ── Narrowing macros ───────────────────────────────────────────────

/// `Conn<i_N, i_M>` narrowing (`bits(i_N) > bits(i_M)`).
///
/// **Constraint** (verified at the call site, not at compile time):
/// `bits($A) > bits($B)`. The macro's `ceil` casts `<$B>::MAX as $A`
/// and `<$B>::MIN as $A` for its threshold checks; both must fit
/// losslessly in `$A` for the saturation logic to be correct.
/// Mirrors the `ext_int!` constraint a few lines up.
///
/// `ceil` saturates at both `i_M::MIN` and `i_M::MAX`; `inner` is
/// the lossless widen with the high-end FINE_MAX fixup
/// (`inner(i_M::MAX) = i_N::MAX`).
///
/// **Why no FINE_MIN fixup?** The low-end plateau holds for
/// `galois_l` without one. The plateau covers source values
/// `a < i_M::MIN as i_N` (everything `ceil` collapses onto
/// `i_M::MIN`). For these, `ceil(a) = i_M::MIN ≤ b` is true for
/// every `b ∈ i_M`, so the law's LHS is always true, and the RHS
/// (`a ≤ inner(b)`) is also always true because
/// `inner(b) ≥ i_M::MIN as i_N > a` (since
/// `i_M::MIN as i_N > i_N::MIN ≥ a` by the bit-width
/// constraint). Both sides match without fiddling. Compare the
/// high end, where `ceil` collapsing onto `i_M::MAX` does require
/// the fixup so `a ≤ inner(i_M::MAX) = i_N::MAX` holds.
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! int_int_narrow {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating narrow.")]
        pub const $NAME: $crate::conn::Conn<$A, $B> = {
            fn ceil(x: $A) -> $B {
                if x > <$B>::MAX as $A {
                    <$B>::MAX
                } else if x < <$B>::MIN as $A {
                    <$B>::MIN
                } else {
                    x as $B
                }
            }
            fn inner(x: $B) -> $A {
                if x == <$B>::MAX { <$A>::MAX } else { x as $A }
            }
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}
pub(crate) use int_int_narrow;

/// `Conn<u_N, u_M>` narrowing (`bits(u_N) > bits(u_M)`).
///
/// `ceil` saturates source values above `u_M::MAX` down to
/// `u_M::MAX` before downcasting. There is **no** low-end branch
/// (no `MIN` saturation arm) because both endpoints are unsigned —
/// the source range starts at `0 = u_N::MIN ≥ u_M::MIN = 0`, so no
/// source value can fall below the target's minimum. Compare
/// `int_int_narrow!`, which needs both arms because signed sources
/// can dip below the target's `MIN`.
///
/// `inner` is the lossless `as`-widen with a FINE_MAX fixup
/// (`inner(u_M::MAX) = u_N::MAX`). The fixup is required for
/// left-Galois to hold at the source-side saturation plateau
/// (mirrors the same pattern in the per-primitive `fix_fix_uN!`
/// macros).
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! uint_uint_narrow {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating narrow.")]
        pub const $NAME: $crate::conn::Conn<$A, $B> = {
            fn ceil(x: $A) -> $B {
                if x > <$B>::MAX as $A {
                    <$B>::MAX
                } else {
                    x as $B
                }
            }
            fn inner(x: $B) -> $A {
                if x == <$B>::MAX { <$A>::MAX } else { x as $A }
            }
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}
pub(crate) use uint_uint_narrow;

/// `Conn<u_N, i_M>` non-widening cross-sign (`bits(u_N) ≥ bits(i_M)`).
///
/// **Constraint** (verified at the call site, not at compile time):
/// `bits($A) ≥ bits($B)`. `floor` casts `<$B>::MAX as $A`, which
/// must fit in `$A` losslessly — guaranteed by the bit-width
/// constraint since `$B::MAX > 0` and unsigned `$A` can hold any
/// positive value up to `$A::MAX ≥ $B::MAX`. `inner` casts
/// non-negative `$B` values to `$A`, also lossless under the
/// same constraint. Mirrors the `ext_int!` constraint pattern.
///
/// **Right-Galois single-sided** (uses [`Conn::new_r`](crate::conn::Conn::new_r)). The
/// saturation plateau lives on the target side: `inner` clips
/// `i_M`'s negative half to `0_u_N`. `floor` saturates `u_N` values
/// above `i_M::MAX` down to `i_M::MAX`.
///
/// No FINE_MAX fixup needed: `inner`'s image is exactly
/// `[0, i_M::MAX as u_N]`, and `floor`'s collapse at the high
/// plateau aligns the target-side fiber with the source identity at
/// `i_M::MAX`.
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! uint_int_sat {
    ($(#[$attr:meta])* $NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating cast (right-Galois).")]
        $(#[$attr])*
        pub const $NAME: $crate::conn::Conn<$A, $B, $crate::conn::R> = {
            fn floor(x: $A) -> $B {
                if x > <$B>::MAX as $A {
                    <$B>::MAX
                } else {
                    x as $B
                }
            }
            fn inner(x: $B) -> $A {
                if x < 0 { 0 } else { x as $A }
            }
            $crate::conn::Conn::new_r(inner, floor)
        };
    };
}
pub(crate) use uint_int_sat;

/// `Conn<i<N>, NonZero<i<N>>>` — saturate `iN` onto `NonZero<iN>` with
/// asymmetric rounding at zero. Source is the bare primitive (not
/// `Extended<iN>`) so there are no infinities at the source-side
/// plateau to break the Galois law: every `iN` value other than 0 is
/// itself a `NonZero<iN>`, and 0 sandwiches between `NonZero(-1)` and
/// `NonZero(+1)`.
///
/// Forward (`ceil` / `floor`): `iN → NonZero<iN>`.
///
/// - `floor(0) = NonZero(-1)`  (largest NonZero ≤ 0)
/// - `ceil(0)  = NonZero(+1)`  (smallest NonZero ≥ 0)
/// - For `v != 0`: `ceil(v) = floor(v) = NonZero(v)` (lossless).
///
/// Back (`inner`): trivial total embedding
/// `NonZero<iN> → iN::get()`.
///
/// Both Galois laws (`galois_l` and `galois_r`) hold: the
/// asymmetric `floor`/`ceil` lift the target's puncture at zero to a
/// [-1, +1] sandwich on the source side, exactly bracketing the
/// missing value.
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! nz_int_ext {
    ($NAME:ident, $A:ty, $NZ:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`",
            stringify!($A),
            " ↔ ",
            stringify!($NZ),
            "` (signed; floor/ceil split 0 between -1 and +1)."
        )]
        pub struct $NAME;

        impl $NAME {
            const fn _ceil(v: $A) -> $NZ {
                let r: $A = if v == 0 { 1 } else { v };
                match <$NZ>::new(r) {
                    Some(nz) => nz,
                    None => panic!("nz_int_ext::ceil produced zero"),
                }
            }
            const fn _floor(v: $A) -> $NZ {
                let r: $A = if v == 0 { -1 } else { v };
                match <$NZ>::new(r) {
                    Some(nz) => nz,
                    None => panic!("nz_int_ext::floor produced zero"),
                }
            }
            const fn _inner(nz: $NZ) -> $A {
                nz.get()
            }
        }

        impl $crate::conn::ConnL for $NAME {
            type A = $A;
            type B = $NZ;
            #[inline]
            fn conn_l(&self) -> $crate::conn::Conn<$A, $NZ, $crate::conn::L> {
                $crate::conn::Conn::new_l($NAME::_ceil, $NAME::_inner)
            }
        }
        impl $crate::conn::ConnR for $NAME {
            type A = $A;
            type B = $NZ;
            #[inline]
            fn conn_r(&self) -> $crate::conn::Conn<$A, $NZ, $crate::conn::R> {
                $crate::conn::Conn::new_r($NAME::_inner, $NAME::_floor)
            }
        }
    };
}
pub(crate) use nz_int_ext;

/// `Conn<u<N>, NonZero<u<N>>>` — unsigned counterpart of
/// [`nz_int_ext!`]. `floor` and `ceil` collapse identically at 0
/// because there is no NonZero ≤ 0 on the unsigned side: both pick
/// `NonZero(1)`, the smallest representable NonZero. Single-sided
/// left-Galois ([`Conn::new_l`]) — `floor = ceil`. The
/// right-Galois law fails at `(NonZero(1), 0)` (no NonZero strictly
/// below 1 to act as the "previous" rounding target).
///
/// [`Conn::new_l`]: crate::conn::Conn::new_l
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! nz_uint_ext {
    ($NAME:ident, $A:ty, $NZ:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`",
            stringify!($A),
            " ↔ ",
            stringify!($NZ),
            "` (unsigned; 0 saturates to NonZero(1); single-sided left-Galois)."
        )]
        pub const $NAME: $crate::conn::Conn<$A, $NZ> = {
            fn ceil(v: $A) -> $NZ {
                let r: $A = if v == 0 { 1 } else { v };
                match <$NZ>::new(r) {
                    Some(nz) => nz,
                    None => panic!("nz_uint_ext::ceil produced zero"),
                }
            }
            fn inner(nz: $NZ) -> $A {
                nz.get()
            }

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}
pub(crate) use nz_uint_ext;

/// `Conn<i_N, u_M>` narrowing (`bits(i_N) > bits(u_M)`).
///
/// `ceil` clips negatives to `0` and saturates positives at
/// `u_M::MAX`; `inner` is the lossless `as`-widen with a FINE_MAX
/// fixup (`inner(u_M::MAX) = i_N::MAX`). The negative half of the
/// source has no plateau issue (it collapses on `ceil`, the
/// source-side fiber compatible with left-Galois).
#[cfg_attr(feature = "macros", macro_export)]
macro_rules! int_uint_narrow {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating narrow.")]
        pub const $NAME: $crate::conn::Conn<$A, $B> = {
            fn ceil(x: $A) -> $B {
                if x < 0 {
                    0
                } else if x > <$B>::MAX as $A {
                    <$B>::MAX
                } else {
                    x as $B
                }
            }
            fn inner(x: $B) -> $A {
                if x == <$B>::MAX { <$A>::MAX } else { x as $A }
            }
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}
pub(crate) use int_uint_narrow;

// ── Per-primitive submodules ───────────────────────────────────────

pub mod i008;
pub mod i016;
pub mod i032;
pub mod i064;
pub mod i128;
pub mod u008;
pub mod u016;
pub mod u032;
pub mod u064;
pub mod u128;

#[cfg(feature = "f16")]
pub mod f016;
pub mod f032;
pub mod f064;

pub mod bool;
pub mod char;
