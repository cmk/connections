//! Connections rooted in primitive types from [`std`].
//!
//! Per the [§Module organization](crate) rule, each per-type
//! submodule hosts the Conn consts where that type wins as the
//! placement target (right-side wins).
//!
//! - [`mod@i64`] additionally nests [`i64::decimal`], the custom
//!   decimal-SI ladder (`FD00`..`FD12`) built on `i64`.
//!
//! Mirrors the upstream Haskell `Data.Connection.Int` and
//! `Data.Connection.Word` modules, with three structural differences:
//!
//! - Per-primitive submodules (`i8` / `i16` / `i32` / `i64` / `i128` /
//!   `u8` / `u16` / `u32` / `u64` / `u128`) instead of one flat file.
//!   Each Conn lives in the module of its **right side** (the
//!   destination primitive) — so `I008I016` is in [`i16`] (the wider
//!   destination), `I016I008` is in [`i8`] (the narrower destination),
//!   `U008I008` is in [`i8`] (the signed destination).
//! - `i128` / `u128` extensions throughout. Haskell's `Data.Word` /
//!   `Data.Int` top out at 64 bits.
//! - Narrowing and cross-sign-narrowing directions are first-class
//!   `pub const` Conns (whereas in Haskell narrowing is only
//!   accessible via the `inner` adjoint of the widening Cast).
//!
//! Seven macro families generate the Conns; all live in this
//! parent module and are `pub(crate)`-imported by the per-primitive
//! submodules:
//!
//! | macro | direction | Galois | constructor |
//! |---|---|---|---|
//! | `uint_uint!`        | U→U widening    | left  | `new_left` |
//! | `int_uint!`         | I→U widening    | left  | `new_left` |
//! | `ext_int!`          | I→I, U→I widening (Extended source) | full triple | `new` |
//! | `int_int_narrow!`   | I→I narrowing   | left  | `new_left` |
//! | `uint_uint_narrow!` | U→U narrowing   | left  | `new_left` |
//! | `int_uint_narrow!`  | I→U narrowing   | left  | `new_left` |
//! | `uint_int_sat!`     | U→I non-widening | right | `new_right` |
//!
//! The four narrowing/non-widening macros use a **FINE_MAX
//! boundary fixup** in `inner` (`inner(Coarse::MAX) =
//! Source::MAX`) so the relevant Galois bi-implication holds at
//! the source-side saturation plateau — same pattern as
//! `conn::fixed::u<width>`. The right-Galois `uint_int_sat!` macro
//! doesn't need the fixup: its plateau lives on the target side
//! (negative `i_N` values clip to `0_u_M` via `inner`), and `floor`
//! collapses the symmetric way at the high end.

// The macros expand at the call site (in each submodule), so this
// parent file doesn't need to import `Conn` or `Extended` itself —
// the submodules pull them in.

// ── Existing-shape macros ──────────────────────────────────────────

/// `Conn<u_N, u_M>` widening (`bits(u_N) < bits(u_M)`).
///
/// `ceil` is the lossless `as`-upcast; `inner` saturates targets
/// above `u_N::MAX` down to `u_N::MAX` before downcasting.
macro_rules! uint_uint {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating cast.")]
        pub const $NAME: Conn<$A, $B> = {
            fn ceil(x: $A) -> $B {
                x as $B
            }
            fn inner(x: $B) -> $A {
                let cap = <$A>::MAX as $B;
                let clipped = if x > cap { cap } else { x };
                clipped as $A
            }
            Conn::new_left(ceil, inner)
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
        pub const $NAME: Conn<$A, $B> = {
            fn ceil(x: $A) -> $B {
                if x < 0 { 0 } else { x as $B }
            }
            fn inner(x: $B) -> $A {
                let cap = <$A>::MAX as $B;
                let clipped = if x > cap { cap } else { x };
                clipped as $A
            }
            Conn::new_left(ceil, inner)
        };
    };
}
pub(crate) use int_uint;

/// `Conn<Extended<$A>, $B>` widening with Extended source.
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
macro_rules! ext_int {
    ($NAME:ident, $A:ty, $B:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`Extended<",
            stringify!($A),
            "> → ",
            stringify!($B),
            "` adjoint triple."
        )]
        pub const $NAME: Conn<Extended<$A>, $B> = {
            // `BELOW` is one below the source's MIN; `ABOVE` is one
            // above the source's MAX. Both are themselves in the
            // infinity regions: `inner(BELOW) == NegInf` and
            // `inner(ABOVE) == PosInf` (the `<=` / `>=` are
            // inclusive). `Finite(_)` only covers the open interval
            // `(BELOW, ABOVE)`.
            const BELOW: $B = (<$A>::MIN as $B) - 1;
            const ABOVE: $B = (<$A>::MAX as $B) + 1;
            fn ceil(x: Extended<$A>) -> $B {
                match x {
                    Extended::NegInf => <$B>::MIN,
                    Extended::Finite(a) => a as $B,
                    Extended::PosInf => ABOVE,
                }
            }
            fn inner(x: $B) -> Extended<$A> {
                if x <= BELOW {
                    Extended::NegInf
                } else if x >= ABOVE {
                    Extended::PosInf
                } else {
                    Extended::Finite(x as $A)
                }
            }
            fn floor(x: Extended<$A>) -> $B {
                match x {
                    Extended::NegInf => BELOW,
                    Extended::Finite(a) => a as $B,
                    Extended::PosInf => <$B>::MAX,
                }
            }
            Conn::new(ceil, inner, floor)
        };
    };
}
pub(crate) use ext_int;

// ── Narrowing macros ───────────────────────────────────────────────

/// `Conn<i_N, i_M>` narrowing (`bits(i_N) > bits(i_M)`).
///
/// `ceil` saturates at both `i_M::MIN` and `i_M::MAX`; `inner` is
/// the lossless widen with the high-end FINE_MAX fixup
/// (`inner(i_M::MAX) = i_N::MAX`). The low-end plateau holds
/// without fixup because `i_M::MIN as i_N` is strictly above
/// `i_N::MIN`, so `inner(i_M::MIN)` lands above every low-plateau
/// source value.
macro_rules! int_int_narrow {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating narrow.")]
        pub const $NAME: Conn<$A, $B> = {
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
            Conn::new_left(ceil, inner)
        };
    };
}
pub(crate) use int_int_narrow;

/// `Conn<u_N, u_M>` narrowing (`bits(u_N) > bits(u_M)`).
///
/// `ceil` saturates source values above `u_M::MAX` down to
/// `u_M::MAX` before downcasting; `inner` is the lossless `as`-widen
/// with a FINE_MAX fixup (`inner(u_M::MAX) = u_N::MAX`). The fixup
/// is required for left-Galois to hold at the source-side
/// saturation plateau (mirrors the same pattern in
/// `conn::fixed::u<width>`).
macro_rules! uint_uint_narrow {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating narrow.")]
        pub const $NAME: Conn<$A, $B> = {
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
            Conn::new_left(ceil, inner)
        };
    };
}
pub(crate) use uint_uint_narrow;

/// `Conn<u_N, i_M>` non-widening cross-sign (`bits(u_N) ≥ bits(i_M)`).
///
/// **Right-Galois single-sided** (uses [`Conn::new_right`]). The
/// saturation plateau lives on the target side: `inner` clips
/// `i_M`'s negative half to `0_u_N`. `floor` saturates `u_N` values
/// above `i_M::MAX` down to `i_M::MAX`.
///
/// No FINE_MAX fixup needed: `inner`'s image is exactly
/// `[0, i_M::MAX as u_N]`, and `floor`'s collapse at the high
/// plateau aligns the target-side fiber with the source identity at
/// `i_M::MAX`.
macro_rules! uint_int_sat {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating cast (right-Galois).")]
        pub const $NAME: Conn<$A, $B> = {
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
            Conn::new_right(inner, floor)
        };
    };
}
pub(crate) use uint_int_sat;

/// `Conn<i_N, u_M>` narrowing (`bits(i_N) > bits(u_M)`).
///
/// `ceil` clips negatives to `0` and saturates positives at
/// `u_M::MAX`; `inner` is the lossless `as`-widen with a FINE_MAX
/// fixup (`inner(u_M::MAX) = i_N::MAX`). The negative half of the
/// source has no plateau issue (it collapses on `ceil`, the
/// source-side fiber compatible with left-Galois).
macro_rules! int_uint_narrow {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating narrow.")]
        pub const $NAME: Conn<$A, $B> = {
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
            Conn::new_left(ceil, inner)
        };
    };
}
pub(crate) use int_uint_narrow;

// ── Per-primitive submodules ───────────────────────────────────────

pub mod i128;
pub mod i16;
pub mod i32;
pub mod i64;
pub mod i8;
pub mod u128;
pub mod u16;
pub mod u32;
pub mod u64;
pub mod u8;
