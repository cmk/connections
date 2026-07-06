//! `usize` → `u8` / `u16` / `u32` / `u64` / `u128` pointer-width cast Conns.
//!
//! `usize` is pointer-width (16/32/64-bit by target), so these casts
//! cannot reuse the fixed-width `as`-based std-int macros in
//! [`crate::core`]: an `as`-narrowing *truncates* out-of-range values
//! (`70000_u32 as u16 == 4464`) where the Galois law needs *saturation*.
//! Every conversion here clamps with [`TryFrom`] (or the infallible
//! [`From`] where the target is guaranteed to hold the source — `u8`/`u16`
//! into `usize`), which makes the family lawful on every target width
//! rather than only the 64-bit host, with no `cfg`.
//!
//! - [`SIZEU008`] — `usize → u8`, saturating narrow (a narrowing on every
//!   target, since `usize ≥ 16 > 8` bits).
//! - [`SIZEU016`] — `usize → u16`, saturating narrow (the identity iso on a
//!   16-bit target, a narrowing on 32/64-bit).
//! - [`SIZEU032`] — `usize → u32`, saturating narrow (iso on 32-bit; a
//!   lossless widen on 16-bit, a narrowing on 64-bit).
//! - [`SIZEU064`] — `usize → u64`, saturating embed (iso on 64-bit; a
//!   lossless widen on 16/32-bit).
//! - [`SIZEU128`] — `usize → u128`, saturating embed (lossless on every real
//!   target).
//!
//! The three narrowings (`u8`/`u16`/`u32`) carry a FINE_MAX fixup in `inner`
//! so left-Galois holds at the target-max saturation plateau; the two embeds
//! (`u64`/`u128`) do not (widenings, like [`uint_uint!`](crate::uint_uint)).
//! All five are one-sided left-Galois ([`Conn::new_l`]): `ceil ⊣ inner`.

use crate::conn::Conn;

/// `usize → u8` saturating narrow (left-Galois).
///
/// A narrowing on every target (`usize ≥ 16 > 8` bits), so `ceil` always
/// saturates values above `u8::MAX`, and `inner` widens with the FINE_MAX
/// fixup (`inner(u8::MAX) = usize::MAX`) — the fixup pins the source-side
/// saturation plateau so `a ≤ inner(ceil(a))` holds for every `a`. The
/// widen itself is the infallible `usize::from` (`u8` fits every `usize`).
pub const SIZEU008: Conn<usize, u8> = {
    fn ceil(x: usize) -> u8 {
        u8::try_from(x).unwrap_or(u8::MAX)
    }
    fn inner(y: u8) -> usize {
        if y == u8::MAX {
            usize::MAX
        } else {
            usize::from(y)
        }
    }
    Conn::new_l(ceil, inner)
};

/// `usize → u16` saturating narrow (left-Galois).
///
/// A narrowing on 32/64-bit and the identity iso on a 16-bit target
/// (`usize == u16`), never a widening (`usize ≥ 16` bits). `ceil` saturates
/// values above `u16::MAX`; `inner` widens via the infallible `usize::from`
/// with the FINE_MAX fixup (`inner(u16::MAX) = usize::MAX`), which on a
/// 16-bit target coincides with `u16::MAX` and keeps the iso consistent.
pub const SIZEU016: Conn<usize, u16> = {
    fn ceil(x: usize) -> u16 {
        u16::try_from(x).unwrap_or(u16::MAX)
    }
    fn inner(y: u16) -> usize {
        if y == u16::MAX {
            usize::MAX
        } else {
            usize::from(y)
        }
    }
    Conn::new_l(ceil, inner)
};

/// `usize → u32` saturating narrow (left-Galois).
///
/// `ceil` clamps source values above `u32::MAX` down to `u32::MAX`;
/// `inner` widens losslessly with a FINE_MAX fixup (`inner(u32::MAX) =
/// usize::MAX`). The fixup is what keeps left-Galois true on a 64-bit
/// target, where every `usize > u32::MAX` collapses onto `u32::MAX` under
/// `ceil`: taking `b = u32::MAX` makes the law's LHS `ceil(a) ≤ b`
/// vacuously true, so `a ≤ inner(b)` must hold for *every* `a`, forcing
/// `inner(u32::MAX) = usize::MAX`. Mirrors the fixed-width
/// `uint_uint_narrow!` macro.
///
/// On a 16-bit target `usize` is *narrower* than `u32`, so `ceil` is a
/// lossless widen and `inner` saturates instead — the same two functions
/// stay lawful because both clamp with `TryFrom`. Unlike [`SIZEU008`] /
/// [`SIZEU016`], `inner`'s widen must be fallible `usize::try_from`: `u32`
/// does not fit a 16-bit `usize`, so there is no `From<u32> for usize`.
pub const SIZEU032: Conn<usize, u32> = {
    fn ceil(x: usize) -> u32 {
        u32::try_from(x).unwrap_or(u32::MAX)
    }
    fn inner(y: u32) -> usize {
        if y == u32::MAX {
            usize::MAX
        } else {
            // y < u32::MAX: fits in usize on 32/64-bit; on a 16-bit
            // target it saturates to usize::MAX.
            usize::try_from(y).unwrap_or(usize::MAX)
        }
    }
    Conn::new_l(ceil, inner)
};

/// `usize → u64` saturating embed (left-Galois).
///
/// `ceil` embeds losslessly on every real target (`usize ≤ 64` bits); the
/// `unwrap_or` saturation arm is dead on real hardware and only fires on a
/// hypothetical `> 64`-bit `usize`. `inner` saturates `u64` values above
/// `usize::MAX` down to `usize::MAX`.
///
/// Unlike the narrowings there is **no** FINE_MAX fixup: this is a widening
/// (like the fixed-width `uint_uint!` macro), so the saturation cap already
/// lands `inner(u64::MAX) = usize::MAX` on 16/32-bit targets, and on a
/// 64-bit target `usize == u64` makes the whole Conn the identity iso.
pub const SIZEU064: Conn<usize, u64> = {
    fn ceil(x: usize) -> u64 {
        u64::try_from(x).unwrap_or(u64::MAX)
    }
    fn inner(y: u64) -> usize {
        usize::try_from(y).unwrap_or(usize::MAX)
    }
    Conn::new_l(ceil, inner)
};

/// `usize → u128` saturating embed (left-Galois).
///
/// `ceil` embeds losslessly on every real target (`usize ≤ 64 < 128` bits);
/// the `unwrap_or` arm is dead on real hardware. `inner` saturates `u128`
/// values above `usize::MAX` down to `usize::MAX`. No FINE_MAX fixup (a
/// widening, like [`SIZEU064`]).
pub const SIZEU128: Conn<usize, u128> = {
    fn ceil(x: usize) -> u128 {
        u128::try_from(x).unwrap_or(u128::MAX)
    }
    fn inner(y: u128) -> usize {
        usize::try_from(y).unwrap_or(usize::MAX)
    }
    Conn::new_l(ceil, inner)
};

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── Narrowing saturation / fixup spot checks ──────────────────────

    #[test]
    fn sizeu008_saturates_and_fixes_up() {
        // Width-agnostic: usize::MAX ≥ 65535 > u8::MAX on every target, so
        // ceil always saturates and the fixup pins inner(u8::MAX).
        assert_eq!(SIZEU008.ceil(usize::MAX), u8::MAX);
        assert_eq!(SIZEU008.upper(u8::MAX), usize::MAX);
        assert_eq!(SIZEU008.upper(0), 0);
        assert_eq!(SIZEU008.ceil(200), 200);
        assert_eq!(SIZEU008.upper(200), 200);
    }

    #[test]
    fn sizeu016_saturates_and_fixes_up() {
        // On a 16-bit target usize::MAX == u16::MAX, so ceil(usize::MAX) is
        // the iso image; on 32/64-bit it saturates. Either way == u16::MAX.
        assert_eq!(SIZEU016.ceil(usize::MAX), u16::MAX);
        assert_eq!(SIZEU016.upper(u16::MAX), usize::MAX);
        assert_eq!(SIZEU016.upper(0), 0);
        assert_eq!(SIZEU016.ceil(1_000), 1_000);
        assert_eq!(SIZEU016.upper(1_000), 1_000);
    }

    #[test]
    fn sizeu032_saturates_and_fixes_up() {
        // Width-agnostic: the FINE_MAX fixup pins inner(u32::MAX) to
        // usize::MAX on every target, and small values round-trip.
        assert_eq!(SIZEU032.upper(u32::MAX), usize::MAX);
        assert_eq!(SIZEU032.upper(0), 0);
        assert_eq!(SIZEU032.ceil(1_000), 1_000);
        assert_eq!(SIZEU032.upper(1_000), 1_000);

        // Narrowing saturation only exists where usize is wider than u32
        // (a 64-bit target): source values above u32::MAX clamp down under
        // ceil. On 16/32-bit no usize exceeds u32::MAX, so there is nothing
        // to saturate and `ceil(usize::MAX)` is the lossless `usize::MAX`.
        #[cfg(target_pointer_width = "64")]
        {
            assert_eq!(SIZEU032.ceil(usize::MAX), u32::MAX);
            assert_eq!(SIZEU032.ceil(u32::MAX as usize + 1), u32::MAX);
        }
    }

    // ── Embed spot checks ─────────────────────────────────────────────

    #[test]
    fn sizeu064_embeds_and_saturates() {
        assert_eq!(SIZEU064.upper(u64::MAX), usize::MAX);
        // Lossless embed on the low range: ceil == `as`, and it round-trips.
        for v in [0usize, 1, 1_000, usize::MAX - 1, usize::MAX] {
            assert_eq!(SIZEU064.ceil(v), v as u64);
            assert_eq!(SIZEU064.upper(v as u64), v);
        }
    }

    #[test]
    fn sizeu128_embeds_and_saturates() {
        assert_eq!(SIZEU128.upper(u128::MAX), usize::MAX);
        for v in [0usize, 1, 1_000, usize::MAX - 1, usize::MAX] {
            assert_eq!(SIZEU128.ceil(v), v as u128);
            assert_eq!(SIZEU128.upper(v as u128), v);
        }
    }

    // ── Boundary-biased Galois-law properties ─────────────────────────

    fn arb_usize() -> impl Strategy<Value = usize> {
        prop_oneof![
            Just(0usize),
            Just(usize::MAX),
            Just(u8::MAX as usize),
            Just(u16::MAX as usize),
            Just(u32::MAX as usize),
            any::<usize>(),
        ]
    }
    fn arb_u8() -> impl Strategy<Value = u8> {
        prop_oneof![Just(0u8), Just(u8::MAX), any::<u8>()]
    }
    fn arb_u16() -> impl Strategy<Value = u16> {
        prop_oneof![Just(0u16), Just(u16::MAX), any::<u16>()]
    }
    fn arb_u32() -> impl Strategy<Value = u32> {
        prop_oneof![Just(0u32), Just(u32::MAX), any::<u32>()]
    }
    fn arb_u64() -> impl Strategy<Value = u64> {
        prop_oneof![
            Just(0u64),
            Just(u64::MAX),
            Just(usize::MAX as u64),
            any::<u64>()
        ]
    }
    fn arb_u128() -> impl Strategy<Value = u128> {
        prop_oneof![
            Just(0u128),
            Just(u128::MAX),
            Just(usize::MAX as u128),
            any::<u128>(),
        ]
    }

    proptest! {
        #[test]
        fn sizeu008_galois_l(a in arb_usize(), b in arb_u8()) {
            prop_assert!(conn_laws::galois_l(&SIZEU008, a, b));
        }
        #[test]
        fn sizeu008_kernel_l(b in arb_u8()) {
            prop_assert!(conn_laws::kernel_l(&SIZEU008, b));
        }
        #[test]
        fn sizeu016_galois_l(a in arb_usize(), b in arb_u16()) {
            prop_assert!(conn_laws::galois_l(&SIZEU016, a, b));
        }
        #[test]
        fn sizeu016_kernel_l(b in arb_u16()) {
            prop_assert!(conn_laws::kernel_l(&SIZEU016, b));
        }
        #[test]
        fn sizeu032_galois_l(a in arb_usize(), b in arb_u32()) {
            prop_assert!(conn_laws::galois_l(&SIZEU032, a, b));
        }
        #[test]
        fn sizeu032_kernel_l(b in arb_u32()) {
            prop_assert!(conn_laws::kernel_l(&SIZEU032, b));
        }
        #[test]
        fn sizeu064_galois_l(a in arb_usize(), b in arb_u64()) {
            prop_assert!(conn_laws::galois_l(&SIZEU064, a, b));
        }
        #[test]
        fn sizeu064_kernel_l(b in arb_u64()) {
            prop_assert!(conn_laws::kernel_l(&SIZEU064, b));
        }
        #[test]
        fn sizeu128_galois_l(a in arb_usize(), b in arb_u128()) {
            prop_assert!(conn_laws::galois_l(&SIZEU128, a, b));
        }
        #[test]
        fn sizeu128_kernel_l(b in arb_u128()) {
            prop_assert!(conn_laws::kernel_l(&SIZEU128, b));
        }
    }
}
