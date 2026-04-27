//! Unsigned-integer connections: `u_N → u_M` widening and `i_N → u_M`
//! saturating cross-sign casts.
//!
//! Two families, both single-sided ([`Conn::new_left`]):
//!
//! - **`U??U??`** — `Conn<u_N, u_M>` for `N < M`. `ceil` is the
//!   `as`-upcast (lossless); `inner` saturates at `u_N::MAX`.
//! - **`I??U??`** — `Conn<i_N, u_M>` for `N ≤ M`. `ceil` clips negative
//!   inputs to `0`, then upcasts; `inner` saturates at `i_N::MAX`. The
//!   `bits(i_N) ≤ bits(u_M)` constraint guarantees the positive half of
//!   `i_N` fits in `u_M` losslessly.
//!
//! Mirrors `Data.Connection.Word` from the upstream Haskell `connections`
//! library — see the type-code legend in [`crate`].

use crate::conn::Conn;

// ── U??U??: unsigned widen + saturating-narrow inner ────────────────

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

uint_uint!(U008U016, u8, u16);
uint_uint!(U008U032, u8, u32);
uint_uint!(U008U064, u8, u64);
uint_uint!(U008U128, u8, u128);
uint_uint!(U016U032, u16, u32);
uint_uint!(U016U064, u16, u64);
uint_uint!(U016U128, u16, u128);
uint_uint!(U032U064, u32, u64);
uint_uint!(U032U128, u32, u128);
uint_uint!(U064U128, u64, u128);

// ── I??U??: signed → unsigned saturating cast (saturate at 0) ───────

macro_rules! int_uint {
    ($NAME:ident, $A:ty, $B:ty) => {
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

int_uint!(I008U008, i8, u8);
int_uint!(I008U016, i8, u16);
int_uint!(I016U016, i16, u16);
int_uint!(I008U032, i8, u32);
int_uint!(I016U032, i16, u32);
int_uint!(I032U032, i32, u32);
int_uint!(I008U064, i8, u64);
int_uint!(I016U064, i16, u64);
int_uint!(I032U064, i32, u64);
int_uint!(I064U064, i64, u64);
int_uint!(I008U128, i8, u128);
int_uint!(I016U128, i16, u128);
int_uint!(I032U128, i32, u128);
int_uint!(I064U128, i64, u128);
int_uint!(I128U128, i128, u128);

#[cfg(test)]
mod tests {
    use super::*;

    // ── Spot checks ────────────────────────────────────────────────

    #[test]
    fn uint_widening_ceil_at_boundaries() {
        assert_eq!(U008U016.ceil(0u8), 0u16);
        assert_eq!(U008U016.ceil(u8::MAX), u8::MAX as u16);
        assert_eq!(U008U032.ceil(u8::MAX), u8::MAX as u32);
        assert_eq!(U008U064.ceil(u8::MAX), u8::MAX as u64);
        assert_eq!(U016U032.ceil(u16::MAX), u16::MAX as u32);
        assert_eq!(U016U064.ceil(u16::MAX), u16::MAX as u64);
        assert_eq!(U032U064.ceil(u32::MAX), u32::MAX as u64);
    }

    #[test]
    fn uint_widening_inner_saturates_at_source_max() {
        assert_eq!(U008U016.inner(u16::MAX), u8::MAX);
        assert_eq!(U008U032.inner(u32::MAX), u8::MAX);
        assert_eq!(U008U064.inner(u64::MAX), u8::MAX);
        assert_eq!(U016U032.inner(u32::MAX), u16::MAX);
        assert_eq!(U016U064.inner(u64::MAX), u16::MAX);
        assert_eq!(U032U064.inner(u64::MAX), u32::MAX);
        // Below cap is identity-cast back.
        assert_eq!(U008U016.inner(50), 50);
        assert_eq!(U016U064.inner(60_000), 60_000);
    }

    #[test]
    fn int_uint_ceil_clips_negatives_to_zero() {
        assert_eq!(I008U008.ceil(-5), 0);
        assert_eq!(I008U016.ceil(-128), 0);
        assert_eq!(I016U032.ceil(-32_768), 0);
        assert_eq!(I032U064.ceil(-1), 0);
        assert_eq!(I064U064.ceil(i64::MIN), 0);
    }

    #[test]
    fn int_uint_ceil_passes_non_negative() {
        assert_eq!(I008U008.ceil(0), 0);
        assert_eq!(I008U008.ceil(127), 127);
        assert_eq!(I008U016.ceil(127), 127);
        assert_eq!(I016U032.ceil(32_767), 32_767);
        assert_eq!(I032U064.ceil(i32::MAX), i32::MAX as u64);
        assert_eq!(I064U064.ceil(i64::MAX), i64::MAX as u64);
    }

    #[test]
    fn int_uint_inner_saturates_at_source_max() {
        assert_eq!(I008U008.inner(u8::MAX), i8::MAX);
        assert_eq!(I008U016.inner(u16::MAX), i8::MAX);
        assert_eq!(I016U016.inner(u16::MAX), i16::MAX);
        assert_eq!(I008U032.inner(u32::MAX), i8::MAX);
        assert_eq!(I032U032.inner(u32::MAX), i32::MAX);
        assert_eq!(I008U064.inner(u64::MAX), i8::MAX);
        assert_eq!(I064U064.inner(u64::MAX), i64::MAX);
        // Below cap is identity-cast back.
        assert_eq!(I016U032.inner(20_000), 20_000);
    }

    #[test]
    fn int_uint_galois_at_mid_positive() {
        // Exercises the active branch (`a >= 0`, ceil widens, inner is
        // below cap so identity-casts back) — proptest covers this too,
        // but proptest's `any::<iN>()` weights heavily toward boundary
        // values; this fixes a representative middle point.
        for (a, b) in [(50i8, 100u16), (50i8, 49u16), (100i8, 100u16)] {
            assert_eq!(
                I008U016.ceil(a) <= b,
                a <= I008U016.inner(b),
                "I008U016 galois_upper @ ({a}, {b})"
            );
        }
    }

    // ── Property tests ─────────────────────────────────────────────
    //
    // Single-sided Galois connection (`Conn::new_left`) laws:
    //
    //   galois_upper:   ceil(a) ≤ b  ⟺  a ≤ inner(b)
    //   ceil_monotone:  a1 ≤ a2  ⟹  ceil(a1) ≤ ceil(a2)
    //   inner_monotone: b1 ≤ b2  ⟹  inner(b1) ≤ inner(b2)
    //   kernel:         ceil(inner(b)) ≤ b

    macro_rules! single_sided_props {
        ($mod_name:ident, $CONN:expr, $arb_src:expr, $arb_tgt:expr) => {
            mod $mod_name {
                use super::*;
                use proptest::prelude::*;

                proptest! {
                    #[test]
                    fn galois_upper(a in $arb_src, b in $arb_tgt) {
                        prop_assert_eq!($CONN.ceil(a) <= b, a <= $CONN.inner(b));
                    }

                    #[test]
                    fn ceil_monotone(a1 in $arb_src, a2 in $arb_src) {
                        let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                        prop_assert!($CONN.ceil(lo) <= $CONN.ceil(hi));
                    }

                    #[test]
                    fn inner_monotone(b1 in $arb_tgt, b2 in $arb_tgt) {
                        let (lo, hi) = if b1 <= b2 { (b1, b2) } else { (b2, b1) };
                        prop_assert!($CONN.inner(lo) <= $CONN.inner(hi));
                    }

                    #[test]
                    fn kernel(b in $arb_tgt) {
                        prop_assert!($CONN.ceil($CONN.inner(b)) <= b);
                    }
                }
            }
        };
    }

    single_sided_props!(u008u016, U008U016, any::<u8>(), any::<u16>());
    single_sided_props!(u008u032, U008U032, any::<u8>(), any::<u32>());
    single_sided_props!(u008u064, U008U064, any::<u8>(), any::<u64>());
    single_sided_props!(u008u128, U008U128, any::<u8>(), any::<u128>());
    single_sided_props!(u016u032, U016U032, any::<u16>(), any::<u32>());
    single_sided_props!(u016u064, U016U064, any::<u16>(), any::<u64>());
    single_sided_props!(u016u128, U016U128, any::<u16>(), any::<u128>());
    single_sided_props!(u032u064, U032U064, any::<u32>(), any::<u64>());
    single_sided_props!(u032u128, U032U128, any::<u32>(), any::<u128>());
    single_sided_props!(u064u128, U064U128, any::<u64>(), any::<u128>());

    single_sided_props!(i008u008, I008U008, any::<i8>(), any::<u8>());
    single_sided_props!(i008u016, I008U016, any::<i8>(), any::<u16>());
    single_sided_props!(i016u016, I016U016, any::<i16>(), any::<u16>());
    single_sided_props!(i008u032, I008U032, any::<i8>(), any::<u32>());
    single_sided_props!(i016u032, I016U032, any::<i16>(), any::<u32>());
    single_sided_props!(i032u032, I032U032, any::<i32>(), any::<u32>());
    single_sided_props!(i008u064, I008U064, any::<i8>(), any::<u64>());
    single_sided_props!(i016u064, I016U064, any::<i16>(), any::<u64>());
    single_sided_props!(i032u064, I032U064, any::<i32>(), any::<u64>());
    single_sided_props!(i064u064, I064U064, any::<i64>(), any::<u64>());
    single_sided_props!(i008u128, I008U128, any::<i8>(), any::<u128>());
    single_sided_props!(i016u128, I016U128, any::<i16>(), any::<u128>());
    single_sided_props!(i032u128, I032U128, any::<i32>(), any::<u128>());
    single_sided_props!(i064u128, I064U128, any::<i64>(), any::<u128>());
    single_sided_props!(i128u128, I128U128, any::<i128>(), any::<u128>());
}
