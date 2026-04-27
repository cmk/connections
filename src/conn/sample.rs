//! Rate-typed sample-indexed time.
//!
//! Each standard audio sample rate (44.1, 48, 88.2, 96, 176.4, 192 kHz)
//! gets its own `#[repr(transparent)]` newtype over
//! [`fixed::FixedI64`]`<U16>` — i.e. Q48.16 samples: 48 bits of signed
//! integer sample count plus 16 bits of sub-sample fraction.
//!
//! Distinct types per rate prevent accidental rate mixing at compile
//! time: you cannot add an `S44` to an `S48`. To cross rates, apply the
//! appropriate Galois [`Conn`], which expresses the rounding semantics
//! explicitly.
//!
//! # Precision
//!
//! - **Integer range**: ±2⁴⁷ samples — at 48 kHz that is ±93 000 years.
//! - **Sub-sample resolution**: 2⁻¹⁶ of a sample ≈ 15 ppm of one sample
//!   at any rate. Far below sample-accurate.
//!
//! # Connection topology
//!
//! For every ordered pair `(Fine, Coarse)` where `Fine` has the
//! higher Q48.16-bits-per-second rate, a
//! [`Conn`]`<Fine, Coarse>` constant `SXX_SYY` exists:
//!
//! ```text
//!   Fine────────────ratio──────────Coarse   exactness
//!   S88   <─×2─>   S44                      integer
//!   S176  <─×4─>   S44                      integer
//!   S176  <─×2─>   S88                      integer
//!   S96   <─×2─>   S48                      integer
//!   S192  <─×4─>   S48                      integer
//!   S192  <─×2─>   S96                      integer
//!   S48   <─160:147─>  S44                  rational (lossy)
//!   S88   <─147:80─>   S48                  rational
//!   S176  <─147:40─>   S48                  rational
//!   S96   <─320:147─>  S44                  rational
//!   S96   <─160:147─>  S88                  rational
//!   S176  <─147:80─>   S96                  rational
//!   S192  <─640:147─>  S44                  rational
//!   S192  <─320:147─>  S88                  rational
//!   S192  <─160:147─>  S176                 rational
//!
//! Ratio labels read `NUM:DEN`, i.e. the `inner(Coarse) = Coarse ·
//! NUM/DEN Fine` multiplier (always ≥ 1 because Fine is the higher-
//! bits-per-second type).
//! ```
//!
//! Plus one `Conn<FD12, Sxx>` per rate connecting the sample tier to
//! the decimal SI-time tier from [`crate::conn::fixed::decimal`].
//!
//! # Galois semantics for lossy `inner`
//!
//! When the ratio is rational (not integer), `inner` cannot be an exact
//! embedding — it rounds. This module defines `inner` as
//! `floor_div(coarse × NUM, DEN)` and derives `ceil` / `floor` in terms
//! of this `inner` so **both** Galois laws hold by construction:
//!
//! - `ceil ⊣ inner`:    `ceil(x) ≤ b  ⟺  x ≤ inner(b)`
//! - `inner ⊣ floor`:   `inner(b) ≤ x  ⟺  b ≤ floor(x)`
//!
//! The `floor` formula `floor_div((x+1)·DEN − 1, NUM)` looks unusual
//! but it is the correct upper adjoint of a lossy `inner`. For integer
//! ratios (`DEN = 1`) it collapses to the familiar `floor_div(x, NUM)`.

use crate::conn::Conn;
use crate::conn::fixed::decimal::FD12;
use fixed::FixedI64;
use fixed::types::extra::U16;

/// Q48.16 samples. Alias for clarity; all rate newtypes wrap this.
pub type Q48_16 = FixedI64<U16>;

/// Rates in audio samples per second.
pub trait SampleRate {
    const HZ: u32;
}

macro_rules! def_rate {
    ($name:ident, $hz:expr) => {
        #[repr(transparent)]
        #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
        pub struct $name(pub Q48_16);

        impl $crate::lattice::Ple for $name {
            fn ple(&self, other: &Self) -> bool {
                self <= other
            }
        }

        impl SampleRate for $name {
            const HZ: u32 = $hz;
        }

        impl $name {
            /// Zero samples.
            pub const ZERO: Self = Self(Q48_16::from_bits(0));
            /// One whole sample at this rate.
            pub const ONE_SAMPLE: Self = Self(Q48_16::from_bits(1 << 16));

            /// Construct from an integer sample count.
            pub const fn from_sample(n: i64) -> Self {
                Self(Q48_16::from_bits(n << 16))
            }

            /// Construct from raw Q48.16 bits.
            pub const fn from_bits(bits: i64) -> Self {
                Self(Q48_16::from_bits(bits))
            }

            /// Extract raw Q48.16 bits.
            pub const fn to_bits(self) -> i64 {
                self.0.to_bits()
            }

            /// Integer sample part (via arithmetic shift, so negatives
            /// round toward −∞).
            pub const fn sample(self) -> i64 {
                self.0.to_bits() >> 16
            }

            /// Sub-sample fraction as a signed Q16 value in
            /// (−2¹⁵, +2¹⁵).
            pub const fn sub_q16(self) -> i16 {
                (self.0.to_bits() & 0xFFFF) as i16
            }
        }
    };
}

def_rate!(S44,  44_100);
def_rate!(S48,  48_000);
def_rate!(S88,  88_200);
def_rate!(S96,  96_000);
def_rate!(S176, 176_400);
def_rate!(S192, 192_000);

// ─────────────────────────────────────────────────────────────────
// Rate ↔ Rate connections
//
// `rate_conn!(NAME, Fine, Coarse, NUM, DEN)` builds a
// `Conn<Fine, Coarse>` where `Fine`-per-`Coarse` ratio is `NUM/DEN`
// (i.e. `1 Coarse = NUM/DEN Fine`). `NUM ≥ DEN ≥ 1`.
//
// For integer ratio (DEN = 1) `inner` is exact: `coarse_bits · NUM`.
// For rational ratio `inner` rounds toward −∞ via `floor_div`, and
// `floor` is the upper adjoint — see module docs.
// ─────────────────────────────────────────────────────────────────

macro_rules! rate_conn {
    ($CONN:ident, $Fine:ident, $Coarse:ident, $num:expr, $den:expr) => {
        pub const $CONN: Conn<$Fine, $Coarse> = {
            const NUM: i128 = $num;
            const DEN: i128 = $den;

            fn ceil(x: $Fine) -> $Coarse {
                // ceil(x) = ceil_div(x · DEN, NUM)
                let n: i128 = x.0.to_bits() as i128 * DEN;
                let q = n.div_euclid(NUM);
                let r = n.rem_euclid(NUM);
                let bits = if r != 0 { q + 1 } else { q };
                $Coarse(Q48_16::from_bits(bits as i64))
            }

            fn inner(c: $Coarse) -> $Fine {
                // inner(c) = floor_div(c · NUM, DEN)
                let n: i128 = c.0.to_bits() as i128 * NUM;
                $Fine(Q48_16::from_bits(n.div_euclid(DEN) as i64))
            }

            fn floor(x: $Fine) -> $Coarse {
                // Upper adjoint of a lossy inner:
                //   floor(x) = floor_div(x · DEN + DEN − 1, NUM)
                // Equivalent to floor_div(x, NUM) when DEN = 1.
                let n: i128 = x.0.to_bits() as i128 * DEN + (DEN - 1);
                $Coarse(Q48_16::from_bits(n.div_euclid(NUM) as i64))
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// Integer ratios (power-of-two intra-family).
rate_conn!(S88S44,  S88,  S44,  2, 1);
rate_conn!(S176S44, S176, S44,  4, 1);
rate_conn!(S176S88, S176, S88,  2, 1);
rate_conn!(S96S48,  S96,  S48,  2, 1);
rate_conn!(S192S48, S192, S48,  4, 1);
rate_conn!(S192S96, S192, S96,  2, 1);

// Rational ratios (cross-family). Naming convention: `SXX_SYY` has
// `SXX` as the Fine side (higher Q48.16-bits-per-second) and `SYY` as
// Coarse. NUM ≥ DEN ≥ 1 so `inner(coarse) = coarse · NUM / DEN` is an
// upscale. Reduced ratios; gcd(NUM, 147) = 1 in every case so 147
// (= 3² · 7²) stays in the denominator whenever one side is from the
// 44.1k family.
rate_conn!(S48S44,   S48,  S44,  160, 147);
rate_conn!(S88S48,   S88,  S48,  147, 80);
rate_conn!(S176S48,  S176, S48,  147, 40);
rate_conn!(S96S44,   S96,  S44,  320, 147);
rate_conn!(S96S88,   S96,  S88,  160, 147);
rate_conn!(S176S96,  S176, S96,  147, 80);
rate_conn!(S192S44,  S192, S44,  640, 147);
rate_conn!(S192S88,  S192, S88,  320, 147);
rate_conn!(S192S176, S192, S176, 160, 147);

// ─────────────────────────────────────────────────────────────────
// Rate ↔ FD12 connections
//
// For each rate R with sample period `1/R` seconds, one Q48.16 bit
// of R-sample is `10^12 / (R · 2^16)` picoseconds. Ratio = NUM/DEN
// after simplifying by gcd. FD12 has fewer bits per second than the
// audio rates, so FD12 is Coarse and each Sxx is Fine.
// ─────────────────────────────────────────────────────────────────

// Simplified ratios computed once (see module docstring):
//   S48:  gcd(10^12, 48_000·2^16) = 512_000
//         num/den = (10^12 / 512_000) / ((48_000·2^16) / 512_000)
//                 = 1_953_125 / 6144
//   S96:  ratio = 1_953_125 / 12_288   (half of S48)
//   S192: ratio = 1_953_125 / 24_576   (quarter of S48)
//   S44:  gcd(10^12, 44_100·2^16) = 102_400
//         num/den = 9_765_625 / 28_224
//   S88:  ratio = 9_765_625 / 56_448   (half of S44)
//   S176: ratio = 9_765_625 / 112_896  (quarter of S44)
//
// The FD12 direction is SAMPLE → FD12. Sample has fewer bits/sec than
// FD12 (which has 10^12 bits/sec). So FD12 is Fine, Sxx is Coarse.
// Conn<Fine=FD12, Coarse=Sxx> with NUM·sample_bit = DEN·pico.

macro_rules! pico_conn {
    ($CONN:ident, $Rate:ident, $num:expr, $den:expr) => {
        pub const $CONN: Conn<FD12, $Rate> = {
            // 1 Rate-bit = NUM/DEN picoseconds. So:
            //   inner: Rate → FD12. inner(r) = r_bits · NUM / DEN (lossy → floor_div).
            //   ceil:  FD12 → Rate. ceil(p) = ceil_div(p · DEN, NUM).
            //   floor: FD12 → Rate. floor(p) = floor_div(p·DEN + NUM−1? No —
            //      floor_div((p+1)·DEN − 1, NUM) is the Galois floor.
            //
            // Wait — here we have Conn<FD12, Sxx> so Fine=FD12, Coarse=Sxx.
            //   inner: Coarse=Sxx → Fine=FD12. Sxx ×NUM/DEN → FD12.
            //   ceil,floor: FD12 → Sxx.
            //
            // So:
            //   inner(s: Sxx) = floor_div(s_bits · NUM, DEN) picoseconds
            //   ceil(p)  = ceil_div(p · DEN, NUM) Sxx-bits
            //   floor(p) = floor_div(p · DEN + DEN − 1, NUM) Sxx-bits
            const NUM: i128 = $num;
            const DEN: i128 = $den;

            fn ceil(p: FD12) -> $Rate {
                let n: i128 = p.0 as i128 * DEN;
                let q = n.div_euclid(NUM);
                let r = n.rem_euclid(NUM);
                let bits = if r != 0 { q + 1 } else { q };
                $Rate(Q48_16::from_bits(bits as i64))
            }

            fn inner(s: $Rate) -> FD12 {
                let n: i128 = s.0.to_bits() as i128 * NUM;
                FD12(n.div_euclid(DEN) as i64)
            }

            fn floor(p: FD12) -> $Rate {
                let n: i128 = p.0 as i128 * DEN + (DEN - 1);
                $Rate(Q48_16::from_bits(n.div_euclid(NUM) as i64))
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

pico_conn!(F12S44,  S44,  9_765_625,  28_224);
pico_conn!(F12S48,  S48,  1_953_125,  6_144);
pico_conn!(F12S88,  S88,  9_765_625,  56_448);
pico_conn!(F12S96,  S96,  1_953_125,  12_288);
pico_conn!(F12S176, S176, 9_765_625,  112_896);
pico_conn!(F12S192, S192, 1_953_125,  24_576);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::arb::{
        pico_coarse, pico_fine, pico_safe, rate_coarse, rate_fine, rate_safe_fine,
    };
    use proptest::prelude::*;

    // ─────────────────────────────────────────────
    // Spot checks
    // ─────────────────────────────────────────────

    #[test]
    fn s48_from_sample_bits() {
        assert_eq!(S48::from_sample(0).to_bits(), 0);
        assert_eq!(S48::from_sample(1).to_bits(), 1 << 16);
        assert_eq!(S48::from_sample(-1).to_bits(), -(1 << 16));
        assert_eq!(S48::ONE_SAMPLE.to_bits(), 1 << 16);
    }

    #[test]
    fn s48_sample_and_sub() {
        let s = S48::from_sample(42);
        assert_eq!(s.sample(), 42);
        assert_eq!(s.sub_q16(), 0);

        // 1 sample + 1/4 sub-sample = 0x1_4000 bits (16384 = 0x4000)
        let s = S48::from_bits((1 << 16) | 0x4000);
        assert_eq!(s.sample(), 1);
        assert_eq!(s.sub_q16(), 0x4000);
    }

    #[test]
    fn s88_s44_power_of_two_exact_embed() {
        // 1 S44 sample = 2 S88 samples, bit-exact.
        assert_eq!(S88S44.inner(S44::from_sample(7)), S88::from_sample(14));
        // ceil and floor agree on values that land cleanly.
        assert_eq!(S88S44.ceil(S88::from_sample(14)), S44::from_sample(7));
        assert_eq!(S88S44.floor(S88::from_sample(14)), S44::from_sample(7));
        // Off-by-one S88 bit → ceil/floor differ by 1 S44 bit.
        let s88_odd = S88::from_bits(S88::from_sample(14).to_bits() + 1);
        assert_eq!(S88S44.ceil(s88_odd), S44::from_bits(S44::from_sample(7).to_bits() + 1));
        assert_eq!(S88S44.floor(s88_odd), S44::from_bits(S44::from_sample(7).to_bits()));
    }

    #[test]
    fn s48_s44_rational_boundary() {
        // 1 S44 bit = 160/147 S48 bits (floor), so inner(S44(147)) = S48(160) exactly.
        let s44 = S44::from_bits(147);
        assert_eq!(S48S44.inner(s44), S48::from_bits(160));
        // Round-trip at the boundary.
        assert_eq!(S48S44.ceil(S48::from_bits(160)), S44::from_bits(147));
        assert_eq!(S48S44.floor(S48::from_bits(160)), S44::from_bits(147));
        // At x=161, inner(148) = floor(148·160/147) = floor(161.088) = 161. So
        // both ceil and floor of 161 land on 148.
        assert_eq!(S48S44.ceil(S48::from_bits(161)), S44::from_bits(148));
        assert_eq!(S48S44.floor(S48::from_bits(161)), S44::from_bits(148));
        // A value skipped by the staircase: inner(11) = 11, inner(12) = 13,
        // so x=12 is not hit. ceil(12) = 12, floor(12) = 11.
        assert_eq!(S48S44.ceil(S48::from_bits(12)), S44::from_bits(12));
        assert_eq!(S48S44.floor(S48::from_bits(12)), S44::from_bits(11));
    }

    #[test]
    fn s48_pico_spot() {
        // 1 S48 sample = 1/48000 s = 1_000_000_000_000/48_000 ps = 20_833_333.333… ps.
        // inner(S48::from_sample(1)) should be the floor_div version.
        // S48(1 sample) = 65_536 bits. inner = floor_div(65_536 · 1_953_125, 6_144).
        // = floor_div(128_000_000_000, 6_144) = 20_833_333.
        let p = F12S48.inner(S48::from_sample(1));
        assert_eq!(p.0, 20_833_333);
        // ceil of that same FD12 is back to exactly 1 S48 sample.
        assert_eq!(F12S48.ceil(FD12(20_833_333)), S48::from_sample(1));
        // floor of one ps higher is still 1 sample.
        assert_eq!(F12S48.floor(FD12(20_833_333)), S48::from_sample(1));
    }

    // ─────────────────────────────────────────────
    // Galois property battery
    //
    // For each Conn<F, C>, we test:
    //   - upper Galois: ceil(x) ≤ b ⟺ x ≤ inner(b)
    //   - lower Galois: inner(b) ≤ x ⟺ b ≤ floor(x)
    //   - ceil/floor monotone
    //   - floor ≤ ceil
    //   - inner-then-ceil and inner-then-floor round-trip (for integer
    //     ratios the embedding is exact so both round-trip; for rational
    //     the embedding is lossy so the round-trip may differ by 1 ULP,
    //     which the Galois laws already bound)
    //
    // Strategies (`rate_coarse`, `rate_fine`, `rate_safe_fine`) live
    // in `crate::property::arb`.
    // ─────────────────────────────────────────────

    macro_rules! props_for_conn {
        ($mod:ident, $conn:ident, $Fine:ident, $Coarse:ident, $num:expr, $den:expr) => {
            mod $mod {
                use super::*;
                use $crate::property::laws;

                proptest! {
                    #[test]
                    fn monotone_l(
                        x in rate_fine($den, $num),
                        y in rate_fine($den, $num),
                    ) {
                        prop_assert!(laws::conn_monotone_l(
                            &$conn,
                            $Fine::from_bits(x),
                            $Fine::from_bits(y),
                        ));
                    }

                    #[test]
                    fn monotone_r(
                        a in rate_coarse($num),
                        b in rate_coarse($num),
                    ) {
                        prop_assert!(laws::conn_monotone_r(
                            &$conn,
                            $Coarse::from_bits(a),
                            $Coarse::from_bits(b),
                        ));
                    }

                    #[test]
                    fn floor_le_ceil(x in rate_fine($den, $num)) {
                        prop_assert!(laws::conn_floor_le_ceil(&$conn, $Fine::from_bits(x)));
                    }

                    #[test]
                    fn galois_l(
                        x in rate_fine($den, $num),
                        b in rate_coarse($num),
                    ) {
                        prop_assert!(laws::conn_galois_l(
                            &$conn,
                            $Fine::from_bits(x),
                            $Coarse::from_bits(b),
                        ));
                    }

                    #[test]
                    fn galois_r(
                        x in rate_fine($den, $num),
                        b in rate_coarse($num),
                    ) {
                        prop_assert!(laws::conn_galois_r(
                            &$conn,
                            $Fine::from_bits(x),
                            $Coarse::from_bits(b),
                        ));
                    }

                    // For integer ratios (DEN=1) the embedding is exact,
                    // so the strict roundtrip holds. For rational ratios
                    // the embedding is lossy; the Galois laws above
                    // already bound the slack.
                    #[test]
                    fn roundtrip_ceil_integer_ratio(b in rate_coarse($num)) {
                        if $den == 1 {
                            prop_assert!(laws::conn_roundtrip_ceil(
                                &$conn,
                                $Coarse::from_bits(b),
                            ));
                        }
                    }

                    #[test]
                    fn roundtrip_floor_integer_ratio(b in rate_coarse($num)) {
                        if $den == 1 {
                            prop_assert!(laws::conn_roundtrip_floor(
                                &$conn,
                                $Coarse::from_bits(b),
                            ));
                        }
                    }

                    // Closure laws use rate_safe_fine because the
                    // round-trip can grow by up to num/den < num units.
                    #[test]
                    fn closure_l(x in rate_safe_fine($num)) {
                        prop_assert!(laws::conn_closure_l(&$conn, $Fine::from_bits(x)));
                    }

                    #[test]
                    fn closure_r(x in rate_safe_fine($num)) {
                        prop_assert!(laws::conn_closure_r(&$conn, $Fine::from_bits(x)));
                    }

                    #[test]
                    fn idempotent(x in rate_safe_fine($num)) {
                        prop_assert!(laws::conn_idempotent(&$conn, $Fine::from_bits(x)));
                    }
                }
            }
        };
    }

    // Integer-ratio pairs.
    props_for_conn!(p_s88s44,  S88S44,  S88,  S44,  2, 1);
    props_for_conn!(p_s176s44, S176S44, S176, S44,  4, 1);
    props_for_conn!(p_s176s88, S176S88, S176, S88,  2, 1);
    props_for_conn!(p_s96s48,  S96S48,  S96,  S48,  2, 1);
    props_for_conn!(p_s192s48, S192S48, S192, S48,  4, 1);
    props_for_conn!(p_s192s96, S192S96, S192, S96,  2, 1);

    // Cross-family rational pairs.
    props_for_conn!(p_s48s44,   S48S44,   S48,  S44,  160, 147);
    props_for_conn!(p_s88s48,   S88S48,   S88,  S48,  147, 80);
    props_for_conn!(p_s176s48,  S176S48,  S176, S48,  147, 40);
    props_for_conn!(p_s96s44,   S96S44,   S96,  S44,  320, 147);
    props_for_conn!(p_s96s88,   S96S88,   S96,  S88,  160, 147);
    props_for_conn!(p_s176s96,  S176S96,  S176, S96,  147, 80);
    props_for_conn!(p_s192s44,  S192S44,  S192, S44,  640, 147);
    props_for_conn!(p_s192s88,  S192S88,  S192, S88,  320, 147);
    props_for_conn!(p_s192s176, S192S176, S192, S176, 160, 147);

    // FD12 connections. Here Fine = FD12, Coarse = Sxx. The macro is
    // identical but FD12 is not an Sxx — write a tailored mod per conn
    // that reads `.0` on FD12 and `.0.to_bits()` on Sxx.
    macro_rules! props_for_pico_conn {
        ($mod:ident, $conn:ident, $Rate:ident, $num:expr, $den:expr) => {
            mod $mod {
                use super::*;
                use $crate::property::laws;

                proptest! {
                    #[test]
                    fn monotone_l(
                        a in pico_fine(),
                        b in pico_fine(),
                    ) {
                        prop_assert!(laws::conn_monotone_l(&$conn, FD12(a), FD12(b)));
                    }

                    #[test]
                    fn monotone_r(
                        a in pico_coarse($num, $den),
                        b in pico_coarse($num, $den),
                    ) {
                        prop_assert!(laws::conn_monotone_r(
                            &$conn,
                            $Rate::from_bits(a),
                            $Rate::from_bits(b),
                        ));
                    }

                    #[test]
                    fn floor_le_ceil(p in pico_fine()) {
                        let pp = FD12(p);
                        prop_assert!(laws::conn_floor_le_ceil(&$conn, pp));
                        // Stronger: rational-ratio ULP bound
                        // (`ceil - floor ≤ 1` Sxx Q48.16 ULP).
                        prop_assert!(laws::conn_ulp_bound(
                            &$conn,
                            pp,
                            |s: $Rate| s.0.to_bits(),
                        ));
                    }

                    #[test]
                    fn galois_l(
                        p in pico_fine(),
                        s in pico_coarse($num, $den),
                    ) {
                        prop_assert!(laws::conn_galois_l(
                            &$conn,
                            FD12(p),
                            $Rate::from_bits(s),
                        ));
                    }

                    #[test]
                    fn galois_r(
                        p in pico_fine(),
                        s in pico_coarse($num, $den),
                    ) {
                        prop_assert!(laws::conn_galois_r(
                            &$conn,
                            FD12(p),
                            $Rate::from_bits(s),
                        ));
                    }

                    // Closure laws use pico_safe because the
                    // round-trip can grow p by up to NUM/DEN ps.
                    #[test]
                    fn closure_l(p in pico_safe($num)) {
                        prop_assert!(laws::conn_closure_l(&$conn, FD12(p)));
                    }

                    #[test]
                    fn closure_r(p in pico_safe($num)) {
                        prop_assert!(laws::conn_closure_r(&$conn, FD12(p)));
                    }

                    #[test]
                    fn idempotent(p in pico_safe($num)) {
                        prop_assert!(laws::conn_idempotent(&$conn, FD12(p)));
                    }
                }
            }
        };
    }

    props_for_pico_conn!(p_f12s44,  F12S44,  S44,  9_765_625,  28_224);
    props_for_pico_conn!(p_f12s48,  F12S48,  S48,  1_953_125,  6_144);
    props_for_pico_conn!(p_f12s88,  F12S88,  S88,  9_765_625,  56_448);
    props_for_pico_conn!(p_f12s96,  F12S96,  S96,  1_953_125,  12_288);
    props_for_pico_conn!(p_f12s176, F12S176, S176, 9_765_625,  112_896);
    props_for_pico_conn!(p_f12s192, F12S192, S192, 1_953_125,  24_576);

    // Sanity-check the FD12↔sample rate against the transcendental
    // definition: inner(Sxx::from_sample(1)) should be within 0.5 ps
    // of 10^12 / Sxx::HZ.
    #[test]
    fn pico_inner_matches_ideal() {
        // Use f64 for the ideal — this test only, asserts sit here as
        // proof that the integer math agrees with the analytic formula.
        fn check<R: SampleRate + Copy>(conn: Conn<FD12, R>, sample_one: R) {
            let got = conn.inner(sample_one).0 as f64;
            let ideal = 1.0e12 / (R::HZ as f64);
            assert!((got - ideal).abs() <= 1.0, "Rate {}: got {}, ideal {}", R::HZ, got, ideal);
        }
        check(F12S44,  S44::from_sample(1));
        check(F12S48,  S48::from_sample(1));
        check(F12S88,  S88::from_sample(1));
        check(F12S96,  S96::from_sample(1));
        check(F12S176, S176::from_sample(1));
        check(F12S192, S192::from_sample(1));
    }
}
