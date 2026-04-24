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
//! Plus one `Conn<Pico, Sxx>` per rate connecting the sample tier to
//! the decimal SI-time tier from [`crate::conn::fixed`].
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
use crate::conn::fixed::Pico;
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
// Rate ↔ Pico connections
//
// For each rate R with sample period `1/R` seconds, one Q48.16 bit
// of R-sample is `10^12 / (R · 2^16)` picoseconds. Ratio = NUM/DEN
// after simplifying by gcd. Pico has fewer bits per second than the
// audio rates, so Pico is Coarse and each Sxx is Fine.
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
// The Pico direction is SAMPLE → Pico. Sample has fewer bits/sec than
// Pico (which has 10^12 bits/sec). So Pico is Fine, Sxx is Coarse.
// Conn<Fine=Pico, Coarse=Sxx> with NUM·sample_bit = DEN·pico.

macro_rules! pico_conn {
    ($CONN:ident, $Rate:ident, $num:expr, $den:expr) => {
        pub const $CONN: Conn<Pico, $Rate> = {
            // 1 Rate-bit = NUM/DEN picoseconds. So:
            //   inner: Rate → Pico. inner(r) = r_bits · NUM / DEN (lossy → floor_div).
            //   ceil:  Pico → Rate. ceil(p) = ceil_div(p · DEN, NUM).
            //   floor: Pico → Rate. floor(p) = floor_div(p·DEN + NUM−1? No —
            //      floor_div((p+1)·DEN − 1, NUM) is the Galois floor.
            //
            // Wait — here we have Conn<Pico, Sxx> so Fine=Pico, Coarse=Sxx.
            //   inner: Coarse=Sxx → Fine=Pico. Sxx ×NUM/DEN → Pico.
            //   ceil,floor: Pico → Sxx.
            //
            // So:
            //   inner(s: Sxx) = floor_div(s_bits · NUM, DEN) picoseconds
            //   ceil(p)  = ceil_div(p · DEN, NUM) Sxx-bits
            //   floor(p) = floor_div(p · DEN + DEN − 1, NUM) Sxx-bits
            const NUM: i128 = $num;
            const DEN: i128 = $den;

            fn ceil(p: Pico) -> $Rate {
                let n: i128 = p.0 as i128 * DEN;
                let q = n.div_euclid(NUM);
                let r = n.rem_euclid(NUM);
                let bits = if r != 0 { q + 1 } else { q };
                $Rate(Q48_16::from_bits(bits as i64))
            }

            fn inner(s: $Rate) -> Pico {
                let n: i128 = s.0.to_bits() as i128 * NUM;
                Pico(n.div_euclid(DEN) as i64)
            }

            fn floor(p: Pico) -> $Rate {
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
        // ceil of that same Pico is back to exactly 1 S48 sample.
        assert_eq!(F12S48.ceil(Pico(20_833_333)), S48::from_sample(1));
        // floor of one ps higher is still 1 sample.
        assert_eq!(F12S48.floor(Pico(20_833_333)), S48::from_sample(1));
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
    // To keep NUM overflows tame, bound `Coarse` bits so
    // |bits · NUM| < i128::MAX / 2.
    // ─────────────────────────────────────────────

    fn bounded_coarse(num: i128) -> impl Strategy<Value = i64> {
        // `inner(c)` computes `c · NUM / DEN` and casts to i64. For
        // that to fit, |c · NUM| must be < i64::MAX, so
        // |c| < i64::MAX / NUM.
        let limit = (i64::MAX as i128 / num.max(1)) as i64;
        let limit = limit.max(1);
        prop_oneof![
            1 => Just(0_i64),
            1 => Just(1_i64),
            1 => Just(-1_i64),
            1 => Just(limit),
            1 => Just(-limit),
            5 => -limit..=limit,
        ]
    }

    fn bounded_fine(den: i128, _num: i128) -> impl Strategy<Value = i64> {
        // ceil / floor compute `x · DEN ± (DEN-1)` as i128 (never
        // overflows for DEN ≤ 10^7 and x in i64). The i64 cast of the
        // result fits because dividing by NUM ≥ DEN shrinks or
        // preserves magnitude. Any i64 is safe; bias to boundaries.
        let near_max = i64::MAX - den as i64 - 1;
        prop_oneof![
            1 => Just(0_i64),
            1 => Just(1_i64),
            1 => Just(-1_i64),
            1 => Just(near_max),
            1 => Just(-near_max),
            5 => -near_max..=near_max,
        ]
    }

    /// Fine-side strategy restricted to values whose round-trip
    /// `inner(ceil(_))` fits in i64.
    ///
    /// `ceil(Fine(x))` produces `Coarse(q)` where
    /// `q = ⌈x · den / num⌉`. `inner(Coarse(q)) = Fine(q · num / den)`.
    /// Algebra: `q · num / den − x ∈ [0, num/den)`, so the round-trip
    /// output can exceed the input by up to `num − 1`. To keep the
    /// output in i64, cap `|x| ≤ i64::MAX − num`.
    ///
    /// Use for properties that round-trip through `inner` (closure,
    /// idempotent). Non-round-trip properties can use the looser
    /// [`bounded_fine`] instead.
    fn safe_fine_rate(num: i128) -> impl Strategy<Value = i64> {
        // All current NUM values (≤ 640) fit trivially in i64. The
        // i128 parameter carries the API shape; `as i64` would
        // silently truncate a future NUM > i64::MAX, so use
        // try_from so the assumption trips in tests if violated.
        let guard: i64 = i64::try_from(num).expect("NUM fits i64");
        let limit = i64::MAX - guard;
        prop_oneof![
            1 => Just(0_i64),
            1 => Just(1_i64),
            1 => Just(-1_i64),
            1 => Just(limit),
            1 => Just(-limit),
            5 => -limit..=limit,
        ]
    }

    macro_rules! props_for_conn {
        ($mod:ident, $conn:ident, $Fine:ident, $Coarse:ident, $num:expr, $den:expr) => {
            mod $mod {
                use super::*;

                proptest! {
                    #[test]
                    fn ceil_monotone(
                        x in bounded_fine($den, $num),
                        y in bounded_fine($den, $num),
                    ) {
                        let (lo, hi) = if x <= y { ($Fine::from_bits(x), $Fine::from_bits(y)) }
                                       else     { ($Fine::from_bits(y), $Fine::from_bits(x)) };
                        prop_assert!($conn.ceil(lo) <= $conn.ceil(hi));
                    }

                    #[test]
                    fn floor_monotone(
                        x in bounded_fine($den, $num),
                        y in bounded_fine($den, $num),
                    ) {
                        let (lo, hi) = if x <= y { ($Fine::from_bits(x), $Fine::from_bits(y)) }
                                       else     { ($Fine::from_bits(y), $Fine::from_bits(x)) };
                        prop_assert!($conn.floor(lo) <= $conn.floor(hi));
                    }

                    #[test]
                    fn inner_monotone(
                        a in bounded_coarse($num),
                        b in bounded_coarse($num),
                    ) {
                        let (lo, hi) = if a <= b { ($Coarse::from_bits(a), $Coarse::from_bits(b)) }
                                       else     { ($Coarse::from_bits(b), $Coarse::from_bits(a)) };
                        prop_assert!($conn.inner(lo) <= $conn.inner(hi));
                    }

                    #[test]
                    fn floor_le_ceil(x in bounded_fine($den, $num)) {
                        let fx = $Fine::from_bits(x);
                        prop_assert!($conn.floor(fx) <= $conn.ceil(fx));
                    }

                    #[test]
                    fn galois_upper(
                        x in bounded_fine($den, $num),
                        b in bounded_coarse($num),
                    ) {
                        let fx = $Fine::from_bits(x);
                        let cb = $Coarse::from_bits(b);
                        prop_assert_eq!(
                            $conn.ceil(fx) <= cb,
                            fx <= $conn.inner(cb)
                        );
                    }

                    #[test]
                    fn galois_lower(
                        x in bounded_fine($den, $num),
                        b in bounded_coarse($num),
                    ) {
                        let fx = $Fine::from_bits(x);
                        let cb = $Coarse::from_bits(b);
                        prop_assert_eq!(
                            $conn.inner(cb) <= fx,
                            cb <= $conn.floor(fx)
                        );
                    }

                    #[test]
                    fn inner_then_ceil_integer_ratio(b in bounded_coarse($num)) {
                        // For DEN = 1 the embedding is exact, so
                        // ceil(inner(b)) == b and floor(inner(b)) == b.
                        // For DEN > 1 the embedding is lossy; skip this
                        // strict roundtrip (covered by Galois laws).
                        if $den == 1 {
                            let cb = $Coarse::from_bits(b);
                            prop_assert_eq!($conn.ceil($conn.inner(cb)), cb);
                            prop_assert_eq!($conn.floor($conn.inner(cb)), cb);
                        }
                    }

                    // Closure: a ≤ inner(ceil(a))
                    // Uses safe_fine_rate because the round-trip can
                    // grow by up to num/den < num units; see its docs.
                    #[test]
                    fn prop_closure_l(x in safe_fine_rate($num)) {
                        let a = $Fine::from_bits(x);
                        prop_assert!(a <= $conn.inner($conn.ceil(a)));
                    }

                    // Closure dual: inner(floor(a)) ≤ a
                    #[test]
                    fn prop_closure_r(x in safe_fine_rate($num)) {
                        let a = $Fine::from_bits(x);
                        prop_assert!($conn.inner($conn.floor(a)) <= a);
                    }

                    // Idempotent: inner∘ceil is idempotent on its image.
                    #[test]
                    fn prop_idempotent(x in safe_fine_rate($num)) {
                        let a = $Fine::from_bits(x);
                        let once = $conn.inner($conn.ceil(a));
                        let twice = $conn.inner($conn.ceil(once));
                        prop_assert_eq!(once, twice);
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

    // Pico connections. Here Fine = Pico, Coarse = Sxx. The macro is
    // identical but Pico is not an Sxx — write a tailored mod per conn
    // that reads `.0` on Pico and `.0.to_bits()` on Sxx.
    macro_rules! props_for_pico_conn {
        ($mod:ident, $conn:ident, $Rate:ident, $num:expr, $den:expr) => {
            mod $mod {
                use super::*;

                fn pico_bounded() -> impl Strategy<Value = i64> {
                    // ceil/floor of Pico produce Sxx-bits: pico · DEN / NUM,
                    // which shrinks by DEN/NUM < 1, so any i64 fits.
                    // `pico · DEN` stays in i128 trivially for DEN ≤ 113_000.
                    prop_oneof![
                        1 => Just(0_i64),
                        1 => Just(1_i64),
                        1 => Just(-1_i64),
                        1 => Just(i64::MAX),
                        1 => Just(i64::MIN + 1),
                        5 => any::<i64>(),
                    ]
                }

                fn sample_bounded() -> impl Strategy<Value = i64> {
                    // inner(Sxx) returns Pico(bits · NUM / DEN). Fits i64
                    // iff |bits| < i64::MAX · DEN / NUM.
                    let limit = (i64::MAX as i128 * $den / ($num as i128).max(1)) as i64;
                    let limit = limit.max(1);
                    prop_oneof![
                        1 => Just(0_i64),
                        1 => Just(1_i64),
                        1 => Just(-1_i64),
                        1 => Just(limit),
                        1 => Just(-limit),
                        5 => -limit..=limit,
                    ]
                }

                /// Pico bits restricted so `inner(ceil(p))` fits i64.
                ///
                /// Round-trip growth is at most NUM/DEN < NUM picoseconds
                /// (worst-case: ceil rounds up by < 1 Sxx-bit, inner
                /// scales that back up by NUM/DEN). Cap at
                /// `|p| ≤ i64::MAX − NUM`.
                fn safe_pico_bounded() -> impl Strategy<Value = i64> {
                    // All current NUM values (max 9_765_625) fit in
                    // i64. `as i64` would silently truncate a future
                    // NUM > i64::MAX; try_from documents the
                    // assumption and fails loudly if violated.
                    let guard: i64 =
                        i64::try_from($num as i128).expect("NUM fits i64");
                    let limit = i64::MAX - guard;
                    prop_oneof![
                        1 => Just(0_i64),
                        1 => Just(1_i64),
                        1 => Just(-1_i64),
                        1 => Just(limit),
                        1 => Just(-limit),
                        5 => -limit..=limit,
                    ]
                }

                proptest! {
                    #[test]
                    fn ceil_monotone(
                        a in pico_bounded(),
                        b in pico_bounded(),
                    ) {
                        let (lo, hi) = if a <= b { (Pico(a), Pico(b)) }
                                       else     { (Pico(b), Pico(a)) };
                        prop_assert!($conn.ceil(lo) <= $conn.ceil(hi));
                    }

                    #[test]
                    fn floor_monotone(
                        a in pico_bounded(),
                        b in pico_bounded(),
                    ) {
                        let (lo, hi) = if a <= b { (Pico(a), Pico(b)) }
                                       else     { (Pico(b), Pico(a)) };
                        prop_assert!($conn.floor(lo) <= $conn.floor(hi));
                    }

                    #[test]
                    fn inner_monotone(
                        a in sample_bounded(),
                        b in sample_bounded(),
                    ) {
                        let (lo, hi) = if a <= b { ($Rate::from_bits(a), $Rate::from_bits(b)) }
                                       else     { ($Rate::from_bits(b), $Rate::from_bits(a)) };
                        prop_assert!($conn.inner(lo) <= $conn.inner(hi));
                    }

                    #[test]
                    fn floor_le_ceil(p in pico_bounded()) {
                        prop_assert!($conn.floor(Pico(p)) <= $conn.ceil(Pico(p)));
                    }

                    #[test]
                    fn ulp_bound(p in pico_bounded()) {
                        // Rate ↔ Pico is a monotone fractional ratio;
                        // ceil and floor can differ by at most one
                        // Sxx Q48.16 ULP for any input.
                        let c = $conn.ceil(Pico(p)).0.to_bits();
                        let f = $conn.floor(Pico(p)).0.to_bits();
                        prop_assert!(c - f <= 1, "ceil - floor = {}", c - f);
                    }

                    #[test]
                    fn galois_upper(
                        p in pico_bounded(),
                        s in sample_bounded(),
                    ) {
                        let pp = Pico(p);
                        let ss = $Rate::from_bits(s);
                        prop_assert_eq!(
                            $conn.ceil(pp) <= ss,
                            pp <= $conn.inner(ss)
                        );
                    }

                    #[test]
                    fn galois_lower(
                        p in pico_bounded(),
                        s in sample_bounded(),
                    ) {
                        let pp = Pico(p);
                        let ss = $Rate::from_bits(s);
                        prop_assert_eq!(
                            $conn.inner(ss) <= pp,
                            ss <= $conn.floor(pp)
                        );
                    }

                    // Closure: a ≤ inner(ceil(a))
                    // Uses safe_pico_bounded because the round-trip
                    // can grow p by up to NUM/DEN picoseconds.
                    #[test]
                    fn prop_closure_l(p in safe_pico_bounded()) {
                        let a = Pico(p);
                        prop_assert!(a <= $conn.inner($conn.ceil(a)));
                    }

                    // Closure dual: inner(floor(a)) ≤ a
                    #[test]
                    fn prop_closure_r(p in safe_pico_bounded()) {
                        let a = Pico(p);
                        prop_assert!($conn.inner($conn.floor(a)) <= a);
                    }

                    // Idempotent: inner∘ceil is idempotent on its image.
                    #[test]
                    fn prop_idempotent(p in safe_pico_bounded()) {
                        let a = Pico(p);
                        let once = $conn.inner($conn.ceil(a));
                        let twice = $conn.inner($conn.ceil(once));
                        prop_assert_eq!(once, twice);
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

    // Sanity-check the Pico↔sample rate against the transcendental
    // definition: inner(Sxx::from_sample(1)) should be within 0.5 ps
    // of 10^12 / Sxx::HZ.
    #[test]
    fn pico_inner_matches_ideal() {
        // Use f64 for the ideal — this test only, asserts sit here as
        // proof that the integer math agrees with the analytic formula.
        fn check<R: SampleRate + Copy>(conn: Conn<Pico, R>, sample_one: R) {
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
