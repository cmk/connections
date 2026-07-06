//! IPv4 / IPv6 / IpAddr connections.
//!
//! Five Conns covering the std-library IP types:
//!
//! - [`U032IPV4`] — `Conn<u32, Ipv4Addr>` total bijection via
//!   `Ipv4Addr::{from,to}_bits`. Constructed with the [`conn_k!`](crate::conn_k) macro;
//!   both Galois laws and `floor_le_ceil` hold trivially.
//! - [`U128IPV6`] — `Conn<u128, Ipv6Addr>` total bijection, same
//!   shape.
//! - [`IPV6IPV4`] — `Conn<Ipv6Addr, Extended<Ipv4Addr>>`, the
//!   v4-mapped bridge. Full triple (the [`conn_k!`](crate::conn_k) macro) with asymmetric
//!   ceil/floor outside the v4-mapped block; lawful (passes
//!   `floor_le_ceil`) because `inner` is order-reflecting — the
//!   v4-mapped block sits strictly inside `Ipv6Addr`, giving "room"
//!   between `inner(NegInf) = ::` and `inner(Finite(0.0.0.0)) =
//!   ::ffff:0:0`.
//! - [`IPVXIPV4`] — `Conn<IpAddr, Extended<Ipv4Addr>>` extracting
//!   V4 from the sum. One-sided ([`Conn::new_l`]); only Galois L
//!   is asserted. V6 inputs saturate up to `PosInf`.
//! - [`IPVXIPV6`] — `Conn<IpAddr, Extended<Ipv6Addr>>` extracting
//!   V6. One-sided ([`Conn::new_r`]); only Galois R is asserted.
//!   V4 inputs saturate down to `NegInf`.
//!
//! IP-address types sit on the right side of these Conns — they're
//! the use-wise-more-specific endpoint. The natural composition
//! flows `<numeric chain> → u32 → Ipv4Addr` and `IpAddr →
//! Extended<Ipv4Addr>` (left-to-right, generic to specific).

use crate::conn::Conn;
use crate::extended::Extended;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

/// Smallest u128 representation of the v4-mapped Ipv6 prefix
/// `::ffff:0:0`.
const V4MAPPED_LO: u128 = 0x0000_0000_0000_0000_0000_FFFF_0000_0000;
/// Largest u128 representation of the v4-mapped Ipv6 prefix
/// `::ffff:ffff:ffff`.
const V4MAPPED_HI: u128 = 0x0000_0000_0000_0000_0000_FFFF_FFFF_FFFF;

const fn u32_to_v4(b: u32) -> Ipv4Addr {
    Ipv4Addr::from_bits(b)
}
const fn v4_to_u32(a: Ipv4Addr) -> u32 {
    a.to_bits()
}

crate::iso! {
    /// `u32 ↔ Ipv4Addr` — total bijection via the standard big-endian
    /// representation.
    ///
    /// Both directions are lossless; `floor = ceil = forward`
    /// (degenerate Galois, constructed via the [`iso!`](crate::iso) macro).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::view_l;
    /// use connections::addr::U032IPV4;
    /// use std::net::Ipv4Addr;
    ///
    /// assert_eq!(view_l(&U032IPV4).ceil(0xC0A80101_u32), Ipv4Addr::new(192, 168, 1, 1));
    /// assert_eq!(view_l(&U032IPV4).upper(Ipv4Addr::new(192, 168, 1, 1)), 0xC0A80101_u32);
    /// ```
    pub U032IPV4 : u32 => Ipv4Addr {
        forward: u32_to_v4,
        back:    v4_to_u32,
    }
}

const fn u128_to_v6(b: u128) -> Ipv6Addr {
    Ipv6Addr::from_bits(b)
}
const fn v6_to_u128(a: Ipv6Addr) -> u128 {
    a.to_bits()
}

crate::iso! {
    /// `u128 ↔ Ipv6Addr` — total bijection via the standard big-endian
    /// representation.
    ///
    /// Both directions are lossless; `floor = ceil = forward`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::view_l;
    /// use connections::addr::U128IPV6;
    /// use std::net::Ipv6Addr;
    ///
    /// assert_eq!(view_l(&U128IPV6).ceil(1_u128), Ipv6Addr::LOCALHOST);
    /// assert_eq!(view_l(&U128IPV6).upper(Ipv6Addr::LOCALHOST), 1_u128);
    /// ```
    pub U128IPV6 : u128 => Ipv6Addr {
        forward: u128_to_v6,
        back:    v6_to_u128,
    }
}

const fn ipv6ipv4_ceil(v6: Ipv6Addr) -> Extended<Ipv4Addr> {
    let bits = v6.to_bits();
    if bits == 0 {
        // `::` — Galois pins ceil to NegInf because inner(NegInf) = `::`.
        Extended::NegInf
    } else if bits < V4MAPPED_LO {
        // Below v4-mapped block — smallest rung b with v6 ≤ inner(b)
        // is `Finite(0.0.0.0)` (whose inner is `::ffff:0:0`).
        Extended::Finite(Ipv4Addr::UNSPECIFIED)
    } else if bits <= V4MAPPED_HI {
        Extended::Finite(Ipv4Addr::from_bits(bits as u32))
    } else {
        // Above v4-mapped block — no Finite v4 has inner(v4) ≥ v6.
        Extended::PosInf
    }
}

const fn ipv6ipv4_inner(b: Extended<Ipv4Addr>) -> Ipv6Addr {
    match b {
        Extended::NegInf => Ipv6Addr::UNSPECIFIED,
        Extended::Finite(v4) => v4.to_ipv6_mapped(),
        Extended::PosInf => Ipv6Addr::from_bits(u128::MAX),
    }
}

const fn ipv6ipv4_floor(v6: Ipv6Addr) -> Extended<Ipv4Addr> {
    let bits = v6.to_bits();
    if bits == u128::MAX {
        // `MAX` — Galois pins floor to PosInf (inner(PosInf) = MAX).
        Extended::PosInf
    } else if bits < V4MAPPED_LO {
        // Below v4-mapped block — no Finite v4 has inner(v4) ≤ v6
        // (inner of any Finite is in the block).
        Extended::NegInf
    } else if bits <= V4MAPPED_HI {
        Extended::Finite(Ipv4Addr::from_bits(bits as u32))
    } else {
        // Above v4-mapped block — largest Finite v4 with inner ≤ v6
        // is `Finite(255.255.255.255)` (whose inner is V4MAPPED_HI).
        Extended::Finite(Ipv4Addr::BROADCAST)
    }
}

crate::conn_k! {
    /// `Ipv6Addr → Extended<Ipv4Addr>` — the v4-mapped bridge.
    ///
    /// The forward map projects an `Ipv6Addr` onto its embedded
    /// `Ipv4Addr` whenever the address sits in the v4-mapped prefix
    /// `::ffff:0:0/96`; outside that block, projection saturates to
    /// `NegInf` / `PosInf` on the rung. Target `Extended<Ipv4Addr>`
    /// supplies the synthetic ends; source `Ipv6Addr` stays plain (the
    /// Ipv6 range is its own bounded universe).
    ///
    /// On the v4-mapped block the Conn is bijective — `ceil = floor =
    /// Finite(extracted v4)`, and `inner` round-trips via
    /// `Ipv4Addr::to_ipv6_mapped`.
    ///
    /// Outside the v4-mapped block the Conn has asymmetric arms: ceil
    /// rounds *up* into the block (or saturates above), floor rounds
    /// *down* (or saturates below). This is a lawful full triple
    /// (`floor ≤ ceil` everywhere) because `inner` is order-reflecting:
    /// `inner(NegInf) = ::` is strictly below `inner(Finite(0.0.0.0)) =
    /// ::ffff:0:0`, and `inner(PosInf) = MAX` is strictly above
    /// `inner(Finite(255.255.255.255)) = ::ffff:ffff:ffff` — the
    /// pre-block and post-block "room" plays the role that subsec
    /// precision plays in `TDURSECS`. Ceil and floor agree at the Ipv6
    /// extremes (`::`, `Ipv6Addr::MAX`) and inside the v4-mapped block;
    /// below or above the block they diverge:
    ///
    /// | v6 region                      | `ceil`                  | `floor`                  |
    /// |--------------------------------|-------------------------|--------------------------|
    /// | `::` (UNSPECIFIED)             | `NegInf`                | `NegInf`                 |
    /// | `::1` …  `::ffff:0:0 - 1`      | `Finite(0.0.0.0)`       | `NegInf`                 |
    /// | `::ffff:0:0` … `::ffff:ffff:ffff` | `Finite(extracted v4)` | `Finite(extracted v4)` |
    /// | `::1:0:0:0` … `MAX - 1`        | `PosInf`                | `Finite(255.255.255.255)`|
    /// | `MAX`                          | `PosInf`                | `PosInf`                 |
    ///
    /// `inner` is the v4-mapped embedding (synthetic ends saturate to
    /// `Ipv6Addr::UNSPECIFIED` and `Ipv6Addr::MAX` respectively).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{view_l, view_r};
    /// use connections::addr::ip::IPV6IPV4;
    /// use connections::extended::Extended;
    /// use std::net::{Ipv4Addr, Ipv6Addr};
    ///
    /// // V4-mapped Ipv6 round-trips through the bridge.
    /// let v4_in_v6: Ipv6Addr = "::ffff:7f00:1".parse().unwrap();
    /// assert_eq!(
    ///     view_l(&IPV6IPV4).ceil(v4_in_v6),
    ///     Extended::Finite(Ipv4Addr::new(127, 0, 0, 1))
    /// );
    /// assert_eq!(
    ///     view_l(&IPV6IPV4).upper(Extended::Finite(Ipv4Addr::new(127, 0, 0, 1))),
    ///     v4_in_v6
    /// );
    ///
    /// // `::1` (loopback) sits below the v4-mapped block — ceil and
    /// // floor diverge.
    /// assert_eq!(view_l(&IPV6IPV4).ceil(Ipv6Addr::LOCALHOST),  Extended::Finite(Ipv4Addr::UNSPECIFIED));
    /// assert_eq!(view_r(&IPV6IPV4).floor(Ipv6Addr::LOCALHOST), Extended::NegInf);
    /// ```
    pub IPV6IPV4 : Ipv6Addr => Extended<Ipv4Addr> {
        ceil:  ipv6ipv4_ceil,
        inner: ipv6ipv4_inner,
        floor: ipv6ipv4_floor,
    }
}

/// `IpAddr → Extended<Ipv4Addr>` — V4 extraction from the IpAddr sum.
///
/// One-sided ceil-adjoint Conn ([`Conn::new_l`]): only `ceil ⊣
/// inner` holds (`galois_l`); the right-Galois law does not. The
/// full triple isn't lawful for this projection because the source
/// IpAddr's MIN (`V4(0.0.0.0)`) coincides with `inner(NegInf rung)`,
/// making `inner` non-order-reflecting at the bottom — which would
/// force `floor_le_ceil` to fail at `V4(0.0.0.0)` (concretely:
/// `ceil = NegInf` but `floor = Finite(0.0.0.0)` violates `floor ≤
/// ceil`). `new_left` sets `floor = ceil` as a fn pointer, dodging
/// the violation by structurally collapsing the two sides.
///
/// V4 inputs project to `Finite(addr)` except at the source MIN where
/// Galois forces `ceil(V4(0.0.0.0)) = NegInf`. V6 inputs saturate up
/// to `PosInf` (above all V4 in the coproduct order).
///
/// # Examples
///
/// ```rust
/// use connections::addr::ip::IPVXIPV4;
/// use connections::extended::Extended;
/// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
///
/// assert_eq!(
///     IPVXIPV4.ceil(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1))),
///     Extended::Finite(Ipv4Addr::new(127, 0, 0, 1))
/// );
///
/// // V6 input saturates above all V4 values.
/// assert_eq!(IPVXIPV4.ceil(IpAddr::V6(Ipv6Addr::LOCALHOST)), Extended::PosInf);
///
/// // IPVXIPV4 is a one-sided ConnL — no `.floor()` method exists,
/// // and no R-view is exposed. `inner` is the surviving lower-side
/// // accessor; `inner(PosInf)` saturates to the source MAX
/// // (`V6` with all bits set) per the L-Galois right-adjoint formula.
/// assert_eq!(
///     IPVXIPV4.upper(Extended::PosInf),
///     IpAddr::V6(Ipv6Addr::from_bits(u128::MAX)),
/// );
/// ```
pub const IPVXIPV4: crate::conn::Conn<IpAddr, Extended<Ipv4Addr>> = {
    fn ceil(a: IpAddr) -> Extended<Ipv4Addr> {
        match a {
            // Galois forces ceil(MIN) = NegInf because inner(NegInf) = V4(0.0.0.0)
            // (the source MIN) and there's no IpAddr below it.
            IpAddr::V4(v4) if v4 == Ipv4Addr::UNSPECIFIED => Extended::NegInf,
            IpAddr::V4(v4) => Extended::Finite(v4),
            IpAddr::V6(_) => Extended::PosInf,
        }
    }

    fn inner(b: Extended<Ipv4Addr>) -> IpAddr {
        match b {
            Extended::NegInf => IpAddr::V4(Ipv4Addr::UNSPECIFIED),
            Extended::Finite(v4) => IpAddr::V4(v4),
            // Galois L's right adjoint formula: inner(PosInf) = sup{a : ceil(a) ≤ PosInf}.
            // PosInf is top, so all a satisfy → sup = source MAX = V6(MAX bits).
            Extended::PosInf => IpAddr::V6(Ipv6Addr::from_bits(u128::MAX)),
        }
    }

    Conn::new_l(ceil, inner)
};

/// `IpAddr → Extended<Ipv6Addr>` — V6 extraction from the IpAddr sum.
///
/// One-sided floor-adjoint Conn ([`Conn::new_r`]): only `inner ⊣
/// floor` holds (`galois_r`); the left-Galois law does not. The
/// full triple isn't lawful here because the source IpAddr's MAX
/// (`V6(MAX)`) coincides with `inner(PosInf rung)`, making `inner`
/// non-order-reflecting at the top — which would force a
/// `floor_le_ceil` violation at `V6(MAX)` (`ceil = Finite(MAX)` but
/// `floor = PosInf` violates `floor ≤ ceil`). `new_right` sets `ceil
/// = floor` as a fn pointer, dodging the violation.
///
/// V6 inputs project to `Finite(addr)` except at the source MAX
/// where Galois forces `floor(V6(MAX)) = PosInf`. V4 inputs saturate
/// down to `NegInf` (below all V6 in the coproduct order).
///
/// # Examples
///
/// ```rust
/// use connections::addr::ip::IPVXIPV6;
/// use connections::extended::Extended;
/// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
///
/// assert_eq!(
///     IPVXIPV6.floor(IpAddr::V6(Ipv6Addr::LOCALHOST)),
///     Extended::Finite(Ipv6Addr::LOCALHOST)
/// );
///
/// // V4 input saturates below all V6 values.
/// assert_eq!(IPVXIPV6.floor(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1))), Extended::NegInf);
///
/// // IPVXIPV6 is a one-sided ConnR — no `.ceil()` method exists,
/// // and no L-view is exposed. `inner` is the surviving lower-side
/// // accessor.
/// assert_eq!(IPVXIPV6.lower(Extended::NegInf), IpAddr::V4(Ipv4Addr::UNSPECIFIED));
/// ```
pub const IPVXIPV6: crate::conn::Conn<IpAddr, Extended<Ipv6Addr>, crate::conn::R> = {
    fn inner(b: Extended<Ipv6Addr>) -> IpAddr {
        match b {
            // Galois R pins inner(NegInf) below all V6: largest V4 ≤ all V6 is the
            // source MIN, V4(0.0.0.0) (since Rust's IpAddr puts V4 < V6).
            Extended::NegInf => IpAddr::V4(Ipv4Addr::UNSPECIFIED),
            Extended::Finite(v6) => IpAddr::V6(v6),
            Extended::PosInf => IpAddr::V6(Ipv6Addr::from_bits(u128::MAX)),
        }
    }

    fn floor(a: IpAddr) -> Extended<Ipv6Addr> {
        match a {
            // V4 saturates to NegInf — no V6 ≤ V4(_).
            IpAddr::V4(_) => Extended::NegInf,
            // Galois forces floor(MAX) = PosInf because inner(PosInf) = V6(MAX)
            // (the source MAX) and there's no IpAddr above it.
            IpAddr::V6(v6) if v6.to_bits() == u128::MAX => Extended::PosInf,
            IpAddr::V6(v6) => Extended::Finite(v6),
        }
    }

    Conn::new_r(inner, floor)
};

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::prop::arb::{arb_extended_ipv4, arb_extended_ipv6, arb_ip_addr, arb_ipv4, arb_ipv6};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── U032IPV4 spot checks ────────────────────────────────────

    #[test]
    fn u032ipv4_loopback() {
        assert_eq!(
            U032IPV4.view_l().ceil(0x7F000001_u32),
            Ipv4Addr::new(127, 0, 0, 1)
        );
        assert_eq!(
            U032IPV4.view_l().upper(Ipv4Addr::new(127, 0, 0, 1)),
            0x7F000001_u32
        );
    }

    #[test]
    fn u032ipv4_extremes() {
        assert_eq!(U032IPV4.view_l().ceil(0_u32), Ipv4Addr::UNSPECIFIED);
        assert_eq!(U032IPV4.view_l().ceil(u32::MAX), Ipv4Addr::BROADCAST);
        assert_eq!(U032IPV4.view_l().upper(Ipv4Addr::UNSPECIFIED), 0_u32);
        assert_eq!(U032IPV4.view_l().upper(Ipv4Addr::BROADCAST), u32::MAX);
    }

    // ── U128IPV6 spot checks ────────────────────────────────────

    #[test]
    fn u128ipv6_localhost() {
        assert_eq!(U128IPV6.view_l().ceil(1_u128), Ipv6Addr::LOCALHOST);
        assert_eq!(U128IPV6.view_l().upper(Ipv6Addr::LOCALHOST), 1_u128);
    }

    #[test]
    fn u128ipv6_extremes() {
        assert_eq!(U128IPV6.view_l().ceil(0_u128), Ipv6Addr::UNSPECIFIED);
        assert_eq!(U128IPV6.view_l().upper(Ipv6Addr::UNSPECIFIED), 0_u128);
        assert_eq!(
            U128IPV6.view_l().ceil(u128::MAX),
            Ipv6Addr::from_bits(u128::MAX)
        );
    }

    // ── Galois law batteries ────────────────────────────────────
    //
    // Both Conns are total bijections (`iso!`), so both Galois
    // laws hold trivially and `inner` round-trips both directions.

    crate::law_battery! {
        mod u032ipv4_laws,
        conn: U032IPV4,
        fine:   any::<u32>(),
        coarse: arb_ipv4(),
    }

    crate::law_battery! {
        mod u128ipv6_laws,
        conn: U128IPV6,
        fine:   any::<u128>(),
        coarse: arb_ipv6(),
    }

    proptest! {
        #[test]
        fn u032ipv4_floor_le_ceil(b in any::<u32>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U032IPV4, b));
        }

        #[test]
        fn u128ipv6_floor_le_ceil(b in any::<u128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U128IPV6, b));
        }
    }

    // ── IPV6IPV4 spot checks ────────────────────────────────────

    #[test]
    fn ipv6ipv4_v4mapped_round_trip() {
        let v4 = Ipv4Addr::new(127, 0, 0, 1);
        let v6: Ipv6Addr = "::ffff:7f00:1".parse().unwrap();
        assert_eq!(IPV6IPV4.view_l().ceil(v6), Extended::Finite(v4));
        assert_eq!(IPV6IPV4.view_r().floor(v6), Extended::Finite(v4));
        assert_eq!(IPV6IPV4.view_l().upper(Extended::Finite(v4)), v6);
    }

    #[test]
    fn ipv6ipv4_v4mapped_extremes() {
        let lo = Ipv6Addr::from_bits(V4MAPPED_LO);
        let hi = Ipv6Addr::from_bits(V4MAPPED_HI);
        assert_eq!(
            IPV6IPV4.view_l().ceil(lo),
            Extended::Finite(Ipv4Addr::UNSPECIFIED)
        );
        assert_eq!(
            IPV6IPV4.view_r().floor(lo),
            Extended::Finite(Ipv4Addr::UNSPECIFIED)
        );
        assert_eq!(
            IPV6IPV4.view_l().ceil(hi),
            Extended::Finite(Ipv4Addr::BROADCAST)
        );
        assert_eq!(
            IPV6IPV4.view_r().floor(hi),
            Extended::Finite(Ipv4Addr::BROADCAST)
        );
    }

    #[test]
    fn ipv6ipv4_below_block_asymmetric() {
        // Loopback `::1` sits below the v4-mapped block.
        // ceil rounds *up* into the block; floor saturates to NegInf.
        assert_eq!(
            IPV6IPV4.view_l().ceil(Ipv6Addr::LOCALHOST),
            Extended::Finite(Ipv4Addr::UNSPECIFIED)
        );
        assert_eq!(
            IPV6IPV4.view_r().floor(Ipv6Addr::LOCALHOST),
            Extended::NegInf
        );

        // `::ffff:0:0 - 1` is the largest v6 below the block.
        let just_below = Ipv6Addr::from_bits(V4MAPPED_LO - 1);
        assert_eq!(
            IPV6IPV4.view_l().ceil(just_below),
            Extended::Finite(Ipv4Addr::UNSPECIFIED)
        );
        assert_eq!(IPV6IPV4.view_r().floor(just_below), Extended::NegInf);
    }

    #[test]
    fn ipv6ipv4_above_block_asymmetric() {
        // `::ffff:ffff:ffff + 1` is the smallest v6 above the block.
        let just_above = Ipv6Addr::from_bits(V4MAPPED_HI + 1);
        assert_eq!(IPV6IPV4.view_l().ceil(just_above), Extended::PosInf);
        assert_eq!(
            IPV6IPV4.view_r().floor(just_above),
            Extended::Finite(Ipv4Addr::BROADCAST)
        );
    }

    #[test]
    fn ipv6ipv4_ipv6_extremes_synced() {
        // At `::` and `Ipv6Addr::MAX`, ceil and floor agree (Galois
        // pins them to NegInf/PosInf respectively).
        assert_eq!(
            IPV6IPV4.view_l().ceil(Ipv6Addr::UNSPECIFIED),
            Extended::NegInf
        );
        assert_eq!(
            IPV6IPV4.view_r().floor(Ipv6Addr::UNSPECIFIED),
            Extended::NegInf
        );

        let max = Ipv6Addr::from_bits(u128::MAX);
        assert_eq!(IPV6IPV4.view_l().ceil(max), Extended::PosInf);
        assert_eq!(IPV6IPV4.view_r().floor(max), Extended::PosInf);
    }

    #[test]
    fn ipv6ipv4_synthetic_inner() {
        assert_eq!(
            IPV6IPV4.view_l().upper(Extended::NegInf),
            Ipv6Addr::UNSPECIFIED
        );
        assert_eq!(
            IPV6IPV4.view_l().upper(Extended::PosInf),
            Ipv6Addr::from_bits(u128::MAX)
        );
    }

    // ── IPV6IPV4 Galois law battery ─────────────────────────────

    crate::law_battery! {
        mod ipv6ipv4_laws,
        conn: IPV6IPV4,
        fine:   arb_ipv6(),
        coarse: arb_extended_ipv4(),
    }

    proptest! {
        // V4-mapped block round-trips bijectively.
        #[test]
        fn ipv6ipv4_v4_round_trip(v4 in arb_ipv4()) {
            let v6 = IPV6IPV4.view_l().upper(Extended::Finite(v4));
            prop_assert_eq!(IPV6IPV4.view_l().ceil(v6), Extended::Finite(v4));
            prop_assert_eq!(IPV6IPV4.view_r().floor(v6), Extended::Finite(v4));
        }

        #[test]
        fn ipv6ipv4_floor_le_ceil(a in arb_ipv6()) {
            prop_assert!(conn_laws::floor_le_ceil(&IPV6IPV4, a));
        }

        // ── IPVXIPV4 (one-sided ceil-adjoint, bare ConnL) ───────
        //
        // new_left contract: Galois L holds, Galois R does not.
        // IPVXIPV4 is a bare `pub const ConnL` (not a triple marker),
        // so it's tested directly here rather than via law_battery!.

        #[test]
        fn ipvxipv4_galois_l(a in arb_ip_addr(), b in arb_extended_ipv4()) {
            prop_assert!(conn_laws::galois_l(&IPVXIPV4, a, b));
        }

        #[test]
        fn ipvxipv4_closure_l(a in arb_ip_addr()) {
            prop_assert!(conn_laws::closure_l(&IPVXIPV4, a));
        }

        #[test]
        fn ipvxipv4_kernel_l(b in arb_extended_ipv4()) {
            prop_assert!(conn_laws::kernel_l(&IPVXIPV4, b));
        }

        #[test]
        fn ipvxipv4_idempotent(a in arb_ip_addr()) {
            prop_assert!(conn_laws::idempotent(&IPVXIPV4, a));
        }

        // ── IPVXIPV6 (one-sided floor-adjoint, bare ConnR) ──────

        #[test]
        fn ipvxipv6_galois_r(a in arb_ip_addr(), b in arb_extended_ipv6()) {
            prop_assert!(conn_laws::galois_r(&IPVXIPV6, a, b));
        }

        #[test]
        fn ipvxipv6_closure_r(a in arb_ip_addr()) {
            prop_assert!(conn_laws::closure_r(&IPVXIPV6, a));
        }

        #[test]
        fn ipvxipv6_kernel_r(b in arb_extended_ipv6()) {
            prop_assert!(conn_laws::kernel_r(&IPVXIPV6, b));
        }
    }
}
