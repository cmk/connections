//! IPv4 / IPv6 / IpAddr connections.
//!
//! Five Conns covering the std-library IP types:
//!
//! - [`U032IPV4`] — `Conn<u32, Ipv4Addr>` total bijection via
//!   `Ipv4Addr::{from,to}_bits`. Constructed with [`Conn::new_iso`];
//!   both Galois laws and `floor_le_ceil` hold trivially.
//! - [`U128IPV6`] — `Conn<u128, Ipv6Addr>` total bijection, same
//!   shape.
//! - [`IPV6IPV4`] — `Conn<Ipv6Addr, Extended<Ipv4Addr>>`, the
//!   v4-mapped bridge. Full triple ([`Conn::new`]) with asymmetric
//!   ceil/floor outside the v4-mapped block; lawful (passes
//!   `floor_le_ceil`) because `inner` is order-reflecting — the
//!   v4-mapped block sits strictly inside `Ipv6Addr`, giving "room"
//!   between `inner(NegInf) = ::` and `inner(Finite(0.0.0.0)) =
//!   ::ffff:0:0`.
//! - [`IPVXIPV4`] — `Conn<IpAddr, Extended<Ipv4Addr>>` extracting
//!   V4 from the sum. One-sided ([`Conn::new_left`]); only Galois L
//!   is asserted. V6 inputs saturate up to `PosInf`.
//! - [`IPVXIPV6`] — `Conn<IpAddr, Extended<Ipv6Addr>>` extracting
//!   V6. One-sided ([`Conn::new_right`]); only Galois R is asserted.
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

/// `u32 ↔ Ipv4Addr` — total bijection via the standard big-endian
/// representation.
///
/// Both directions are lossless; `floor = ceil = forward`
/// (degenerate Galois, constructed via [`Conn::new_iso`]).
///
/// # Examples
///
/// ```rust
/// use connections::addr::U032IPV4;
/// use std::net::Ipv4Addr;
///
/// assert_eq!(U032IPV4.ceil(0xC0A80101_u32), Ipv4Addr::new(192, 168, 1, 1));
/// assert_eq!(U032IPV4.inner(Ipv4Addr::new(192, 168, 1, 1)), 0xC0A80101_u32);
/// ```
pub const U032IPV4: Conn<u32, Ipv4Addr> = {
    fn forward(b: u32) -> Ipv4Addr {
        Ipv4Addr::from_bits(b)
    }
    fn back(a: Ipv4Addr) -> u32 {
        a.to_bits()
    }
    Conn::new_iso(forward, back)
};

/// `u128 ↔ Ipv6Addr` — total bijection via the standard big-endian
/// representation.
///
/// Both directions are lossless; `floor = ceil = forward`.
///
/// # Examples
///
/// ```rust
/// use connections::addr::U128IPV6;
/// use std::net::Ipv6Addr;
///
/// assert_eq!(U128IPV6.ceil(1_u128), Ipv6Addr::LOCALHOST);
/// assert_eq!(U128IPV6.inner(Ipv6Addr::LOCALHOST), 1_u128);
/// ```
pub const U128IPV6: Conn<u128, Ipv6Addr> = {
    fn forward(b: u128) -> Ipv6Addr {
        Ipv6Addr::from_bits(b)
    }
    fn back(a: Ipv6Addr) -> u128 {
        a.to_bits()
    }
    Conn::new_iso(forward, back)
};

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
/// precision plays in `DURNSECS`. Ceil and floor agree at the Ipv6
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
/// use connections::addr::ip::IPV6IPV4;
/// use connections::extended::Extended;
/// use std::net::{Ipv4Addr, Ipv6Addr};
///
/// // V4-mapped Ipv6 round-trips through the bridge.
/// let v4_in_v6: Ipv6Addr = "::ffff:7f00:1".parse().unwrap();
/// assert_eq!(
///     IPV6IPV4.ceil(v4_in_v6),
///     Extended::Finite(Ipv4Addr::new(127, 0, 0, 1))
/// );
/// assert_eq!(
///     IPV6IPV4.inner(Extended::Finite(Ipv4Addr::new(127, 0, 0, 1))),
///     v4_in_v6
/// );
///
/// // `::1` (loopback) sits below the v4-mapped block — ceil and
/// // floor diverge.
/// assert_eq!(IPV6IPV4.ceil(Ipv6Addr::LOCALHOST),  Extended::Finite(Ipv4Addr::UNSPECIFIED));
/// assert_eq!(IPV6IPV4.floor(Ipv6Addr::LOCALHOST), Extended::NegInf);
/// ```
pub const IPV6IPV4: Conn<Ipv6Addr, Extended<Ipv4Addr>> = {
    fn ceil(v6: Ipv6Addr) -> Extended<Ipv4Addr> {
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

    fn inner(b: Extended<Ipv4Addr>) -> Ipv6Addr {
        match b {
            Extended::NegInf => Ipv6Addr::UNSPECIFIED,
            Extended::Finite(v4) => v4.to_ipv6_mapped(),
            Extended::PosInf => Ipv6Addr::from_bits(u128::MAX),
        }
    }

    fn floor(v6: Ipv6Addr) -> Extended<Ipv4Addr> {
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

    Conn::new(ceil, inner, floor)
};

/// `IpAddr → Extended<Ipv4Addr>` — V4 extraction from the IpAddr sum.
///
/// One-sided ceil-adjoint Conn ([`Conn::new_left`]): only `ceil ⊣
/// inner` holds (`conn_galois_l`); the right-Galois law does not. The
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
/// // `floor` returns the same as `ceil` (one-sided contract).
/// assert_eq!(IPVXIPV4.floor(IpAddr::V6(Ipv6Addr::LOCALHOST)), Extended::PosInf);
/// ```
pub const IPVXIPV4: Conn<IpAddr, Extended<Ipv4Addr>> = {
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

    Conn::new_left(ceil, inner)
};

/// `IpAddr → Extended<Ipv6Addr>` — V6 extraction from the IpAddr sum.
///
/// One-sided floor-adjoint Conn ([`Conn::new_right`]): only `inner ⊣
/// floor` holds (`conn_galois_r`); the left-Galois law does not. The
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
/// // `ceil` returns the same as `floor` (one-sided contract).
/// assert_eq!(IPVXIPV6.ceil(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1))),  Extended::NegInf);
/// ```
pub const IPVXIPV6: Conn<IpAddr, Extended<Ipv6Addr>> = {
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

    Conn::new_right(inner, floor)
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prop::arb::{arb_extended_ipv4, arb_extended_ipv6, arb_ip_addr, arb_ipv4, arb_ipv6};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── U032IPV4 spot checks ────────────────────────────────────

    #[test]
    fn u032ipv4_loopback() {
        assert_eq!(U032IPV4.ceil(0x7F000001_u32), Ipv4Addr::new(127, 0, 0, 1));
        assert_eq!(U032IPV4.inner(Ipv4Addr::new(127, 0, 0, 1)), 0x7F000001_u32);
    }

    #[test]
    fn u032ipv4_extremes() {
        assert_eq!(U032IPV4.ceil(0_u32), Ipv4Addr::UNSPECIFIED);
        assert_eq!(U032IPV4.ceil(u32::MAX), Ipv4Addr::BROADCAST);
        assert_eq!(U032IPV4.inner(Ipv4Addr::UNSPECIFIED), 0_u32);
        assert_eq!(U032IPV4.inner(Ipv4Addr::BROADCAST), u32::MAX);
    }

    // ── U128IPV6 spot checks ────────────────────────────────────

    #[test]
    fn u128ipv6_localhost() {
        assert_eq!(U128IPV6.ceil(1_u128), Ipv6Addr::LOCALHOST);
        assert_eq!(U128IPV6.inner(Ipv6Addr::LOCALHOST), 1_u128);
    }

    #[test]
    fn u128ipv6_extremes() {
        assert_eq!(U128IPV6.ceil(0_u128), Ipv6Addr::UNSPECIFIED);
        assert_eq!(U128IPV6.inner(Ipv6Addr::UNSPECIFIED), 0_u128);
        assert_eq!(U128IPV6.ceil(u128::MAX), Ipv6Addr::from_bits(u128::MAX));
    }

    // ── Galois law batteries ────────────────────────────────────
    //
    // Both Conns are total bijections (`new_iso`), so both Galois
    // laws hold trivially and `inner` round-trips both directions.

    proptest! {
        #[test]
        fn u032ipv4_galois_l(b in any::<u32>(), a in arb_ipv4()) {
            prop_assert!(conn_laws::conn_galois_l(&U032IPV4, b, a));
        }

        #[test]
        fn u032ipv4_galois_r(b in any::<u32>(), a in arb_ipv4()) {
            prop_assert!(conn_laws::conn_galois_r(&U032IPV4, b, a));
        }

        #[test]
        fn u032ipv4_round_trip_b(b in any::<u32>()) {
            prop_assert_eq!(U032IPV4.inner(U032IPV4.ceil(b)), b);
        }

        #[test]
        fn u032ipv4_round_trip_a(a in arb_ipv4()) {
            prop_assert_eq!(U032IPV4.ceil(U032IPV4.inner(a)), a);
        }

        #[test]
        fn u032ipv4_floor_le_ceil(b in any::<u32>()) {
            prop_assert!(conn_laws::conn_floor_le_ceil(&U032IPV4, b));
        }

        #[test]
        fn u128ipv6_galois_l(b in any::<u128>(), a in arb_ipv6()) {
            prop_assert!(conn_laws::conn_galois_l(&U128IPV6, b, a));
        }

        #[test]
        fn u128ipv6_galois_r(b in any::<u128>(), a in arb_ipv6()) {
            prop_assert!(conn_laws::conn_galois_r(&U128IPV6, b, a));
        }

        #[test]
        fn u128ipv6_round_trip_b(b in any::<u128>()) {
            prop_assert_eq!(U128IPV6.inner(U128IPV6.ceil(b)), b);
        }

        #[test]
        fn u128ipv6_round_trip_a(a in arb_ipv6()) {
            prop_assert_eq!(U128IPV6.ceil(U128IPV6.inner(a)), a);
        }

        #[test]
        fn u128ipv6_floor_le_ceil(b in any::<u128>()) {
            prop_assert!(conn_laws::conn_floor_le_ceil(&U128IPV6, b));
        }
    }

    // ── IPV6IPV4 spot checks ────────────────────────────────────

    #[test]
    fn ipv6ipv4_v4mapped_round_trip() {
        let v4 = Ipv4Addr::new(127, 0, 0, 1);
        let v6: Ipv6Addr = "::ffff:7f00:1".parse().unwrap();
        assert_eq!(IPV6IPV4.ceil(v6), Extended::Finite(v4));
        assert_eq!(IPV6IPV4.floor(v6), Extended::Finite(v4));
        assert_eq!(IPV6IPV4.inner(Extended::Finite(v4)), v6);
    }

    #[test]
    fn ipv6ipv4_v4mapped_extremes() {
        let lo = Ipv6Addr::from_bits(V4MAPPED_LO);
        let hi = Ipv6Addr::from_bits(V4MAPPED_HI);
        assert_eq!(IPV6IPV4.ceil(lo), Extended::Finite(Ipv4Addr::UNSPECIFIED));
        assert_eq!(IPV6IPV4.floor(lo), Extended::Finite(Ipv4Addr::UNSPECIFIED));
        assert_eq!(IPV6IPV4.ceil(hi), Extended::Finite(Ipv4Addr::BROADCAST));
        assert_eq!(IPV6IPV4.floor(hi), Extended::Finite(Ipv4Addr::BROADCAST));
    }

    #[test]
    fn ipv6ipv4_below_block_asymmetric() {
        // Loopback `::1` sits below the v4-mapped block.
        // ceil rounds *up* into the block; floor saturates to NegInf.
        assert_eq!(
            IPV6IPV4.ceil(Ipv6Addr::LOCALHOST),
            Extended::Finite(Ipv4Addr::UNSPECIFIED)
        );
        assert_eq!(IPV6IPV4.floor(Ipv6Addr::LOCALHOST), Extended::NegInf);

        // `::ffff:0:0 - 1` is the largest v6 below the block.
        let just_below = Ipv6Addr::from_bits(V4MAPPED_LO - 1);
        assert_eq!(
            IPV6IPV4.ceil(just_below),
            Extended::Finite(Ipv4Addr::UNSPECIFIED)
        );
        assert_eq!(IPV6IPV4.floor(just_below), Extended::NegInf);
    }

    #[test]
    fn ipv6ipv4_above_block_asymmetric() {
        // `::ffff:ffff:ffff + 1` is the smallest v6 above the block.
        let just_above = Ipv6Addr::from_bits(V4MAPPED_HI + 1);
        assert_eq!(IPV6IPV4.ceil(just_above), Extended::PosInf);
        assert_eq!(
            IPV6IPV4.floor(just_above),
            Extended::Finite(Ipv4Addr::BROADCAST)
        );
    }

    #[test]
    fn ipv6ipv4_ipv6_extremes_synced() {
        // At `::` and `Ipv6Addr::MAX`, ceil and floor agree (Galois
        // pins them to NegInf/PosInf respectively).
        assert_eq!(IPV6IPV4.ceil(Ipv6Addr::UNSPECIFIED), Extended::NegInf);
        assert_eq!(IPV6IPV4.floor(Ipv6Addr::UNSPECIFIED), Extended::NegInf);

        let max = Ipv6Addr::from_bits(u128::MAX);
        assert_eq!(IPV6IPV4.ceil(max), Extended::PosInf);
        assert_eq!(IPV6IPV4.floor(max), Extended::PosInf);
    }

    #[test]
    fn ipv6ipv4_synthetic_inner() {
        assert_eq!(IPV6IPV4.inner(Extended::NegInf), Ipv6Addr::UNSPECIFIED);
        assert_eq!(
            IPV6IPV4.inner(Extended::PosInf),
            Ipv6Addr::from_bits(u128::MAX)
        );
    }

    // ── IPV6IPV4 Galois law battery ─────────────────────────────

    proptest! {
        #[test]
        fn ipv6ipv4_galois_l(a in arb_ipv6(), b in arb_extended_ipv4()) {
            prop_assert!(conn_laws::conn_galois_l(&IPV6IPV4, a, b));
        }

        #[test]
        fn ipv6ipv4_galois_r(a in arb_ipv6(), b in arb_extended_ipv4()) {
            prop_assert!(conn_laws::conn_galois_r(&IPV6IPV4, a, b));
        }

        #[test]
        fn ipv6ipv4_closure_l(a in arb_ipv6()) {
            prop_assert!(conn_laws::conn_closure_l(&IPV6IPV4, a));
        }

        #[test]
        fn ipv6ipv4_closure_r(a in arb_ipv6()) {
            prop_assert!(conn_laws::conn_closure_r(&IPV6IPV4, a));
        }

        #[test]
        fn ipv6ipv4_kernel_l(b in arb_extended_ipv4()) {
            prop_assert!(conn_laws::conn_kernel_l(&IPV6IPV4, b));
        }

        #[test]
        fn ipv6ipv4_kernel_r(b in arb_extended_ipv4()) {
            prop_assert!(conn_laws::conn_kernel_r(&IPV6IPV4, b));
        }

        #[test]
        fn ipv6ipv4_monotone_l(a in arb_ipv6(), b in arb_ipv6()) {
            prop_assert!(conn_laws::conn_monotone_l(&IPV6IPV4, a, b));
        }

        #[test]
        fn ipv6ipv4_monotone_r(a in arb_extended_ipv4(), b in arb_extended_ipv4()) {
            prop_assert!(conn_laws::conn_monotone_r(&IPV6IPV4, a, b));
        }

        #[test]
        fn ipv6ipv4_idempotent(a in arb_ipv6()) {
            prop_assert!(conn_laws::conn_idempotent(&IPV6IPV4, a));
        }

        // V4-mapped block round-trips bijectively.
        #[test]
        fn ipv6ipv4_v4_round_trip(v4 in arb_ipv4()) {
            let v6 = IPV6IPV4.inner(Extended::Finite(v4));
            prop_assert_eq!(IPV6IPV4.ceil(v6), Extended::Finite(v4));
            prop_assert_eq!(IPV6IPV4.floor(v6), Extended::Finite(v4));
        }

        #[test]
        fn ipv6ipv4_floor_le_ceil(a in arb_ipv6()) {
            prop_assert!(conn_laws::conn_floor_le_ceil(&IPV6IPV4, a));
        }

        // ── IPVXIPV4 (one-sided ceil-adjoint) law battery ───────
        //
        // new_left contract: Galois L holds, Galois R does not.
        // floor_le_ceil holds trivially (floor = ceil structurally).

        #[test]
        fn ipvxipv4_galois_l(a in arb_ip_addr(), b in arb_extended_ipv4()) {
            prop_assert!(conn_laws::conn_galois_l(&IPVXIPV4, a, b));
        }

        #[test]
        fn ipvxipv4_closure_l(a in arb_ip_addr()) {
            prop_assert!(conn_laws::conn_closure_l(&IPVXIPV4, a));
        }

        #[test]
        fn ipvxipv4_kernel_l(b in arb_extended_ipv4()) {
            prop_assert!(conn_laws::conn_kernel_l(&IPVXIPV4, b));
        }

        #[test]
        fn ipvxipv4_floor_le_ceil(a in arb_ip_addr()) {
            prop_assert!(conn_laws::conn_floor_le_ceil(&IPVXIPV4, a));
        }

        #[test]
        fn ipvxipv4_idempotent(a in arb_ip_addr()) {
            prop_assert!(conn_laws::conn_idempotent(&IPVXIPV4, a));
        }

        // ── IPVXIPV6 (one-sided floor-adjoint) law battery ──────
        //
        // new_right contract: Galois R holds, Galois L does not.
        // floor_le_ceil holds trivially (ceil = floor structurally).

        #[test]
        fn ipvxipv6_galois_r(a in arb_ip_addr(), b in arb_extended_ipv6()) {
            prop_assert!(conn_laws::conn_galois_r(&IPVXIPV6, a, b));
        }

        #[test]
        fn ipvxipv6_closure_r(a in arb_ip_addr()) {
            prop_assert!(conn_laws::conn_closure_r(&IPVXIPV6, a));
        }

        #[test]
        fn ipvxipv6_kernel_r(b in arb_extended_ipv6()) {
            prop_assert!(conn_laws::conn_kernel_r(&IPVXIPV6, b));
        }

        #[test]
        fn ipvxipv6_floor_le_ceil(a in arb_ip_addr()) {
            prop_assert!(conn_laws::conn_floor_le_ceil(&IPVXIPV6, a));
        }

        #[test]
        fn ipvxipv6_idempotent(a in arb_ip_addr()) {
            prop_assert!(conn_laws::conn_idempotent(&IPVXIPV6, a));
        }
    }
}
