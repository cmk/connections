# Review 00042 — Plan 24: `addr/` submodule + `LATTBOOL` helper

## Summary

- Adds a new top-level `addr/` submodule with seven Galois connections
  for `std::net` address types: `U032IPV4` and `U128IPV6` (total
  bijections), `IPV6IPV4` (v4-mapped bridge, full triple), and the
  four sum projections `IPVXIPV4` / `IPVXIPV6` / `SOVXSOV4` /
  `SOVXSOV6` (one-sided `new_left` / `new_right` Conns extracting
  variant-specific values from `IpAddr` and `SocketAddr`).
- Adds a generic `LATTBOOL<A>() -> Conn<A, bool>` helper to
  `lattice.rs` — the canonical `bndbin`-shape Conn for any bounded
  lattice — plus `Join` + `Meet` impls on `core::cmp::Ordering` as
  the smallest non-trivial in-crate test surface.
- Cuts the original Plan 24 scope significantly: the `char`,
  `Ordering`, and `bool` Conns from the spec are deferred, and the
  one-sided structure of the four sum-projection Conns replaces the
  originally-specced full triples (which weren't Galois-lawful
  because `inner` is non-order-reflecting at the source extremes).
  The plan's Review section captures the math, the deviations, and
  the lessons.

## Test plan

- [x] `cargo build` clean.
- [x] `cargo test --workspace` clean (1291 lib tests, +61 over Plan 23 baseline).
- [x] `cargo test --doc` clean — every shipped Conn has a runnable doctest.
- [x] `cargo clippy --all-targets -- -D warnings` clean.
- [x] `cargo fmt --all -- --check` clean.
- [x] `scripts/check-pii.sh` and `scripts/check_readme_mirror.sh` exit 0.
- [x] Every full-triple Conn (`U032IPV4`, `U128IPV6`, `IPV6IPV4`)
      has `conn_floor_le_ceil` in its battery (over its source domain).
- [x] Every one-sided Conn (`IPVXIPV4`, `IPVXIPV6`, `SOVXSOV4`,
      `SOVXSOV6`) asserts the appropriate Galois law (`L` for
      `new_left`, `R` for `new_right`) plus `floor_le_ceil` (which
      holds trivially because `floor = ceil` as a fn pointer).
- [x] `LATTBOOL::<Ordering>()` exercises both Galois laws +
      `floor_le_ceil` + `idempotent` over the 3-element chain.

## Local review (2026-04-28)

### Commit Hygiene

Four commits; all conventional prefixes (`plan:`, `doc:`, `feat:`, `doc:`). The ordering is
correct: `cb76455 plan:` → `70c57cb doc: reframe` → `06e9bcd feat:` → `e15f86d doc: review
skeleton`. The reframe lands before the feature, so the new Conns were authored against the
mandatory framing, not the old "optional for saturating connections" framing. Each commit is
self-contained and leaves the build in a passing state (no partial module introductions).

### Code Quality

`#![forbid(unsafe_code)]` present in `src/lib.rs`. No `unsafe` blocks introduced.

**One-sided Conns — correct side asserted.** `IPVXIPV4` and `SOVXSOV4` are `new_left`, and
their tests assert `galois_l` / `closure_l` / `kernel_l` (not `_r`). `IPVXIPV6` and
`SOVXSOV6` are `new_right`, and their tests assert `galois_r` / `closure_r` / `kernel_r`
(not `_l`). Correct per the `new_left` / `new_right` constructors' documented contracts.
All four one-sided Conns also assert `floor_le_ceil` and `idempotent`. Plan Verification
table is satisfied.

**Full-triple Conns — both Galois laws and `floor_le_ceil` asserted.** `U032IPV4`,
`U128IPV6`: both `galois_l` + `galois_r` + `floor_le_ceil`. `IPV6IPV4`: both Galois laws,
`closure_l/r`, `kernel_l/r`, `monotone_l/r`, `idempotent`, `floor_le_ceil`, and the
bijective round-trip. All present.

**`LATTBOOL` bounds.** Signature is `A: Join + Meet + Copy + 'static`. `Join: PartialOrd`
and `Meet: PartialOrd`; `PartialOrd: PartialEq` in std, so the `PartialEq` required by the
inner `ceil` and `floor` helpers is covered by the outer bound. The `#[allow(non_snake_case)]`
attribute is present and justified in the plan and the rustdoc.

**Stale cross-reference in `src/fixed/i16.rs`.** Commit `70c57cb` renamed the `design.md`
section from `"Triple-only properties and the role of injectivity"` to `"The
rounding-sandwich property and full-triple lawfulness"` and explicitly updated the test
comment at line 320. However, the module-level rustdoc at line 17 still says:

```
§ "Triple-only properties and the role of injectivity" for the reasoning behind the design.
```

The link is now a dead cross-reference. The commit message says it updated `src/fixed/i16.rs:320`,
but line 17 was not touched. Consequence: a reader following that link to `doc/design.md`
will find no matching section header.

**`src/addr.rs` module doc omits `socket` submodule.** The bullet list at lines 6–8 mentions
only `[ip]` and two of the seven Conns (`U032IPV4`, `U128IPV6`). `[socket]` and its two
Conns (`SOVXSOV4`, `SOVXSOV6`) are absent. The naming-convention section at line 17 also
only enumerates `IPV4`/`IPV6` prefixes; `SOV4`, `SOV6`, `SOVX` are unmentioned. The
re-export lines at the bottom (correct) contrast with the incomplete prose above.

**`src/addr/ip.rs` module doc describes only two of five Conns.** The module-level comment
says "Both Conns are total bijections … `floor = ceil = forward`." `IPV6IPV4`, `IPVXIPV4`,
and `IPVXIPV6` — the other three Conns in the file — are not mentioned. A reader of the
module comment would not know this file also contains the v4-mapped bridge and the two
IpAddr sum projections.

**`V4MAPPED_HI` notation.** The constant comment says `::ffff:ffff:ffff`; Rust's
`Ipv6Addr::Display` would render this as `::ffff:255.255.255.255` (v4-mapped dotted decimal).
Both notations identify the same address and the constant value is correct. No bug, but the
comment uses hex IPv6 notation where Rust would show dotted-decimal — a minor potential
confusion for anyone comparing against `Ipv6Addr`'s `Debug`/`Display` output.

No dead code, no unused imports, no `#[ignore]` in the new test modules.

### Test Coverage

**All required properties present.** Per the Verification table:
- `U032IPV4`: `galois_l`, `galois_r`, `round_trip_b`, `round_trip_a`, `floor_le_ceil`.
- `U128IPV6`: same shape.
- `IPV6IPV4`: `galois_l`, `galois_r`, `closure_l/r`, `kernel_l/r`, `monotone_l/r`,
  `idempotent`, `floor_le_ceil`, bijective round-trip.
- `IPVXIPV4`: `galois_l`, `closure_l`, `kernel_l`, `floor_le_ceil`, `idempotent`.
- `IPVXIPV6`: `galois_r`, `closure_r`, `kernel_r`, `floor_le_ceil`, `idempotent`.
- `SOVXSOV4`/`SOVXSOV6`: same one-sided shape as the IP projections.
- `LATTBOOL::<Ordering>()`: `galois_l`, `galois_r`, `floor_le_ceil`, `idempotent`, plus
  the spot checks from `lattbool_ordering_spot`.

**`arb_ipv6` missing `V4MAPPED_LO - 1`.** The strategy covers `UNSPECIFIED`, `LOCALHOST`,
`V4MAPPED_LO`, `V4MAPPED_HI`, `V4MAPPED_HI + 1`, `MAX`, and uniform. The critical
boundary `V4MAPPED_LO - 1` (the address just below the block, where `ceil` and `floor`
first diverge) is exercised in the deterministic spot check
`ipv6ipv4_below_block_asymmetric` but is absent from `arb_ipv6`. The proptest battery for
`IPV6IPV4` will therefore hit this boundary only when the uniform slot randomly generates
it. Adding `Just(Ipv6Addr::from_bits(v4mapped_lo - 1))` to `arb_ipv6` with weight 1 would
make this coverage reliable. Low severity because the spot check exists, but worth fixing
before pushing.

**`arb_char` and `arb_extended_char` are orphaned.** Both are public strategies with no
in-crate consumer (the CHAR family was dropped). The plan documents `arb_extended_u32` as
intentionally kept for symmetry; it does not mention `arb_char` / `arb_extended_char`.
Since they're `pub`, clippy won't warn. They can stay as future-proofing for Plan 28's
CHAR work, but the plan should acknowledge them the way it acknowledges
`arb_extended_u32`.

**`arb_socket_addr_v6` covers non-zero `flowinfo` and `scope_id`.** The strategy has
`u32::MAX` and uniform weights for both fields. `sov6_max()` uses `u32::MAX` for both,
which is the critical `SOVXSOV6` floor-pin point. This is covered.

### Plan Conformance

- **T0** (`LATTBOOL` + `Ordering` impls): present in `src/lattice.rs`. Both impls are
  correct (`join = max`, `meet = min`, `bot = Less`, `top = Greater`).
- **T1** (three full-triple addr/ip.rs Conns): all three present (`U032IPV4`, `U128IPV6`,
  `IPV6IPV4`).
- **T2** (two one-sided IpAddr projections): `IPVXIPV4` (`new_left`) and `IPVXIPV6`
  (`new_right`) present.
- **T3** (two one-sided SocketAddr projections): `SOVXSOV4` and `SOVXSOV6` present.
- **T4** (`prop/arb.rs` strategies): all listed strategies present. See coverage note above
  re: `V4MAPPED_LO - 1`.
- **T5** (`pub mod addr`): one new top-level module, no `boolean`/`char`/`net`/`ordering`.
- **T6/T7** (CLAUDE.md + README): correctly deferred; neither touched.

Six design deviations documented in the plan's Review section. Implementation matches all
six claims:
1. `addr/` only (not four submodules) — confirmed.
2. Numeric LHS, domain RHS — all Conn names and types verify.
3. Sum projections one-sided — all four use `new_left`/`new_right`.
4. `LATTBOOL` mid-sprint addition — in `lattice.rs`.
5. CHAR family absent — not in diff.
6. `floor_le_ceil` reframe — commit `70c57cb` lands before `06e9bcd`.

### Risks

**`src/fixed/i16.rs` module-level comment frames the law as structurally absent, not as
debt.** Lines 14–25 say the five Galois axioms hold, then "the triple-only rounding sandwich
`floor(a) ≤ ceil(a)` does not hold … and is not asserted by the test suite." The test-level
comment at line 320 was updated by `70c57cb` to say "tracked as known debt — Plan 27 audits
…" but the module-level comment still reads as if the omission is correct-by-design. A
reader landing at the module header gets contradictory framing compared to `doc/design.md`'s
new mandatory stance.

**The `Ordering` `Join` + `Meet` impls are a new public-API addition** (since `lattice` is
`pub`). Both impls are correct: `join = max`, `meet = min` over the 3-element chain
`Less < Equal < Greater` satisfies all lattice laws. The `lattice_bot` / `lattice_top`
proptests confirm this.

No new dependencies added; `Cargo.toml` is unchanged.

---

### Must fix before push

1. **`src/fixed/i16.rs` line 17** — stale cross-reference. The section `"Triple-only
   properties and the role of injectivity"` was renamed by commit `70c57cb` to `"The
   rounding-sandwich property and full-triple lawfulness"`. Update the reference so the
   link resolves. One-line fix.

2. **`src/addr.rs` module doc** — `socket` submodule and its Conns are absent from the
   bullet list and the naming-convention section. Add a second bullet for `[socket]` listing
   `SOVXSOV4` and `SOVXSOV6`, and extend the naming-convention prose to cover `SOV4`,
   `SOV6`, `SOVX`. Without this, `rustdoc` for `connections::addr` shows only half the
   module's contents in the narrative.

3. **`src/addr/ip.rs` module doc** — the opening claim "Both Conns are total bijections"
   is false for a five-Conn module. Either replace the paragraph with a per-Conn bullet list
   (matching `addr.rs` style) or narrow the claim to "The two integer-bijection Conns …"
   and add a second paragraph for the remaining three.

4. **`src/prop/arb.rs` — add `V4MAPPED_LO - 1` to `arb_ipv6`**. The proptest battery for
   `IPV6IPV4` is the primary guard against regressions in the boundary logic. The
   just-below-block address is the first point where `ceil` and `floor` diverge and is
   currently only in a deterministic spot check, not the proptest strategy. Add
   `Just(std::net::Ipv6Addr::from_bits(v4mapped_lo - 1))` with weight 1 alongside the
   existing `v4mapped_lo - 1` boundary in the spot check.

### Follow-up (future work)

- **`src/fixed/i16.rs` module-level prose (lines 14–25)** should be updated in Plan 27
  alongside the full audit — the `floor_le_ceil`-violating Conns in this file will be
  converted to one-sided, at which point the "does not hold … and is not asserted" language
  becomes false. Not a push blocker but tracks with Plan 27.
- **`arb_char` / `arb_extended_char` orphan status** should be noted in the plan's Deferred
  section the same way `arb_extended_u32` is, so a future reader knows they're intentionally
  kept. One sentence in Deferred suffices.

### Resolutions (pre-push)

All four must-fix items resolved in commit `f73fca2` (`fix: Address Tier-1 review on MR !42`):

1. **Stale cross-reference in `src/fixed/i16.rs:17`** — link updated to point at the renamed `doc/design.md § "The rounding-sandwich property and full-triple lawfulness"`. While there, also reframed lines 14–25 of the module-level comment so the floor_le_ceil violation at the saturation boundary reads as "known debt tracked by Plan 27" rather than "does not hold and is not asserted by design" — addresses follow-up 1 in the same commit.
2. **`src/addr.rs` module doc** — extended bullet list to cover `socket` and all seven Conns; naming-convention section expanded into a per-prefix table covering `IPV4` / `IPV6` / `IPVX` / `SOV4` / `SOV6` / `SOVX`; added a "One-sided vs full-triple shapes" note explaining when each applies.
3. **`src/addr/ip.rs` module doc** — replaced the "Both Conns are total bijections" claim with a per-Conn bullet list covering all five (`U032IPV4`, `U128IPV6`, `IPV6IPV4`, `IPVXIPV4`, `IPVXIPV6`). Each bullet calls out the constructor used and the lawfulness reasoning.
4. **`arb_ipv6` boundary coverage** — added `Just(Ipv6Addr::from_bits(v4mapped_lo - 1))` with weight 1. The just-below-block address (where `IPV6IPV4`'s ceil and floor first diverge) is now in the proptest strategy alongside the existing spot check.

Follow-up 2 (`arb_char` / `arb_extended_char` orphan status) is also folded into the same commit — added to the plan's Deferred section alongside the existing `arb_extended_u32` note.

Test surface still clean: 1291 lib tests + 51 doctests pass, fmt clean.
