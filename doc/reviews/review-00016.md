# PR #16 — usize Conn family (SIZEU032, SIZEU064)

## Summary

Adds a `usize` cast family in a new `core::size` submodule — the first
pointer-width endpoint in the crate.

- **`SIZEU032 : Conn<usize, u32>`** — saturating narrow. `ceil` clamps
  `usize` values above `u32::MAX` down to `u32::MAX`; `inner` widens with
  the FINE_MAX fixup (`inner(u32::MAX) = usize::MAX`) so left-Galois holds
  at the 64-bit saturation plateau, exactly as `uint_uint_narrow!` does for
  the fixed-width narrowings.
- **`SIZEU064 : Conn<usize, u64>`** — saturating embed. `ceil` is a lossless
  widen on every real target (`usize ≤ 64` bits); `inner` saturates `u64`
  values above `usize::MAX`. No fixup (a widening, like `uint_uint!`), and
  the identity iso on a 64-bit target.

**Why not reuse the existing `as`-based macros.** `usize` is pointer-width
(16/32/64-bit by target), so a fixed-width `as`-narrowing is wrong on some
targets: `uint_uint_narrow!(_, usize, u32)`'s `inner` is `x as usize`, which
*truncates* a `u32 > usize::MAX` on a 16-bit target (`70000 as u16 == 4464`)
where the Galois law needs *saturation*. Both Conns therefore clamp with
`TryFrom` instead of `as`, which keeps the left-Galois laws true on
16/32/64-bit targets with **no `cfg`** — the same reasoning the narrow macros
already rely on, lifted to a platform-variable width.

Both are one-sided left-Galois (`Conn::new_l`), so they carry the L-laws
(`galois_l`, `kernel_l`, monotonicity, idempotence) but not the triple-only
`floor_le_ceil`.

### Tests
- Inline spot checks in `src/core/size.rs`: saturation at the maxima, the
  `inner(u32::MAX) = usize::MAX` fixup, and low-range round-trips.
- Integration battery `tests/core/size.rs` (registered in `tests/core.rs`),
  reusing the `single_sided_props!` shape from `tests/core/u032.rs`
  (`galois_upper`, `ceil_monotone`, `inner_monotone`, `kernel`, `idempotent`)
  for both Conns, with boundary-biased strategies pinning `0` / `usize::MAX`
  / `u32::MAX` / `u64::MAX`.

Gates green: `cargo test` (2664 passed), `cargo clippy --all-targets -D
warnings`, `cargo fmt --check`, `cargo doc` with `RUSTDOCFLAGS=-D warnings`.

### Docs / registry sync
`src/core.rs` (`pub mod size;` + submodule bullet + `SIZE` prefix-table row),
`src/lib.rs` naming table, `README.md` module table, and `CHANGELOG.md`
`### Added`. The README SMT-verification claim is caveated: kani's CBMC models
one concrete pointer width per run, so the `usize` family is covered by the
proptest battery on the host target rather than a width-agnostic SMT proof
(the only integer family without a kani harness, by design).

### Deferred
`u8`/`u16`/`u128` rungs and an `isize` family (mechanical repeats of the two
templates). See `doc/plans/plan-2026-07-05-01.md` → Deferred / Review for the
full list, including a flagged pre-existing doc drift in `src/kani.rs:47–52`
(byte-encoding harness consts listed under stale `fixed::…` paths that now live
in `core::…`).
