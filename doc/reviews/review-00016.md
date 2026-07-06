# PR #16 — usize Conn family (SIZEU008 … SIZEU128)

## Summary

Adds a `usize` cast family in a new `core::size` submodule — the first
pointer-width endpoint in the crate. The complete `usize → u8`/`u16`/`u32`
/`u64`/`u128` ladder:

- **`SIZEU008` / `SIZEU016` / `SIZEU032`** — saturating narrows. `ceil` clamps
  source values above the target max; `inner` widens with the FINE_MAX fixup
  (`inner(uN::MAX) = usize::MAX`) so left-Galois holds at the saturation
  plateau, exactly as `uint_uint_narrow!` does for the fixed-width narrowings.
  `→u8` narrows on every target; `→u16` is the identity iso on a 16-bit target
  and narrows otherwise; `→u32` narrows on 64-bit, is an iso on 32-bit, and
  widens on 16-bit.
- **`SIZEU064` / `SIZEU128`** — saturating embeds. `ceil` is a lossless widen
  on every real target (`usize ≤ 64` bits); `inner` saturates values above
  `usize::MAX`. No fixup (widenings, like `uint_uint!`); `→u64` is the identity
  iso on a 64-bit target.

**Why not reuse the existing `as`-based macros.** `usize` is pointer-width
(16/32/64-bit by target), so a fixed-width `as`-narrowing is wrong on some
targets: `uint_uint_narrow!(_, usize, u32)`'s `inner` is `x as usize`, which
*truncates* a `u32 > usize::MAX` on a 16-bit target (`70000 as u16 == 4464`)
where the Galois law needs *saturation*. Every conversion here clamps with
`TryFrom` — or the infallible `From` for the `u8`/`u16 → usize` widen in
`inner`, where a `From` exists (this also keeps clippy's
`unnecessary_fallible_conversions` quiet). That keeps the left-Galois laws true
on 16/32/64-bit targets with **no `cfg`** in the Conn definitions — the same
reasoning the narrow macros already rely on, lifted to a platform-variable
width.

All five are one-sided left-Galois (`Conn::new_l`), so they carry the L-laws
(`galois_l`, `kernel_l`, monotonicity, idempotence) but not the triple-only
`floor_le_ceil`.

### Tests
- Inline spot checks in `src/core/size.rs`: saturation at the maxima, the
  `inner(uN::MAX) = usize::MAX` fixup on the narrowings, and low-range
  round-trips on the embeds. The one genuinely width-specific check —
  `SIZEU032.ceil(usize::MAX) == u32::MAX`, true only where `usize > u32` — is
  gated behind `cfg(target_pointer_width = "64")`.
- Integration battery `tests/core/size.rs` (registered in `tests/core.rs`),
  reusing the `single_sided_props!` shape from `tests/core/u032.rs`
  (`galois_upper`, `ceil_monotone`, `inner_monotone`, `kernel`, `idempotent`)
  for all five Conns, with boundary-biased strategies pinning `0` /
  `usize::MAX` / each `u{8,16,32}::MAX as usize` / `uN::MAX`.

Gates green: `cargo test`, `cargo clippy --all-targets -D warnings`, `cargo
fmt --check`, `cargo doc` with `RUSTDOCFLAGS=-D warnings`.

### Docs / registry sync
`src/core.rs` (`pub mod size;` + submodule bullet + `SIZE` prefix-table row),
`src/lib.rs` naming table, `README.md` module table, and `CHANGELOG.md`
`### Added`. The README SMT-verification claim is caveated: kani's CBMC models
one concrete pointer width per run, so the `usize` family is covered by the
proptest battery on the host target rather than a width-agnostic SMT proof
(the only integer family without a kani harness, by design).

### Deferred
An `isize` family (signed counterpart via an `Extended<isize>` source). See
`doc/plans/plan-2026-07-05-01.md` → Deferred / Review for the full list,
including a flagged pre-existing doc drift in `src/kani.rs:47–52` (byte-encoding
harness consts listed under stale `fixed::…` paths that now live in `core::…`).

## Local review (2026-07-05)

**Branch:** plan/2026-07-05-01
**Commits:** 3 (origin/main..plan/2026-07-05-01)
**Reviewer:** Codex (`codex review --base origin/main`)
**Prompt fingerprint:** AGENTS.md=4563f590caa7dbba5ea9eae973fa59182f1a6470 calibration=missing

---

The implementation has target-dependent test coverage that fails on 16-bit pointer-width targets, and the new public docs likely break the documented `cargo doc` gate with default features. These are blocking issues for the stated portability and repository gates.

Full review comments:

- [P1] Avoid feature-gated macro links in public docs — src/core/size.rs:28-28
  With the default `cargo doc` gate, the `macros` feature is disabled, so `crate::uint_uint_narrow` is not exported at the crate root (`macro_export` is feature-gated). Rustdoc treats this public intra-doc link, and the `crate::uint_uint` link in the `SIZEU064` docs, as unresolved; with `RUSTDOCFLAGS=-D warnings` this becomes a doc build failure. Use plain code text or avoid linking to feature-gated macros here.

- [P2] Make SIZEU032 max check pointer-width aware — src/core/size.rs:85-85
  On 16-bit pointer-width targets, `usize::MAX` is `65535`, so `SIZEU032.ceil(usize::MAX)` returns `65535` via `u32::try_from`, not `u32::MAX`. This makes `cargo test` fail on one of the target widths this Conn is documented to support; gate this assertion by `target_pointer_width` or compare against the TryFrom-saturating expected value.

