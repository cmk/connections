# PR #17 — core::usize rename + portable core::isize + kani doc fix

## Summary

Three changes, all keeping the crate architecture-portable (no target-width
assumption is introduced anywhere):

### 1. Rename `core::size` → `core::usize` (`SIZEU### → USZEU###`)

Pure rename of the `usize` family merged in PR #16 — the portable
`TryFrom` / `From` bodies and the 16/32/64-bit framing are unchanged. Files
`src/core/size.rs` / `tests/core/size.rs` move to `…/usize.rs`; the five
consts and their test fns are renamed. The `SIZE` prefix mnemonic becomes
`USZE` in the `src/core.rs` and `src/lib.rs` naming tables.

### 2. New `core::isize` family — portable, three rungs

`isize → i8` / `i16` / `i128`, built from the stock fixed-width macros so
each const is **lawful on every pointer width**:

- **`ISZEI008` / `ISZEI016`** — `int_int_narrow!`. `isize` is always ≥ 16
  bits, so `→ i8` is always a narrowing and `→ i16` is a narrowing (32/64-bit)
  or the identity iso (16-bit) — never a widening. Saturate-both `ceil` with
  the high-end FINE_MAX `inner` fixup, exactly like `I064I008` / `I064I016`.
- **`ISZEI128`** — `ext_int!`, `Conn<Extended<isize>, i128>`. `i128` is the
  widest, so `→ i128` is always a widening. The `Extended` source is
  required: `isize::MIN` embeds *above* `i128::MIN`, so a plain
  `Conn<isize, i128>` would leave unreachable negatives and break left-Galois
  at the bottom. `NegInf` / `PosInf` absorb them — the same construction as
  `I064I128`.

**`isize → i32` and `isize → i64` are intentionally omitted.** Those are the
only rungs whose cast *direction flips* with pointer width (`→ i32` narrows
on 64-bit, is the identity on 32-bit, and *widens* on 16-bit; `→ i64` is the
identity on 64-bit and widens on ≤ 32-bit). No single stock-macro const
covers a flipping rung — `int_int_narrow!` truncates on the widening target,
`ext_int!` overflows computing `BELOW` / `ABOVE` on the iso/narrowing target
— so a portable version needs a bespoke cross-regime `Extended` hybrid.
Omitting the two rungs keeps every shipped const portable and defers that
strategy choice with a clean slate (rather than baking in a 64-bit
assumption now).

All five `USZE****` and the three `ISZE****` are one-sided left-Galois; the
`ext_int!`-based `ISZEI128` additionally carries `closure_upper`.

### 3. Fix `src/kani.rs` `## Layout` doc drift

The byte-encoding harness rows listed their target consts under stale
`fixed::…` paths; the consts live in `core::…` (`BOOLBE01` / `BOOLLE01` in
`core::bool`, not `fixed::u008`). Corrected the right-column paths. This
clears the drift flagged in Plan 01's Review. Shipped as a separate `doc:`
commit.

### Tests

- `tests/core/usize.rs` — the `single_sided_props!` battery for all five
  `USZE****` (renamed from the `SIZE****` battery), boundary-biased
  strategies.
- `tests/core/isize.rs` — `single_sided_props!` for `ISZEI008` / `ISZEI016`
  (plain `isize` source); `ext_int_props!` for `ISZEI128` (`Extended<isize>`
  source via `arb_ext_isize()`), copying the `core::i064` integration shape.
- Inline spot checks in `src/core/isize.rs`: saturate-both + FINE_MAX fixup
  for the narrowings; `ceil(PosInf) = isize::MAX + 1` /
  `ceil(NegInf) = i128::MIN` for the widening.

Gates green: `cargo test` (2664 passed), `cargo clippy --all-targets -- -D
warnings`, `cargo fmt --check`, `cargo doc` with `RUSTDOCFLAGS=-D warnings`.

### Docs / registry sync

`src/core.rs` (module decls + Submodules bullet + `USZE`/`ISZE` prefix rows),
`src/lib.rs` naming table, `README.md` module table + SMT caveat (both
pointer-width families named), and `CHANGELOG.md` `[Unreleased]`.

### Deferred

`ISZEI032` / `ISZEI064` (the direction-flipping rungs); kani harnesses for
the pointer-width families. See `doc/plans/plan-2026-07-05-02.md` →
Deferred / Review.
