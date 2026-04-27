# MR !27 — Final pre-publish push: 45 missing Conns + `conn::std` restructure

## Summary

- Closes the API-symmetry gaps identified in the 0.1.0 publish
  audit (`note-2026-04-27-01.md`) by shipping **45 new `pub
  const` Conns** across four families:
  - **§1 I→I narrowing** (10 Conns, `int_int_narrow!`,
    left-Galois) — `I016I008` … `I128I064`.
  - **§2 U→U narrowing** (10, `uint_uint_narrow!`, left-Galois) —
    `U016U008` … `U128U064`.
  - **§3 U→I non-widening** (15, `uint_int_sat!`,
    **right-Galois** via new `Conn::new_right`) — `U008I008` …
    `U128I128`. The right-Galois shape is forced by the
    target-side saturation plateau (`i_M`'s negative half
    collapses to `0_u_N` via `inner`); single-sided left-Galois
    breaks at every `(0_u_M, neg_i_N)` corner.
  - **§4 I→U narrowing** (10, `int_uint_narrow!`, left-Galois) —
    `I016U008` … `I128U064`.

  Each new single-sided narrowing macro carries the same
  **FINE_MAX boundary fixup** in `inner` that landed in MR !20
  for `conn::fixed::u<width>` — required for `galois_l` to hold
  at the source-side saturation plateau.
- Restructures `conn::int` and `conn::uint` into per-primitive
  submodules `conn::std::{i8,i16,i32,i64,i128,u8,u16,u32,u64,u128}`
  per right-side wins. The 24 existing widening Conns are
  redistributed (e.g. `conn::int::I008I016 →
  conn::std::i16::I008I016`); the three existing macros
  (`uint_uint!`, `int_uint!`, `ext_int!`) move to
  `src/conn/std.rs` as `pub(crate) use`-exported items shared
  across submodules. Indirectly closes audit W1's recommendation
  by going one level deeper (`conn::std::<dest>` rather than
  `conn::primitive::{int,uint}`).
- Adds `Conn::new_right(inner, floor)` constructor (one-line
  additive API mirroring `new_left`). Documents the right-Galois
  single-sided shape and pins `ceil = floor`.
- Migrates std-int proptest batteries to integration tests under
  `tests/conn_std_<primitive>_galois.rs` (10 files), mirroring
  the pattern established in MR !20. Spot tests stay inline.
  Indirectly closes audit W2 for the std-int family.
- Updates `src/lib.rs` convention examples to `conn::std::*`
  paths and adds four representative new-narrowing bullets;
  `doc/design.md` file-tree expanded to enumerate every
  `conn/std/*.rs`. README.md docfence example switched from
  `conn::int::U008I016` to `conn::std::i16::U008I016`.

Net post-sprint coverage:
- **Fixed-width int/word Conns: 120** (was 75 — adds 45).
- **All 28 fixed-width Haskell `Connection.{Word,Int}` Casts
  ported**, plus 92 new Rust-only Conns covering i128/u128
  extensions and the four narrowing/non-widening directions
  Haskell doesn't define directly.

## Test plan

- [ ] `cargo test --workspace` — **~3180 tests** pass (1584 lib +
      ~1572 integration across 15 binaries + 26 doctests), 0
      failed.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `cargo doc --no-deps` — clean (modulo the pre-existing
      unrelated `arb` warning in `property/mod.rs`).

## Local review (2026-04-27)

**Branch:** sprint/missing-conns
**Commits:** 9 (origin/main..HEAD, including the post-review fix)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All eight feature commits use conventional prefixes (`feat:`,
`task:`, `doc:`); each leaves the build green. Plan T1–T8 map
cleanly. No merge commits.

### Code Quality

- `#![forbid(unsafe_code)]` posture preserved.
- `as` casts in the four narrowing macros are bounded explicitly
  before the cast. The `int_int_narrow!` `<$B>::MIN as $A` sign-
  extends correctly under the `bits($A) > bits($B)` contract.
- FINE_MAX fixup monotonicity verified: `inner(B::MAX-1)` is
  lossless widen `(B::MAX-1) as A` < `A::MAX`, so the jump at
  `B::MAX` stays monotone.
- §3 right-Galois shape correct: `Conn::new_right(inner, floor)`
  pins `ceil = floor`; `galois_r` holds at every plateau corner
  (verified at `(0_u_M, neg_i_N)` and `(u_M::MAX, i_N::MAX)`).
- `pub mod std` does not surprise; absolute `::std::` still
  reaches the standard library and no submodule pulls `use
  std::…` through the local shadow.
- `pub(crate) use macro_name` pattern works for cross-submodule
  macro sharing.

**Findings (must-fix, both addressed in fix commit):**

1. `src/conn/std.rs:28–31` — stale forward-reference comment
   ("Future commits T3–T6 add four more macros…") still
   referencing the macros now present in the file. **Fixed**:
   replaced with the full present-tense table of all seven macros
   plus a note on the FINE_MAX fixup.
2. `single_sided_props!` and `single_sided_right_props!` — missing
   `idempotent` law that the plan's Verification table and
   `missing-conns.md §5` both required. **Fixed**: added the
   `idempotent` proptest to all 10 `tests/conn_std_*_galois.rs`
   files (and incidentally to the existing `ext_int_props!`
   instances, which propagate via `replace_all` — the law is
   trivially satisfied for full-triple Conns too).

### Test Coverage

All 45 new Conns now drive the full law battery (galois +
monotonicity + kernel + idempotent). Existing widening Conns
likewise.

`floor_le_ceil` is intentionally not separately tested for the
single-sided Conns: `Conn::new_left` pins `floor = ceil` and
`Conn::new_right` pins `ceil = floor`, so the property holds
trivially by construction. This was implicit in the choice of
constructor; not separately documented in the test files
(reviewer flagged as cosmetic follow-up).

### Plan Conformance

T1–T8 implemented as planned. 45 Conn names match
`missing-conns.md` exactly. Module placement (right-side wins)
consistent throughout.

### Risks

**Rebase conflict with parallel branches.** Both
`origin/sprint/publish-prep` (MR !25) and `origin/sprint/cast-b`
(MR !26) still have `pub mod int;` / `pub mod uint;` in their
`src/conn.rs` and reference `conn::int::U008I016` in
`src/lib.rs` and `README.md`. This sprint deletes those modules
and edits the same lines. A rebase will require a manual
3-way merge in those three files if either MR lands first.
Tracked, not blocking the push.

`src/conn/time/date.rs:217` has a stale `conn::int::U008I016`
comment inside a `#[cfg(test)]` block. Cosmetic; queued as
follow-up.

No new dependencies. No TODOs/stubs.

### Recommendations

**Must fix before push:** None remaining (both reviewer items
addressed in the fix commit).

**Follow-up (future work):**

1. Per-const doctests on the 45 new Conns
   (`missing-conns.md §7` requirement). Pre-existing gap on the
   widening Conns too. Track separately.
2. Update `src/conn/time/date.rs:217` stale comment. One-line.
3. Document the `floor_le_ceil` skip rationale inline in the
   proptest macros (cosmetic).

<!-- glab-id: 3289342452 -->
<!-- glab-discussion: b3e7c82853271d1646fcc839ad2337d80251e2e3 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/std.rs:207` (2026-04-27 11:30 UTC) [open]

**[must-fix]** The `int_int_narrow!` macro's `inner` returns `<$B>::MIN as $A` for the low-plateau case without a FINE_MIN fixup, but the doc comment claims "The low-end plateau holds without fixup because `i_M::MIN as i_N` is strictly above `i_N::MIN`". While true for signed→signed narrowing (e.g. `i16::MIN as i32 = -32768 > i32::MIN`), the `ceil` function checks `x < <$B>::MIN as $A` and collapses everything below that threshold to `i_M::MIN` — so the left-Galois law requires `inner(i_M::MIN) ≤ a` for all `a` in that plateau (i.e. all `a < i_M::MIN as i_A`). Since `inner(i_M::MIN) = i_M::MIN as i_A` and every plateau source satisfies `a < i_M::MIN as i_A`, the law `a ≤ inner(b)` at `b = i_M::MIN` reduces to `a ≤ i_M::MIN as i_A`, which fails for plateau sources one below that value. This is the symmetric low-end analogue of the FINE_MAX bug and should be verified against the proptest `galois_upper` at `(a = i_A::MIN, b = i_B::MIN)`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3289342503 -->
<!-- glab-discussion: 06c11d7a303ae756d23634b7205da17e56846962 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/std.rs:251` (2026-04-27 11:30 UTC) [open]

**[follow-up]** The `uint_uint_narrow!` macro's `ceil` only saturates at the high end (`x > <$B>::MAX as $A → <$B>::MAX`) but has no low-end branch, which is correct since `u_N ≥ 0` always. However the doc comment says "The low end works without fixup" without explaining why, which makes the asymmetry with `int_int_narrow!` surprising. A one-line comment noting that unsigned source values are always ≥ 0 ≥ `u_M::MIN` would prevent future confusion.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3289342552 -->
<!-- glab-discussion: 4ffe45c53096db04a7c8e3b021f3759ab901aaf6 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `tests/conn_std_i8_galois.rs:59` (2026-04-27 11:30 UTC) [open]

**[must-fix]** The `single_sided_props!` macro for left-Galois Conns in this file tests `galois_upper` but not `galois_lower` (i.e., `inner(b) ≤ a ⟺ b ≤ floor(a)`). For `Conn::new_left`, `floor = ceil`, so `galois_lower` is a non-trivial constraint and is listed as a required property in the plan's Verification table (`conn_galois_l` covers both directions). The missing `galois_lower` test means the low-plateau behaviour of `int_int_narrow!`'s `inner` is unchecked by proptest in this file (and in the identical `single_sided_props!` macros in `conn_std_i16_galois.rs`, `conn_std_i32_galois.rs`, `conn_std_i64_galois.rs`, `conn_std_u16_galois.rs`, `conn_std_u32_galois.rs`, `conn_std_u64_galois.rs`, `conn_std_u128_galois.rs`).

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3289360791 -->
<!-- glab-discussion: b3e7c82853271d1646fcc839ad2337d80251e2e3 -->
#### ↳ cmk (2026-04-27 11:36 UTC) [open]

The Galois law actually holds at the low plateau — your derivation has a sign error: the law is `a ≤ inner(b)`, not `inner(b) ≤ a`. At `(a = i32::MIN, b = i8::MIN)`: `ceil(a) = i8::MIN ≤ i8::MIN = b` (true) and `a = i32::MIN ≤ inner(i8::MIN) = -128_i32` (true) — both sides match. Same at the "one below" boundary `(a = -129, b = -128)`. The proptest battery's `galois_upper` already covers these corners (proptest biases `any::<i32>()` toward boundary values) and they all pass. No fixup needed.

<!-- glab-id: 3289361254 -->
<!-- glab-discussion: 06c11d7a303ae756d23634b7205da17e56846962 -->
#### ↳ cmk (2026-04-27 11:36 UTC) [open]

Added a paragraph to the macro doc explaining why no low-end branch exists (unsigned sources start at `0 = u_N::MIN ≥ u_M::MIN = 0`, so no source value can fall below the target's minimum) and contrasting with `int_int_narrow!`'s symmetric two-arm shape.

<!-- glab-id: 3289361891 -->
<!-- glab-discussion: 4ffe45c53096db04a7c8e3b021f3759ab901aaf6 -->
#### ↳ cmk (2026-04-27 11:36 UTC) [open]

`galois_r` is not equivalent to `galois_l` at saturation plateaus, even for `Conn::new_left` where `floor = ceil`. Testing it on these single-sided Conns would FAIL by design. Verified at `(a = i32::MIN, b = i8::MIN)`: `inner(b) = -128`, so `b ≤ ceil(a) = i8::MIN ≤ i8::MIN` (true) but `inner(b) ≤ a` is `-128 ≤ -2_147_483_648` (false) — the bi-implication breaks. That's the defining asymmetry of single-sided new_left: only one of the two Galois laws holds. The plan's Verification table correctly lists `galois_l` only for §1/§2/§4; the pre-existing `single_sided_props!` macro in `conn::int`/`conn::uint` (now in `conn::std`) follows the same convention.
