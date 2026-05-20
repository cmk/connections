# PR #7 — LX-keyed signed ints, NonZero widening + narrowing, audit polish

## Summary

Second pre-publish polish pass on the `connections` crate. Four
concerns:

1. **LX sentinel** — a new byte-array wrapper with default-derived
   lex `Ord` (semantics-neutral on the bytes themselves), plus
   bias-encoded big-endian `IxxxLXxy` Conns from signed ints
   targeting it. Closes the only gap in the byte-encoding ladder
   where lex compare disagreed with numeric compare; lets the crate
   produce sort-correct keys for byte-keyed stores (LMDB / RocksDB /
   sled) that compare bytes directly. *Renamed `KV` → `LX` late in
   review*: see "Wrapper rename" below.
2. **NonZero unsigned widening** — 10 new `N###N###` Conns
   `NonZeroU<N> → NonZeroU<M>` for every `N < M` across {8,16,32,
   64,128}. Mirrors the existing `U###U###` widening family at the
   NonZero layer; closes the user-flagged gap.
3. **NonZero narrowing (added mid-sprint)** — 20 new `N###N###`
   Conns via two new macros `nz_int_narrow!` and `nz_uint_narrow!`
   (10 each, one per N > M pair). The matching `nz_int_widen!` was
   investigated and **permanently dropped** as unsound on the bare
   `Conn` type — see "NonZero narrowing" section below.
4. **Audit polish** — leftover items from the four-agent code-health
   audit that didn't land in plan-01, plus a kani-tree path sweep
   triggered by user-flagged drift after the Plan-26 `core/`/`fixed/`
   split.

### LX (T1-T2)

- `connections::core::LX<const N: usize>(pub [u8; N])` — new
  wrapper with default-derived `Ord` (raw lex on the bytes). No
  custom `Ord` impl: the whole contract is that the bytes
  compare lexicographically. The wrapper is semantics-neutral —
  numeric-equivalence claims live on the bias-encoded Conn, not on
  the wrapper, so downstream consumers can use `LX<N>` for arbitrary
  lex-ordered byte data.
- Five signed-int bias-encoder isos: `I008LX01`, `I016LX02`,
  `I032LX04`, `I064LX08`, `I128LX16`, hosted source-side per the
  existing byte-encoding precedent (`I008BE01` lives in
  `src/core/i008.rs`). Each is `iso!`-declared (degenerate Galois
  iso, full triple). Encoder biases by `1 << (bits-1)` then
  big-endian; decoder unbiases. Property suite on `I008LX01` covers
  iso-roundtrip / galois L+R / floor_le_ceil / order-preservation
  (signed numeric compare ⟺ raw byte lex compare on the encoded
  bytes — the contract the bias encoding earns).

### Wrapper rename `KV` → `LX`

Late in review, a downstream agent asked for the type's semantics
relaxed from "key-value store key" to plain lexicographic byte
ordering. The original `KV` ("key-value") framing baked in the
bias-encoded numeric-ordering use case; the relaxed `LX` ("lex")
framing keeps only the default-`Ord`-is-lex contract on the bytes,
so other consumers can use the wrapper for arbitrary lex-ordered
byte data without inheriting the numeric-equivalence claim.

Mechanical impact: type `KV<N>` → `LX<N>`; helper fns
`{i8,i16,i32,i64,i128}_to_kv{01,02,04,08,16}` and inverses →
`*_to_lx*` / `lx*_to_*`; Conn constants `I###KV0N` → `I###LX0N`;
test identifiers `i00Nkv0N_*` / `arb_kvbyteN` → `i00Nlx0N_*` /
`arb_lxbyteN`. The bias-encoded Conn family kept its semantics
unchanged; the rename only affects the wrapper-as-an-`Ord`-contract
identity. Doc on the wrapper now spells out that it is semantics-
neutral.

### NonZero unsigned widening (T3-T4)

- `nz_uint_widen!` macro added to `src/core.rs` next to
  `nz_uint_ext!`. Generates `pub const NAME: Conn<NonZeroUN,
  NonZeroUM, L>` — left-Galois single-sided, mirroring `uint_uint!`
  at the NonZero layer. `ceil` lossless-widens (no zero gap because
  `NonZeroU<N> ≥ 1`); `inner` saturates at `NonZeroU<N>::MAX`.
- 10 Conns landed in `src/core/uNNN.rs` (source-side per CLAUDE.md
  placement rule): `N008N016` … `N064N128`. Spot tests on
  `N008N016` for boundary saturation behavior; galois-L proptest
  battery on every (N,M) pair.
- Macro added to `connections::macros` re-export under the
  `macros` feature; docs table in `src/lib.rs` extended with rows
  for `nz_uint_widen!` and `law_battery!`.

### NonZero narrowing (added mid-sprint)

User flagged three missing macros in `doc/notes/note-2026-05-19-01.md`
(NonZero Conns section): `nz_int_widen!`, `nz_int_narrow!`,
`nz_uint_narrow!`. After investigation, only the two narrowing
macros are soundly expressible as bare `Conn<NonZero<i_N>,
NonZero<i_M>>`.

**`nz_int_narrow!`** — signed `NonZero<i_N> → NonZero<i_M>` with
N > M, left-Galois. `ceil` saturates source values to `i_M::MIN` /
`i_M::MAX` (both nonzero, so no zero gap reappears); `inner`
lossless-widens with the FINE_MAX fixup pattern from
`int_int_narrow!`. 10 Conns spanning every (N, M) pair with N > M:
`N016N008`; `N032N{008,016}`; `N064N{008,016,032}`;
`N128N{008,016,032,064}`. Source-side hosting in `src/core/iNNN.rs`.

**`nz_uint_narrow!`** — unsigned `NonZero<u_N> → NonZero<u_M>` with
N > M, left-Galois. `ceil` saturates above `u_M::MAX`; no low-end
branch (`NonZero<u_N> ≥ 1 > 0 = u_M::MIN`). `inner` lossless-widens
with FINE_MAX fixup. 10 Conns mirror the signed narrowing tier:
`N016N008`; `N032N{008,016}`; `N064N{008,016,032}`;
`N128N{008,016,032,064}`. Source-side hosting in `src/core/uNNN.rs`.

Per-source signed/unsigned name collision (`core::i016::N016N008` vs
`core::u016::N016N008`) is resolved by qualified-import per
CLAUDE.md's collision rule.

**Why `nz_int_widen!` was dropped.** Mirror the unsigned widening
template at the signed layer:

- `ceil`: lossless embedding `NZ<i_N> → NZ<i_M>` (N < M).
- `inner`: saturate target values outside `[i_N::MIN, i_N::MAX]` to
  the matching boundary.

Implementing this and running the L-Galois proptest (with a=NZ(-128),
b=NZ(-129)) gives: `ceil(a) = NZ(-128)`, LHS `NZ(-128) ≤ NZ(-129)` is
**false**; `inner(b) = NZ(i_N::MIN) = NZ(-128)`, RHS `a ≤ inner(b)` is
**true**. L-Galois violated. R-Galois fails symmetrically at the upper
plateau. The root cause: the target range `[i_M::MIN, i_N::MIN as
i_M − 1]` has no representative in `NonZero<i_N>` (the supremum of an
empty set requires a `-Inf` sentinel that `NonZero<i_N>` doesn't
provide). Contrast `nz_uint_widen!`, where the lower bound
`u_N::MIN = 0 < 1 = NonZero<u_M>::MIN` makes that target range
empty.

Workaround for downstream users: compose `nz_int_ext!` +
`ext_int!` to widen via `i_N → Extended<i_N> → i_M → NonZero<i_M>`.
A future `nz_int_widen!` would need new `Extended<NonZero<i_N>>`
infrastructure; out of scope here.

### Stale-path sweep

User flagged 3 stale `crate::fixed::iNNN` references in
`src/kani/nz_ext.rs` + 2 hifi doc comments. The same drift existed
across 5 more kani harnesses — sweep-fixed:

- `src/kani/{ext_int,int_narrow,uint_narrow,uint_sat,uint_widen}.rs`:
  all importing the moved consts via `crate::fixed::iNNN` /
  `crate::fixed::uNNN`. Silent in `cargo build` / `cargo test`
  because `src/kani/` is `cfg(all(kani, feature = "fixed"))`-gated;
  would fail under `cargo kani`. Rewired to per-source-module paths
  (`crate::core::iNNN` / `uNNN`).
- Reorganised each harness's grouping from per-destination to
  per-source so the import path matches the actual hosting after
  the Plan-26 split.
- Legitimate `fixed::iNNN` / `uNNN` imports preserved in
  `iso_family.rs` and `fix_fix_*.rs` (Q-format Conns genuinely host
  in `src/fixed/`).

### Polish (T5-T11)

- Doctest-style fixes in `src/core/f032.rs` and `src/core/f064.rs`:
  replaced tautological `assert!(x <= y)` / `assert!(x >= y)`
  bracketing with `assert_eq!` against named f16/f32 grid points
  around PI. Aligns with memory `feedback_doctest_style`.
- `#[cfg_attr(docsrs, doc(cfg(feature = "f16")))]` mirrors on
  `F032F016` and `F064F016` — completes the docsrs feature-mirror
  story.
- 17+ GitLab `MR !63…!69 round-N` parentheticals removed from
  `src/hifi/{calendar,epoch,duration}.rs` (frozen archive refs with
  no GitHub equivalent).
- `lib.rs` macros table extended with `nz_uint_widen!` and
  `law_battery!` rows; both added to `connections::macros::*`
  re-export.
- Stale "for backward-compat during the migration" prose deleted
  from `src/fixed.rs:60-78` (migration is done).
- `src/lib.rs:13` F016 row repointed at `float::F016` (the actual
  type location).
- `src/interval.rs:68` — added `Hash` to `Interval<A>`'s derive
  pack. Surprising absence given `Eq` was already there.
- `tests/core/*.rs` and `tests/fixed/*.rs` headers swept of stale
  `conn::std::iN` / `conn::fixed::uN` references (pre-rename module
  paths).

## Test plan

- `cargo test --features fixed,time,hifi,macros,proptest` — 4922
  passing (1827 lib +22 from LX/N###N### properties — adds 20 new
  narrowing-pair galois props + 2 narrow-pair spot tests over the
  previous round; 90 doctests +1 for I008LX01), 14 doctests ignored
  per existing harness.
- `cargo clippy --all-targets --features fixed,time,hifi,macros,
  proptest -- -D warnings` — clean.
- `RUSTDOCFLAGS="--cfg docsrs -D warnings" cargo +nightly doc
  --no-deps --features fixed,proptest,macros,time` — clean.
- Spot checks: `I008LX01` boundary table (MIN→0x00, 0→0x80,
  MAX→0xFF), `N008N016` saturation at `u8::MAX`, `N016N008`
  both-plateau saturation + FINE_MAX fixup.

## Deferred

See `doc/plans/plan-2026-05-19-02.md § Review`.

## Local review (2026-05-19)

**Branch:** plan/2026-05-19-02
**Commits:** 5 (origin/main..plan/2026-05-19-02)
**Reviewer:** Codex (`codex review --base origin/main`)
**Prompt fingerprint:** AGENTS.md=b5f7584f2875c10abb637c9b483b4c7e0cb37891 calibration=missing

---

The code builds and tests pass in the checked feature sets, but the patch introduces a public documentation/API map entry pointing to a non-existent F016 path.

Review comment:

- [P3] Point F016 at the actual f16 module — src/lib.rs:13-13
  With the `f16` feature enabled, `connections::float::F016` does not exist; the public alias is defined in `core::f016::F016`. Users following this naming table will be sent to a dead path unless this is reverted or a real `float::F016` re-export is added.


<!-- gh-id: 3270931041 -->
### Copilot on [`tests/fixed/u128.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931041) (2026-05-20 02:44 UTC)

The doc comment references `tests/fixed/u08_galois.rs`, but that file doesn't exist in `tests/fixed/`. Please update the reference to an existing rationale location (e.g., `tests/fixed.rs`, or the relevant module file such as `tests/fixed/u008.rs`).

<!-- gh-id: 3270931061 -->
### Copilot on [`tests/fixed/u064.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931061) (2026-05-20 02:44 UTC)

The doc comment references `tests/fixed/u08_galois.rs`, but that file doesn't exist in `tests/fixed/`. Please update the reference to an existing rationale location (e.g., `tests/fixed.rs`).

<!-- gh-id: 3270931075 -->
### Copilot on [`tests/fixed/u032.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931075) (2026-05-20 02:44 UTC)

The doc comment references `tests/fixed/u08_galois.rs`, but that file doesn't exist in `tests/fixed/`. Please update the reference to an existing rationale location (e.g., `tests/fixed.rs`).

<!-- gh-id: 3270931083 -->
### Copilot on [`tests/fixed/u016.rs:4`](https://github.com/cmk/connections/pull/7#discussion_r3270931083) (2026-05-20 02:44 UTC)

The doc comment references `tests/fixed/u08_galois.rs`, but that file doesn't exist in `tests/fixed/`. Please update the reference to an existing rationale location (e.g., `tests/fixed.rs`).

<!-- gh-id: 3270931091 -->
### Copilot on [`tests/fixed/u008.rs:9`](https://github.com/cmk/connections/pull/7#discussion_r3270931091) (2026-05-20 02:44 UTC)

This comment refers to `tests/fixed/u<width>_galois.rs` as a standalone invocation, but the fixed batteries are currently aggregated under `tests/fixed.rs` (with per-module `#[path] mod ...`). Please update the filename reference (and the standalone-invocation claim, if applicable) so it matches the current test layout.

<!-- gh-id: 3270931099 -->
### Copilot on [`tests/core/u128.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931099) (2026-05-20 02:44 UTC)

The header comment points to `tests/core/u8_galois.rs`, but that file doesn't exist in `tests/core/`. Please update the reference to an existing rationale location (e.g., `tests/core.rs` and/or `tests/core/u008.rs`).

<!-- gh-id: 3270931111 -->
### Copilot on [`tests/core/u064.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931111) (2026-05-20 02:44 UTC)

The header comment points to `tests/core/u8_galois.rs`, but that file doesn't exist in `tests/core/`. Please update the reference to an existing rationale location (e.g., `tests/core.rs` and/or `tests/core/u008.rs`).

<!-- gh-id: 3270931118 -->
### Copilot on [`tests/core/u032.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931118) (2026-05-20 02:44 UTC)

The header comment points to `tests/core/u8_galois.rs`, but that file doesn't exist in `tests/core/`. Please update the reference to an existing rationale location (e.g., `tests/core.rs` and/or `tests/core/u008.rs`).

<!-- gh-id: 3270931124 -->
### Copilot on [`tests/core/u016.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931124) (2026-05-20 02:44 UTC)

The header comment points to `tests/core/u8_galois.rs`, but that file doesn't exist in `tests/core/`. Please update the reference to an existing rationale/counterexample location (e.g., `tests/core/u008.rs` or the crate-level aggregator `tests/core.rs`).

<!-- gh-id: 3270931134 -->
### Copilot on [`tests/core/u008.rs:5`](https://github.com/cmk/connections/pull/7#discussion_r3270931134) (2026-05-20 02:44 UTC)

This doc comment references `tests/fixed/u<width>_galois.rs`, but that file pattern doesn't exist in the current tree. Please update the reference to match the current fixed test layout (e.g., `tests/fixed.rs` or `tests/fixed/u008.rs`).

<!-- gh-id: 3270931151 -->
### Copilot on [`tests/core/i128.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931151) (2026-05-20 02:44 UTC)

The header comment points to `tests/core/u8_galois.rs`, but that file doesn't exist in `tests/core/`. Please update the reference to an existing rationale location (e.g., `tests/core.rs` and/or `tests/core/u008.rs`).

<!-- gh-id: 3270931161 -->
### Copilot on [`tests/core/i064.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931161) (2026-05-20 02:44 UTC)

The header comment points to `tests/core/u8_galois.rs`, but that file doesn't exist in `tests/core/`. Please update the reference to an existing rationale/counterexample location (e.g., `tests/core/u008.rs` or `tests/core.rs`).

<!-- gh-id: 3270931174 -->
### Copilot on [`tests/core/i032.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931174) (2026-05-20 02:44 UTC)

The header comment points to `tests/core/u8_galois.rs`, but that file doesn't exist in `tests/core/`. Please update the reference to an existing rationale/counterexample location (e.g., `tests/core/u008.rs` or `tests/core.rs`).

<!-- gh-id: 3270931181 -->
### Copilot on [`tests/core/i016.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931181) (2026-05-20 02:44 UTC)

The header comment points to `tests/core/u8_galois.rs`, but that file doesn't exist in `tests/core/`. Please update the reference to an existing rationale/counterexample location (e.g., `tests/core/u008.rs` or `tests/core.rs`).

<!-- gh-id: 3270931193 -->
### Copilot on [`tests/core/i008.rs:2`](https://github.com/cmk/connections/pull/7#discussion_r3270931193) (2026-05-20 02:44 UTC)

The header comment points to `tests/core/u8_galois.rs`, but that file doesn't exist in `tests/core/`. Please update the reference to an existing rationale/counterexample location (e.g., `tests/core/u008.rs` or `tests/core.rs`).

<!-- gh-id: 3270931208 -->
### Copilot on [`src/core/i016.rs:85`](https://github.com/cmk/connections/pull/7#discussion_r3270931208) (2026-05-20 02:44 UTC)

`I016KV02` is a new KV (lex-key) encoding iso, but this module’s test suite doesn’t exercise it (unlike `I008KV01`, which has boundary + order-preservation properties). Please add at least basic round-trip + boundary-byte checks and an order/lex-compare property for `I016KV02` to avoid regressions in the bias constant or endianness.

<!-- gh-id: 3270931225 -->
### Copilot on [`src/core/i032.rs:86`](https://github.com/cmk/connections/pull/7#discussion_r3270931225) (2026-05-20 02:44 UTC)

`I032KV04` is a new KV (lex-key) encoding iso, but this module’s test suite doesn’t exercise it. Please add round-trip + boundary-byte checks and an order/lex-compare property (as done for `I008KV01`) to catch mistakes in the bias constant or endianness.

<!-- gh-id: 3270931239 -->
### Copilot on [`src/core/i064.rs:87`](https://github.com/cmk/connections/pull/7#discussion_r3270931239) (2026-05-20 02:44 UTC)

`I064KV08` is a new KV (lex-key) encoding iso, but this module’s test suite doesn’t exercise it. Please add round-trip + boundary-byte checks and an order/lex-compare property (as done for `I008KV01`) so the bias constant/endian shape can’t drift silently.

<!-- gh-id: 3270931258 -->
### Copilot on [`src/core/i128.rs:90`](https://github.com/cmk/connections/pull/7#discussion_r3270931258) (2026-05-20 02:44 UTC)

`I128KV16` is a new KV (lex-key) encoding iso, but this module’s test suite doesn’t exercise it. Please add round-trip + boundary-byte checks and an order/lex-compare property (as done for `I008KV01`) to guard the bias constant/endian encoding.

<!-- gh-id: 4324819909 -->
### copilot-pull-request-reviewer[bot] — COMMENTED ([2026-05-20 02:44 UTC](https://github.com/cmk/connections/pull/7#pullrequestreview-4324819909))

## Pull request overview

This PR is a pre-publish polish pass for the `connections` crate that extends the crate’s numeric-encoding ladder with KV-store-sortable signed-int key encodings, fills in NonZero widening/narrowing Conn families via new macros, and cleans up assorted drift and documentation issues (including kani harness import paths and hifi doc comment artifacts).

**Changes:**
- Added `core::KV<N>` and new signed-int `IxxxKVyy` isos producing lex-orderable big-endian key bytes for KV stores.
- Added NonZero Conn macro families (`nz_uint_widen!`, `nz_int_narrow!`, `nz_uint_narrow!`) and instantiated the corresponding `N###N###` Conns across u8..u128 / i16..i128.
- Swept polish/drift fixes across kani harnesses, docs tables/re-exports, and various test/doc comments.

### Reviewed changes

Copilot reviewed 44 out of 44 changed files in this pull request and generated 20 comments.

<details>
<summary>Show a summary per file</summary>

| File | Description |
| ---- | ----------- |
| tests/fixed/u128.rs | Updates header docs for fixed u128 proptest battery. |
| tests/fixed/u064.rs | Updates header docs for fixed u64 proptest battery. |
| tests/fixed/u032.rs | Updates header docs for fixed u32 proptest battery. |
| tests/fixed/u016.rs | Updates header docs for fixed u16 proptest battery. |
| tests/fixed/u008.rs | Updates header docs for fixed u8 proptest battery. |
| tests/core/u128.rs | Updates header docs for core u128 proptest battery. |
| tests/core/u064.rs | Updates header docs for core u64 proptest battery. |
| tests/core/u032.rs | Updates header docs for core u32 proptest battery. |
| tests/core/u016.rs | Updates header docs for core u16 proptest battery. |
| tests/core/u008.rs | Updates header docs for core u8 proptest battery. |
| tests/core/i128.rs | Updates header docs for core i128 proptest battery. |
| tests/core/i064.rs | Updates header docs for core i64 proptest battery. |
| tests/core/i032.rs | Updates header docs for core i32 proptest battery. |
| tests/core/i016.rs | Updates header docs for core i16 proptest battery. |
| tests/core/i008.rs | Updates header docs for core i8 proptest battery. |
| src/lib.rs | Fixes F016 path in the public naming table; extends macro table and macro re-exports. |
| src/kani/uint_widen.rs | Rewires kani harness imports to `crate::core::*` after the core/fixed split; reorganizes by source module. |
| src/kani/uint_sat.rs | Rewires kani harness imports to `crate::core::*` and groups by source module. |
| src/kani/uint_narrow.rs | Rewires kani harness imports to `crate::core::*` and groups by source module. |
| src/kani/nz_ext.rs | Fixes stale kani import paths for NonZero extension Conns. |
| src/kani/int_narrow.rs | Fixes stale kani import paths for int narrowing Conns. |
| src/kani/ext_int.rs | Fixes stale kani import paths for Extended-source widening Conns; reorganizes by source. |
| src/interval.rs | Adds `Hash` derive to `Interval<A>`. |
| src/hifi/epoch.rs | Removes stale GitLab MR parenthetical references from doc comments/tests. |
| src/hifi/duration.rs | Removes stale GitLab MR parenthetical references from doc comments/tests. |
| src/hifi/calendar.rs | Fixes stale module path in docs and removes GitLab MR parentheticals. |
| src/hifi.rs | Fixes stale module path reference in docs. |
| src/float.rs | Adds `float::F016` alias (feature-gated) and docsrs cfg mirror. |
| src/fixed.rs | Removes stale “migration/backward-compat” documentation text. |
| src/core/u128.rs | Adds `nz_uint_narrow!` instantiations (N128N###) and proptests. |
| src/core/u064.rs | Adds `nz_uint_narrow!` (N064N###) + `nz_uint_widen!` (N064N128) and proptests. |
| src/core/u032.rs | Adds `nz_uint_narrow!` (N032N###) + `nz_uint_widen!` and proptests. |
| src/core/u016.rs | Adds `nz_uint_narrow!` (N016N008) + `nz_uint_widen!` and spot/property tests. |
| src/core/u008.rs | Adds `nz_uint_widen!` instantiations (N008N###) and spot/property tests. |
| src/core/i128.rs | Adds `nz_int_narrow!` (N128N###) and `I128KV16` iso. |
| src/core/i064.rs | Adds `nz_int_narrow!` (N064N###) and `I064KV08` iso. |
| src/core/i032.rs | Adds `nz_int_narrow!` (N032N###) and `I032KV04` iso. |
| src/core/i016.rs | Adds `nz_int_narrow!` (N016N008) and `I016KV02` iso. |
| src/core/i008.rs | Adds `I008KV01` iso plus boundary/roundtrip/Galois/order-preservation property tests. |
| src/core/f064.rs | Improves doctest assertions and adds docsrs cfg mirror for f16-gated item. |
| src/core/f032.rs | Improves doctest assertions and adds docsrs cfg mirror for f16-gated item. |
| src/core.rs | Introduces `KV<N>` wrapper and adds the new NonZero widening/narrowing macros (and rationale for no `nz_int_widen!`). |
| doc/reviews/review-00007.md | Audit-trail review record (out of review scope per repo rules). |
| doc/plans/plan-2026-05-19-02.md | Adds the sprint plan describing KV + NonZero macro work and associated polish. |
</details>







<!-- gh-id: 3270931271 -->
### Copilot on [`doc/plans/plan-2026-05-19-02.md:18`](https://github.com/cmk/connections/pull/7#discussion_r3270931271) (2026-05-20 02:44 UTC)

This plan still contains a few now-stale technical details that conflict with the shipped diff:
- Line 15 has a typo in the type mapping (`NonZeroUN> → NonZeroUM`).
- The KV snippet (lines 54–55) includes `Default`, but `KV<N>` in `src/core.rs` intentionally does not derive `Default` (see the later “Design deviations” note).
- The `nz_uint_widen!` signature here (lines 107–112) still shows a 3-arg form, but the macro in `src/core.rs` takes 5 args.
Please update these earlier sections so readers don’t copy/paste incorrect signatures/derives even if they miss the later review notes.


<!-- gh-id: 3271186151 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271186151))

Fixed — repointed to `tests/fixed/u008.rs` (the actual rationale file; the `_galois` suffix was a pre-restructure stale ref).

<!-- gh-id: 3271186337 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271186337))

Fixed — repointed to `tests/fixed/u008.rs` (the actual rationale file; the `_galois` suffix was a pre-restructure stale ref).

<!-- gh-id: 3271186579 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271186579))

Fixed — repointed to `tests/fixed/u008.rs` (the actual rationale file; the `_galois` suffix was a pre-restructure stale ref).

<!-- gh-id: 3271186786 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271186786))

Fixed — repointed to `tests/fixed/u008.rs` (the actual rationale file; the `_galois` suffix was a pre-restructure stale ref). Also corrected the `src/conn/fixed/u016.rs` path to `src/fixed/u016.rs`.

<!-- gh-id: 3271186965 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271186965))

Fixed — rewrote the header to reflect the actual integration-test layout (mounted from `tests/fixed.rs` aggregator via `#[path]`, not separate standalone rustc invocations) and corrected the spot-test path to `src/fixed/u008.rs`.

<!-- gh-id: 3271187300 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271187300))

Fixed — repointed to `tests/core/u008.rs` (the canonical core rationale file).

<!-- gh-id: 3271187461 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271187461))

Fixed — repointed to `tests/core/u008.rs` (the canonical core rationale file).

<!-- gh-id: 3271187744 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271187744))

Fixed — repointed to `tests/core/u008.rs` (the canonical core rationale file).

<!-- gh-id: 3271187942 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271187942))

Fixed — repointed to `tests/core/u008.rs` (the canonical core rationale file).

<!-- gh-id: 3271188189 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271188189))

Fixed — cross-tree precedent ref updated from `tests/fixed/u<width>_galois.rs` to `tests/fixed/u008.rs` (the actual rationale file).

<!-- gh-id: 3271188512 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271188512))

Fixed — repointed to `tests/core/u008.rs` (the canonical core rationale file).

<!-- gh-id: 3271188718 -->
#### ↳ cmk ([2026-05-20 04:18 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271188718))

Fixed — repointed to `tests/core/u008.rs` (the canonical core rationale file).

<!-- gh-id: 3271188962 -->
#### ↳ cmk ([2026-05-20 04:19 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271188962))

Fixed — repointed to `tests/core/u008.rs` (the canonical core rationale file).

<!-- gh-id: 3271189154 -->
#### ↳ cmk ([2026-05-20 04:19 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271189154))

Fixed — repointed to `tests/core/u008.rs` (the canonical core rationale file).

<!-- gh-id: 3271189365 -->
#### ↳ cmk ([2026-05-20 04:19 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271189365))

Fixed — repointed to `tests/core/u008.rs` (the canonical core rationale file).

<!-- gh-id: 3271189893 -->
#### ↳ cmk ([2026-05-20 04:19 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271189893))

Fixed — added the I016LX02 battery: boundary bytes, iso-roundtrip-l, roundtrip-ceil, galois L/R, floor_le_ceil, and signed-cmp ⟺ raw-byte lex compare. Mirrors I008LX01.

<!-- gh-id: 3271190108 -->
#### ↳ cmk ([2026-05-20 04:19 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271190108))

Fixed — added the I032LX04 battery (same shape as I008LX01: boundary bytes + iso-roundtrip + galois L/R + floor_le_ceil + signed-cmp ⟺ raw-byte lex compare).

<!-- gh-id: 3271190296 -->
#### ↳ cmk ([2026-05-20 04:19 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271190296))

Fixed — added the I064LX08 battery (same shape as I008LX01).

<!-- gh-id: 3271190441 -->
#### ↳ cmk ([2026-05-20 04:19 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271190441))

Fixed — added the I128LX16 battery (same shape as I008LX01).

<!-- gh-id: 3271190604 -->
#### ↳ cmk ([2026-05-20 04:19 UTC](https://github.com/cmk/connections/pull/7#discussion_r3271190604))

Fixed all three:
- Dropped the stray `>` from the type mapping (now `NonZeroUN → NonZeroUM`).
- Removed `Default` from the `LX<N>` snippet and added an inline note explaining why (`[u8; N]: Default` only for N ≤ 32 in const-generic-free form, and sibling wrappers don't have it either).
- Updated `nz_uint_widen!` to the 5-arg form (`NAME, NZN, UN, NZM, UM`) — extra primitives needed for the saturation `as`-cast.
