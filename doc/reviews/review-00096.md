# Review of MR !96 — Plan 26: disentangle core primitives from `fixed/`

## Summary

- Introduce `src/core/` as the home for every Conn whose endpoints are
  pure Rust `core`/`std` primitive types (`iN`/`uN`, IEEE floats,
  `bool`, `char`, `NonZero<T>`). The crate's top-level domain split
  becomes `core/` vs `fixed/` (only the `fixed`-crate Q-format
  wrappers and their cross-crate isos / float bridges remain in
  `fixed/`).
- All `§1` std-int Conns, `§3` `NonZero` adjoints, `BE`/`LE` byte iso
  Conns, the per-IEEE-width float Conn submodules, and `U032CHAR` /
  `BOOL{BE,LE}01` move out of `fixed/` and `float/` into the new
  `core/` tree; the `LE<N>` byte wrapper and the 9 portable std-int
  macros move alongside them.
- Pre-1.0 hard rename: every in-repo doctest, integration test, and
  `README` / `EXAMPLES` import path has been updated to the new
  `connections::core::*` namespace; downstream consumers do their own
  one-shot find/replace. CLAUDE.md §"Module organization" is updated
  to match.

## Test plan

- `cargo test --features testing,macros,time,hifi` — full suite
  (1786 lib + ~3.5k integration + 93 doc) green.
- `cargo clippy --features testing,macros,time,hifi --all-targets -- -D warnings`
  — clean.
- `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features testing,macros,time --document-private-items`
  — no broken intra-doc links.
- `scripts/check_readme_mirror.sh` — README mirror aligned.
- Behavioural contract: zero new properties, zero `#[ignore]` introductions;
  every relocated `law_battery!` and `proptest!` block continues to pass at
  its new home. The diff is mechanical — file moves + import retargeting.

## Local review (2026-05-10)

**Branch:** `sprint/core-split`
**Commits:** 2 (origin/main..sprint/core-split)
**Reviewer:** Claude (sonnet, independent)

> **Note from /sprint-review:** the reviewer audited the diff (correct files, correct trait-claims), but their P2 plan-conformance section refers to `plan-2026-05-10-02.md` (the prior ConnL/ConnR associated-types sprint that already landed on `main`) instead of `plan-2026-05-10-03.md` (this sprint). The P1.A trait-claim audit and P1.B standard-review findings are independent of that misread and still apply to the Plan 26 diff. Reviewer-cited "follow-up #1 (plan numbering)" is the symptom of that misread, not a real artifact.

---

# Review: `sprint/core-split` — 2 commits ahead of `origin/main`

## P1.A — Trait-Claim Audit

The diff is dominated by the associated-types reshape of `ConnL`/`ConnR` and the introduction of `src/core/` as a new module housing moved std-int and float Conns.

### Item 1: `ConnL` / `ConnR` trait definition (`src/conn.rs` lines 480–530)

**Contract.** `ConnL` declares `type A: Copy; type B: Copy; fn conn_l(&self) -> Conn<Self::A, Self::B, L>;`. The default methods `ceil` and `upper` dispatch through `conn_l()`. This is a behavior-preserving reshape — no law is added or weakened; only the representation of `(A, B)` moves from type parameters to associated types.

**Implementation.** The blanket impls `impl<A: Copy, B: Copy> ConnL for Conn<A, B, L>` and `impl<A: Copy, B: Copy> ConnR for Conn<A, B, R>` delegate `conn_l()` / `conn_r()` to `*self`. The `ConnK` super-trait bound `ConnR<A = <Self as ConnL>::A, B = <Self as ConnL>::B>` enforces the cross-trait `(A, B)` equality at the type level.

**Consistency.** Consistent. The reshape is behavior-preserving by construction. The associated-type equality in `ConnK` is strictly more expressive than the prior form.

### Item 2: `conn_k!` macro — emitted `ConnL`/`ConnR` impls (`src/conn.rs` lines 1055–1084)

**Contract.** Emits a zero-sized struct + `ConnL` impl (with `type A = $A; type B = $B`) + `ConnR` impl (same `A`/`B`). The `conn_l` impl calls `Conn::new_l($ceil, $inner)` and `conn_r` calls `Conn::new_r($inner, $floor)`.

**Implementation.** The argument order to `new_r` is `(inner, floor)` — `inner` first. The macro emits this correctly.

**Consistency.** Consistent.

### Item 3: `nz_int_ext!` macro — adjoint triple for signed NonZero (`src/core.rs` lines 390–440)

**Contract.** Claims both `ConnL` and `ConnR` over `(iN, NonZero<iN>)` — full adjoint triple. The asymmetric `ceil(0) = +1`, `floor(0) = -1` construction is the mechanism.

**Implementation.** `conn_l` is `Conn::new_l(_ceil, _inner)` and `conn_r` is `Conn::new_r(_inner, _floor)`. The `_ceil` / `_floor` implementations use `if v == 0 { 1/-1 } else { v }`. The law battery `i008n008_galois_l` and `i008n008_galois_r` in `src/core/i008.rs` directly test both Galois laws with arbitrary `(i8, NonZeroI8)` pairs.

**Consistency.** Consistent.

### Item 4: `nz_uint_ext!` macro — left-Galois only (`src/core.rs` lines 451–478)

**Contract.** Emits a `pub const` of type `Conn<uN, NonZero<uN>>` (default `L` kind). The doc comment explicitly states "single-sided left-Galois — floor = ceil" and explains why the right-Galois law fails at `(NonZero(1), 0)`.

**Implementation.** `Conn::new_l(ceil, inner)` where `ceil(0) = 1`. No `ConnR` impl is emitted. The type matches the one-sided claim.

**Consistency.** Consistent.

### Item 5: `iso!` macro and all call sites (`src/conn.rs` lines 1104–1122; invocations in `core/i008.rs`, `core/u008.rs`, `core/i016.rs`, etc.)

**Contract.** `iso!` delegates to `conn_k!` with `ceil = floor = forward`. Claims both `ConnL` and `ConnR`, meaning both Galois laws hold; the bijection implies `roundtrip_ceil` and `roundtrip_floor` both pass on the full domain.

**Implementation.** All `iso!` invocations in `src/core/` are for byte-encoding Conns (`I008BE01`, `I008LE01`, `U008BE01`, `U008LE01`, etc.) where `forward` is a total bijection (sign-bit XOR or direct copy) and `back` inverts it exactly. No relaxation suffix is present on any associated test.

**Consistency.** Consistent.

### Item 6: Float `conn_k!` markers — `F064F032`, `F032F016`, `F064F016` (`src/core/f064.rs`, `src/core/f032.rs`, `src/core/f016.rs`)

**Contract.** `conn_k!` claims both `ConnL` and `ConnR`. For float-to-float narrowing Conns the Galois laws hold on the N5 lattice (ExtendedFloat ordering) where `NaN` is isolated (incomparable with finites, comparable with itself). The `law_battery!` for `F064F032` uses `subset: numeric_only` — this is the correct, pre-existing subset for this Conn, and the battery is not newly weakened in this diff.

**Implementation.** `f064f032_ceil` and `f064f032_floor` pass through `Bot`/`Top` and delegate to ULP walk helpers for finite values. NaN passes through as `Extend(NaN)` — under N5, `Extend(NaN)` is its own fiber and the Galois law holds reflexively.

**Consistency.** Consistent.

### Item 7: `BOOLBE01` / `BOOLLE01` — `conn_l!` one-sided (`src/core/bool.rs`)

**Contract.** Shipped via `conn_l!` — explicitly one-sided `Conn<bool, [u8;1]>` / `Conn<bool, LE<1>>`. The doc comment is explicit: "not a full iso". No `ConnR` or `ConnK` claim. Test `bool_le_kernel_l_for_noncanonical_true_bytes` explicitly verifies that `roundtrip_ceil` fails for bytes `> 1`, confirming the one-sided declaration is accurate.

**Consistency.** Consistent.

### Item 8: `U032CHAR` — `conn_l!` one-sided (`src/core/char.rs`)

**Contract.** `conn_l!` — `Conn<Extended<u32>, Extended<char>>`. Left-Galois claim only: `ceil` jumps over the surrogate gap, so it is not order-reflecting into char. Law battery uses `subset: l_only`.

**Implementation.** `ceil_u32_char` maps the surrogate range `[0xD800, 0xDFFF]` to `'\u{E000}'` and `> 0x10FFFF` to `PosInf`. `inner_char_u32` is the total lossless `c as u32` cast. These are consistent with a left-Galois claim only.

**Consistency.** Consistent.

### Item 9: Helper function signatures after associated-type reshape (`src/conn.rs` lines 612–931)

**Contract.** All helper fns (`interval`, `truncate`, `truncate1/2`, `round`, `round1/2`, `median`) bind via `T: ConnL<A = A, B = B> + ConnR<A = A, B = B>` rather than the unavailable `T: ConnK<A = A, B = B>`. (Pre-existing in `main`; unchanged by this sprint.)

**Consistency.** Consistent.

**Overall P1.A verdict:** No trait-claim mismatches found. Every `iso!` invocation is a true bijection, every `conn_k!` invocation has both Galois laws covered by tests, every one-sided claim uses `conn_l!` or `conn_r!` with a matching law battery.

---

## P1.B — Standard Review

### Commit Hygiene

Two commits. Commit messages and subject line format match the `feat:` / `doc:` convention from CLAUDE.md. Both commits land the repo in a buildable state (the move is mechanical and the moved code was already tested). No merge commits. Clean.

### Code Quality

No `unsafe` code. `#![forbid(unsafe_code)]` at `src/lib.rs` line 186 is present.

The `::core::num::NonZero*` rooted import discipline is followed consistently throughout all `src/core/*.rs` files. No bare `use core::` appears inside the new `src/core/` module, which is the correct way to avoid the `crate::core` shadow introduced by `pub mod core;` at `src/lib.rs` line 190.

The `src/hifi/calendar.rs` and `src/kani_proofs/hifi_calendar.rs` files use unrooted `use core::num::NonZeroU8;`. These files are not inside `src/core/`, so `core` there refers to `::core` (the standard library) without ambiguity — no issue.

`pub use core::LE;` at `src/lib.rs` line 202 re-exports `crate::core::LE` at the crate root. The name `LE` is unambiguous since `::core` does not export anything named `LE`. Fine.

### Test Coverage

**Property tests fully preserved.** Every `law_battery!` invocation and hand-rolled `proptest!` block from before the sprint is present in the post-sprint files. The cross-module test imports in `src/core/i008.rs` (e.g., `crate::core::{i016::I016I008, u008::U008I008, ...}`) resolve to items that exist in the respective sibling modules — verified by grep.

The `f016` module (`src/core/f016.rs`) is gated on `#[cfg(feature = "f16")]`, and all `f16` code in `f016.rs` is similarly gated. Default builds skip it. The `f016` tests in `src/core/f016.rs` are only reachable under the `f16` feature (nightly), so `cargo test` on stable will not compile or run them. This is pre-existing architecture, not a new gap.

No `#[ignore]` introduced. No test weakening detected.

### Risks

No TODOs or stubs. No new dependencies. No security surface changed.

The plan's locked decision about `ExtendedFloat<T>` is resolved correctly: `ExtendedFloat` remains in `src/float.rs`, not in `src/core.rs`. There is no orphan `ExtendedFloat` definition in `src/core.rs`. `src/float.rs` continues to host the type and all ULP/walk infrastructure. The comment at the top of `src/float.rs` ("Per-IEEE-width Conn modules moved to `crate::core::{f016,f032,f064}` in Plan 26") correctly documents the split point.

---

## P2.A — Test-Exception Escalation

No "weaker predicate", "exclude", or relaxation language in the plan's Verification table. All properties in the Verification table are claimed to pass unchanged. No test-exception escalation items.

## P2.B — Plan Conformance

T1 (worktree + branch): done.
T2 (scaffold `src/core.rs` + 15 stub submodules + 9 portable macros + `LE<N>`): done.
T3 (move §1+§3 to `core/{i008..u128}.rs`): done; `fixed/X.rs` stripped to §2/§4/float-bridge.
T4 (`BOOLBE01`/`BOOLLE01` to `core/bool.rs`): done.
T5 (move per-IEEE-width float Conns to `core/{f016,f032,f064}.rs`): done; `src/float/` deleted; `src/float.rs` retains `ExtendedFloat<T>` + infrastructure.
T6 (doctest + README path updates): done.
T7 (CLAUDE.md + lib.rs rustdoc updates): done.
T8 (cargo build/test/clippy/doc green): documented in Review section.
T9 (plan + review-00096.md): both in the doc commit.

Verification table properties (all `law_battery!` blocks under moved Conns + integration test batteries) verified by the matching `cargo test` count in the Review section.

The plan's "Decision flagged for the user" about `ExtendedFloat<T>` is resolved exactly as the plan's locked default: `ExtendedFloat` stays in `src/float.rs`. Verified.

---

## Recommendations

### Must fix before push

None identified. The trait-claim audit found no mismatches, all Galois laws are covered by tests, import discipline is correct, and all T1–T9 tasks are implemented.

### Follow-up (future work)

1. **`pub use core::LE;` source readability.** The re-export at `src/lib.rs` line 202 (`pub use core::LE;`) could confuse readers into thinking it re-exports from `::core` (the standard library). Renaming to `pub use crate::core::LE;` would be unambiguous. No functional impact — rustdoc already renders the correct source module — but worth noting for future maintainers.

2. **`src/hifi/calendar.rs` and `src/kani_proofs/hifi_calendar.rs` use bare `use core::num::NonZeroU8;`.** These files are outside `src/core/` so there is no shadow issue today, but if `hifi/` ever gains a `pub mod core;` sub-declaration, the bare form would become ambiguous. Pre-emptively rooting to `::core::num::NonZeroU8` would be consistent with the discipline applied in `src/core/`.
