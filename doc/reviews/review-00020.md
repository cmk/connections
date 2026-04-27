# MR !20 — Unsigned binary-fixed Conns + flip `fmt` to blocking

## Summary

- Adds five new modules — `conn::fixed::u08` / `u16` / `u32` /
  `u64` / `u128` — mirroring the signed binary-fixed ladder over
  `fixed::FixedU<width><Frac>`. Frac-level sets extend each
  signed counterpart with the canonical Q1.N formats: U7 (Q1.7
  MIDI velocity) in u08; U14 (Q2.14 14-bit MIDI) and U15 (Q1.15
  audio amplitude) in u16; U31 / U63 / U127 normalised
  amplitudes in u32 / u64 / u128. 119 new `pub const` Conns
  total (28 + 28 + 21 + 21 + 21), all property-tested with the
  full Galois battery (galois_l/r, monotone_l/r, closure_l/r,
  kernel_l/r, idempotent), plus per-module spot tests covering
  Q1.N round-trips, on-grid alignment, the SHIFT-at-max
  degenerate endpoint, and `FINE_MAX` boundary fixups. The u128
  module follows the i128 precedent (`checked_mul` + saturate,
  `checked_shl` for the SHIFT=128 endpoint) since stable Rust has
  no native u256 to widen through.
- Prefaces the sprint with a CI-hardening commit pair: a
  whole-tree `cargo fmt --all` to clean inherited drift, then a
  `.gitlab-ci.yml` change dropping `allow_failure: true` from the
  `fmt` job. With main provably fmt-clean (post-MR !14's
  rustfmt-skip pin and post-MR !18's forward-port), advisory
  formatting is now a footgun; making `fmt` blocking matches the
  hard-gate posture of `clippy`, `test`, and `deny`.
- Updates `src/lib.rs` (drops the "(unsigned, deferred)"
  parenthetical, adds three example bullets pointing at the
  canonical Q1.N pairs) and `doc/design.md` (expands the
  `conn/fixed/` file-tree to enumerate every submodule).
- The 1071 Galois-battery proptests for these modules live as
  five integration-test binaries under `tests/conn_fixed_u<width>_galois.rs`
  (one per backing width). Hosting them outside the lib test
  binary keeps each rustc invocation under CI's container memory
  budget; spot tests stay collocated with the source in
  `src/conn/fixed/u<width>.rs`.

## Test plan

- [ ] `cargo test --workspace` — **2823 tests** pass (1726 lib +
      1071 integration across the five `conn_fixed_u<width>_galois`
      binaries + 26 doctests), 0 failed, 0 ignored.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean (now blocking in CI).
- [ ] `cargo doc --no-deps` — clean (modulo the pre-existing
      unrelated `arb` warning in `property/mod.rs`).

## Local review (2026-04-26)

**Branch:** sprint/unsigned-binary-fixed
**Commits:** 9 (origin/main..sprint/unsigned-binary-fixed)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Nine commits, all with correct conventional prefixes (`style:`, `ci:`, `task:`, `doc:`). The two-commit T0a/T0b split (fmt clean then gate flip) is the right order — a working tree that already passes the new gate. The `task:` commits each ship one module with its full test suite; every intermediate state is buildable. No squash opportunities or hygiene problems.

### Code Quality

**`#![forbid(unsafe_code)]` posture:** Inherited from `src/lib.rs:150`. The new files add no `unsafe` blocks. Clean.

**Boundary-fixup correctness — the critical question for this sprint:** The unsigned `floor` drops the signed `FINE_MIN` guard and retains only `floor(FINE_MAX) = Coarse::MAX`. This is exactly right. The Galois contract requires `inner(b) ≤ a ⟺ b ≤ floor(a)`. At `a = FINE_MAX`, `inner` saturates at `FINE_MAX` for every coarse value (since multiplication overflows), so `inner(b) ≤ FINE_MAX` holds for all `b`. The floor must therefore return the maximum coarse representable, which is `from_bits(T::MAX)`. Without the fixup, `floor(255)` for `U004U000` (RATIO=16) returns 15, but `inner(16) = 255 ≤ 255` while `16 > 15` — a Galois violation. With the fixup it returns 255. The plateau is exactly one point (`FINE_MAX`); no wider saturation plateau requires additional fixups.

**Widening arithmetic bounds:** Verified for all modules.
- u08: max product = 255 × 256 = 65,280 < u16::MAX. Safe.
- u16: max product = 65,535 × 65,536 = 4,294,836,225 < u32::MAX. Safe.
- u32: max product < 2^64. Safe. u64: max product < 2^128. Safe.
- u128 uses `checked_mul` + saturate; no widening type needed.

**Ceiling overflow:** `ceil` adds at most 1 to the quotient. The worst case is SHIFT=1, where `(T::MAX / 2) + 1 = T::MAX/2 + 1`, which is strictly less than `T::MAX` for all widths. No cast truncation possible.

**u128 SHIFT=128 degenerate case:** `1_u128.checked_shl(128)` correctly returns `None`. The `None` branches handle `ceil`, `inner`, and `floor` correctly: `ceil(0)=0`, `ceil(x>0)=1`; `inner(0)=0`, `inner(x>0)=MAX`; `floor(x<MAX)=0`, `floor(MAX)=MAX` (via the FINE_MAX fixup). The Galois identity holds at every case boundary — manually confirmed.

**u128 type alias asymmetry:** The `u128` module ships no `pub type U<frac>` aliases because `U127` and `U128` collide with the typenum imports of the same name. This is documented at `src/conn/fixed/u128.rs:3–9` and in plan D3. Downstream callers spell `FixedU128<typenum::U127>` directly. The asymmetry is safe; there is no code that assumes all modules expose type aliases.

**`fmt` blocking flip:** `allow_failure: true` removed from the `fmt` CI job only. The `claude-review` job correctly retains its `allow_failure: true` (it's the AI advisory reviewer — blocking on it would be a footgun in the other direction). The CI change is precise.

**`#[rustfmt::skip]` pin:** The pin in `src/conn/uint.rs` and `src/conn/int.rs` remains in place. The new unsigned modules have no macro tables requiring it — the invocations are single-line and format naturally. No regression here.

**Dead code / clippy:** No `TODO`s, no `#[ignore]`d tests, no unreachable arms. The constant block `FINE_MIN` from the signed module is absent, as expected.

### Test Coverage

**Full Galois battery:** All nine properties (`galois_l/r`, `monotone_l/r`, `closure_l/r`, `kernel_l/r`, `idempotent`) are present for every conn in every module, via `props_for_pair!`. The u128 module caps cases at 64 (same as i128; the comment cites the same precedent). All other modules use the default case count.

**Spot test gap — plan vs implementation:** The Verification table specifies `spot_q08_q07_at_max` asserting that Q1.7 max value 127 "ceils/floors correctly". The actual test `spot_q17_max_velocity_to_q08` only asserts `inner(127) = 254`. It does not assert `ceil(254) = 127` or `floor(254) = 127` from the Q0.8 side, nor `ceil(127)` or `floor(127)` from the Q1.7 side. The plan's ceil/floor verification at max velocity is absent. This is not a correctness bug — proptest covers these paths — but it is a deviation from the plan's specified spot check, and the named degenerate behavior (Q1.7 max ≠ u8::MAX, so it does not hit the FINE_MAX fixup) is worth explicitly asserting.

**Degenerate endpoint tests:** Present and correct in all modules (`spot_u008u000_degenerate`, `spot_u016u000_degenerate`, `spot_u032u000_degenerate`, `spot_u064u000_degenerate`, `degenerate_max_shift` in u128). The u128 `degenerate_max_shift` test is the most thorough, covering `inner`, `ceil`, and `floor` at all boundary values for the SHIFT=128 case.

**Boundary fixup coverage:** `spot_boundary_fixups` is present in all five modules, exercising `floor(FINE_MAX) = Coarse::MAX`.

**Q1.N round-trip tests:** `spot_q31_to_q32`, `spot_q63_to_q64`, `spot_q127_to_q128`, and `spot_q15_audio_to_q16` all assert `inner` followed by `ceil` and `floor` agree and recover the original — the definitive on-grid round-trip test. These are correct.

**Missing edge case:** No spot test explicitly exercises `ceil` at the boundary where `q+1` would equal the coarse maximum — e.g., `U001U000.ceil(254)` where the result is 127 (=coarse MAX for a 7-bit field). Proptest will catch any violation here, but an explicit spot test would document the design intent.

### Plan Conformance

| Task | Status |
|------|--------|
| T0a `style: cargo fmt --all` | Done — commit `a9f7534` |
| T0b `ci: Flip fmt to blocking` | Done — commit `25b38b2`, `allow_failure` removed from `fmt` only |
| T1 u08 (28 conns, Q1.7, proptest battery) | Done — commit `7f2cc0a` |
| T2 u16 (28 conns, U14/U15, proptest battery) | Done — commit `b5afc62` |
| T3 u32 (21 conns, U31, proptest battery) | Done — commit `c8a2761` |
| T4 u64 (21 conns, U63, proptest battery) | Done — commit `49c378e` |
| T5 u128 (21 conns, U127, checked_mul, proptest battery) | Done — commit `69b98ba` |
| T6 `doc: Update lib.rs + design.md` | Done — commit `2136784` |
| T7 Plan + review doc | Done — commit `9916ba3` |

One conformance deviation: `spot_q08_q07_at_max` (Verification table, u08 row) is not present by that name; the test `spot_q17_max_velocity_to_q08` covers `inner` only and is narrower than the plan specified.

### Risks

No TODOs, no stubs. No new crate dependencies. The modules are purely additive — no existing module is modified except `src/conn/fixed.rs` (adding `pub mod` declarations), `src/lib.rs` (doc update), and formatting-only changes to `src/conn/cast.rs` and `src/conn/time.rs`. The formatting-only changes are safe and expected from T0a.

The `pub mod u32` / `pub mod u64` / `pub mod u128` declarations in `src/conn/fixed.rs` shadow the standard library primitive names within that module's namespace. This is safe — Rust resolves `u32` as a primitive in all contexts where `use conn::fixed::u32` has not been written — but it is worth noting for future contributors importing these modules with `use`.

### Recommendations

**Must fix before push:** None. The implementation is correct, all Galois laws are tested at the property level, and the plan's structural requirements are met.

**Follow-up (future work):**

1. `src/conn/fixed/u08.rs` — Expand `spot_q17_max_velocity_to_q08` (or add a separate `spot_q08_q07_at_max`) to assert `ceil` and `floor` at velocity=127 from both sides, closing the gap with the Verification table. The behavior is correct; the documentation of intent in test form is incomplete.
2. Consider adding one explicit spot test for `ceil` at `Fine::MAX - 1` (one below the FINE_MAX fixup boundary) in any module, to document that the non-fixup path does not accidentally trigger for adjacent values.
3. If/when cross-sign `I??U??` / `U??I??` conns are added (Plan 09 Deferred), the frac levels chosen here (U31/U63/U127 on the unsigned side) have no signed counterpart — the signed modules top out at I032/I064/I128. That asymmetry will need its own plan.
