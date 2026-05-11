# MR !44 — Plan 27: time/ Conns to one-sided so floor_le_ceil holds

## Summary

- Convert six `time/` Conns (`TIMENANO`, `TIMESECS`, `DATEJDAY`,
  `OFDTNANO`, `OFDTSECS`, `PDTMDATE`) from full-triple `Conn::new` to
  one-sided `Conn::new_left(ceil, inner)`. Each had a non-order-
  reflecting `inner` at synthetic extremes that broke
  `conn_floor_le_ceil`; `new_left` wires `floor = ceil` structurally
  so the law holds by construction.
- Behavioral deltas on `floor()` for the three sub-unit projections
  (`TIMESECS`, `OFDTSECS`, `PDTMDATE`): previously truncated, now
  rounds up to match `ceil` (the round-up semantics is preserved as
  the canonical answer). Synthetic-end values (`floor(NegInf)` /
  `floor(PosInf)`) similarly collapse onto `ceil`'s saturation values.
- Property batteries lose `_r` family tests on the converted Conns
  (`galois_r`, `closure_r`, `kernel_r`, `monotone_r`, `roundtrip_floor`)
  since they don't hold under `new_left`; `_l` family + `floor_le_ceil`
  + `idempotent` + `roundtrip_ceil` remain.

## Test plan

- [ ] `cargo test --workspace` passes (1265 lib + 45 integration + 55
  doctests, all green locally).
- [ ] `cargo clippy --all-targets -- -D warnings` clean.
- [ ] `cargo fmt --all -- --check` clean.
- [ ] `floor_le_ceil` proptests pass for all 6 converted Conns.
- [ ] Spot-check `floor` and `ceil` agree at synthetic extremes for
  each Conn (covered by updated `saturation_extremes` tests).

## Local review (2026-04-28)

**Branch:** sprint/plan-27-floor-le-ceil-audit
**Commits:** 1 (origin/main..sprint/plan-27-floor-le-ceil-audit)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Single commit `4c454f8`. Subject is 68 characters, conventional `fix:`, atomic (all six conversions plus plan + review doc in one commit). No compound-command worktree issue — commit runs from project root.

---

### Code Quality

**Stale prose in `src/time.rs` module-level doc table — must fix.**

`src/time.rs` line 64:
```
//! | [`TIMESECS`] | `Conn<Extended<Time>, i64>` | whole seconds since midnight; sub-second `ceil` and `floor` differ. |
```
Under `new_left`, `floor = ceil` structurally — they no longer differ on any input. This description is now false. It will mislead users reading the module overview. Should be updated to something like "sub-second inputs round up; `floor = ceil` under `new_left`."

The verification blurb at `src/time.rs` lines 81–87 says "the full Galois law battery from `crate::prop::conn`". That's now imprecise for the six converted Conns (only the `_l` half runs). The statement is generic enough that it isn't a correctness bug, but it will confuse the next reader who notices the `_r` tests are missing. Follow-up.

All six `Conn::new(ceil, inner, floor)` bodies are gone. No orphan `floor` helper fns remain. All six now call `Conn::new_left(ceil, inner)`. All `/// floor = ceil` structural notes in the per-Conn rustdoc are accurate.

The three sub-unit Conns (`TIMESECS`, `OFDTSECS`, `PDTMDATE`) each carry an explicit behavioral note that `floor` now returns the rounded-up answer. The workaround formula in `TIMESECS`'s doc (`ceil(t) - (t.nanosecond() != 0) as i64`) is correct Rust (`bool as i64` is 0/1).

No leftover prose claiming a "ceil rounds up, floor truncates" duality was found in the four modified files.

Saturation spot-check assertions look correct: TIMENANO `floor(NegInf) = i64::MIN`, `floor(PosInf) = NS_MAX + 1`; TIMESECS `floor(NegInf) = i64::MIN`, `floor(PosInf) = 86_400`; DATEJDAY `floor(NegInf) = i32::MIN`, `floor(PosInf) = MAX_JD + 1`; OFDTNANO `floor(NegInf) = i128::MIN`, `floor(PosInf) = max_ns + 1`; PDTMDATE `floor(MIN) = NegInf`, `floor(MAX) = PosInf`. All match `floor = ceil` under `new_left`.

**OFDTSECS is missing a `saturation_extremes` spot-check** for `floor(NegInf)` and `floor(PosInf)`. OFDTNANO has `ofdtnano_saturation_extremes` asserting both; OFDTSECS has no parallel test. The `floor_le_ceil` proptest will catch violations structurally, but the explicit spot-check is present for every other converted Conn and absent here. Minor inconsistency, follow-up.

---

### Test Coverage

**TIMENANO** — `galois_l` ✓, `closure_l` ✓, `kernel_l` ✓, `monotone_l` ✓, `floor_le_ceil` ✓, `idempotent` ✓, `roundtrip_ceil` ✓. `galois_r`, `closure_r`, `kernel_r`, `monotone_r`, `roundtrip_floor` all removed. ✓

**TIMESECS** — same five required properties present. `_r` family and `roundtrip_floor` removed. `ulp_bound_finite` also removed (was finite-only; no longer meaningful without a distinct floor; this is correct). Subsec spot-check in `subsec_rounds_up` asserts both `ceil = 43_201` and `floor = 43_201`. `end_of_day` drops the floor assertion rather than updating it to 86_400 — the behavioral change (floor was 86_399, now 86_400) is not directly spotchecked at this input. Covered indirectly by `subsec_rounds_up`, but the omission is worth noting. Follow-up.

**DATEJDAY** — five required properties present. `_r` family and `roundtrip_floor` removed. ✓

**OFDTNANO** — five required properties present (prefixed `ofdtnano_`). `_r` family and `roundtrip_floor` removed. ✓

**OFDTSECS** — five required properties present (prefixed `ofdtsecs_`). `_r` family and `roundtrip_floor` removed. `ulp_bound` comment block correctly removed. No `saturation_extremes` spot-check (noted above). `ofdtsecs_negative_subsec` asserts `ceil = 0` for `epoch - 500ms`: `unix_timestamp()` of that instant is −1, `nanosecond()` is 500_000_000 ≠ 0, so `ceil = −1 + 1 = 0`. Value is correct.

**PDTMDATE** — five required properties present. `_r` family and `roundtrip_floor` removed. `ulp_bound` removed. `roundtrip_ceil` correctly filters `Date::MIN` with a documented reason. Spot-checks cover `floor = NegInf` at `PrimitiveDateTime::MIN` and `floor = next_day` at the sub-day input. ✓

**Cross-Conn inconsistency** — TIMESECS `subsec_rounds_up` asserts `floor = 43_201`; the parallel OFDTSECS `ofdtsecs_subsec_rounds_up` asserts only `ceil = 1`, with no floor assertion. Under `new_left` floor and ceil are the same value, so neither is wrong, but sibling Conns handling the identical scenario have different assertion density. Cosmetic; follow-up.

---

### Plan Conformance

T1 per-file walk:
- `time/clock.rs`: TIMENANO and TIMESECS converted. ✓
- `time/date.rs`: DATEJDAY converted. ✓
- `time/datetime.rs`: PDTMDATE converted. ✓
- `time/offset.rs`: OFDTNANO and OFDTSECS converted. ✓

All floor helper fns dropped in all four files. ✓

Verification table requires `galois_l`, `closure_l`, `kernel_l`, `floor_le_ceil`, `idempotent` per Conn. All five are present for all six Conns. ✓

No `#[ignore]`d properties. ✓

---

### Risks

No TODOs or stubs found in the diff.

No callers in the wider codebase use `.floor()` on the six affected Conns outside of `src/time/`. The only non-test references are in `src/time.rs` (re-exports and doc table) and `src/prop/arb.rs` (strategy comment referencing OFDTNANO by name, not calling floor). No callers will silently get the old truncating semantics.

`duration.rs` retains seven `Conn::new(ceil, inner, floor)` full-triple constructors — those are not in scope for this sprint and are untouched. ✓

---

### Recommendations

**Must fix before push**

1. **`src/time.rs` line 64** — the TIMESECS table row says "sub-second `ceil` and `floor` differ". Under `new_left` they are the same value. Update to reflect the new `floor = ceil` semantics, e.g.: `whole seconds since midnight; sub-second inputs round up (`floor = ceil` under `new_left`)`.

**Follow-up**

2. **`src/time.rs` verification prose** (lines 81–87) — "full Galois law battery" is imprecise now that six Conns run only the `_l` half. A parenthetical "(left-sided battery for `new_left` Conns; full battery for full triples)" would future-proof it.

3. **OFDTSECS missing `ofdtsecs_saturation_extremes`** — add spot-checks for `floor(NegInf) = i64::MIN` and `floor(PosInf) = max_s + 1` parallel to `ofdtnano_saturation_extremes`. Structural correctness is guaranteed, but the test gap is visible by comparison.

4. **TIMESECS `end_of_day`** — the old `floor = 86_399` assertion was removed rather than updated to `floor = 86_400`. The `subsec_rounds_up` test covers this indirectly, but adding `assert_eq!(TIMESECS.floor(...), 86_400)` directly to `end_of_day` would make the behavioral change explicit in the spot-check that most naturally documents it.
