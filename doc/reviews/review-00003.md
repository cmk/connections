# MR !3 — Naming convention + f64fix port (Extended, FloatExt)

## Summary

Two upstream tasks shipped together so downstream sees one rev bump:

### U0 — Rename sample-tier conns to the `fXYfZW` 6-character shape

The `PICO_SXX` / `SXX_SYY` names were the only non-conforming ones in
the ladder. Renames:

- `PICO_S44` → `F12S44`, `PICO_S48` → `F12S48`, …, `PICO_S192` →
  `F12S192` (6 renames).
- `S88_S44` → `S88S44`, …, `S192_S176` → `S192S176` (15 renames; drop
  the `_`).

Pure identifier-level rename; no behaviour change. All existing
proptests + spot checks pass unchanged.

### U1 — Port `f64fix` as lawful `Conn<FloatExt<f64>, Extended<Rung>>`

Ports the Haskell `Data.Connection.Fixed.f64fix` to Rust as one `Conn`
constant per decimal rung: `F64F00` (Uni), `F64F01` (Deci), `F64F02`
(Centi), `F64F03` (Milli), `F64F06` (Micro), `F64F09` (Nano), `F64F12`
(Pico).

The lawful shape requires both sides to be totally ordered modulo the
N5-lattice structure of NaN handling:

- **Source:** new `FloatExt<T>` (`float_ext.rs`) adds synthetic `Bot`
  / `Top` bounds outside the IEEE range and patches
  `Finite(NaN).partial_cmp(Finite(NaN))` to `Some(Equal)`. `Bot ≤ x ≤
  Top` for every `x`; NaN stays incomparable with every other
  `Finite(_)`. Implements `PartialOrd` for `FloatExt<f32>` and
  `FloatExt<f64>`.
- **Target:** new `Extended<T>` (`extended.rs`) is a pure
  range-extension wrapper (`NegInf / Finite(T) / PosInf`). Used
  whenever the target cannot represent the source's full range —
  here, i64-bounded Rungs against an f64 source.

The saturation table (see the macro doc comment in `fixed.rs`) falls
out of the adjoint law:

| source `x`           | `ceil`                | `floor`              |
|----------------------|-----------------------|----------------------|
| `Bot`                | `NegInf`              | `NegInf`             |
| `Top`                | `PosInf`              | `PosInf`             |
| `Finite(NaN)`        | `PosInf`              | `NegInf`             |
| `Finite(-∞)`         | `Finite(Rung::MIN)`   | `NegInf`             |
| `Finite(+∞)`         | `PosInf`              | `Finite(Rung::MAX)`  |
| finite ≪ inner(MIN)  | `Finite(Rung::MIN)`   | `NegInf`             |
| finite ≫ inner(MAX)  | `PosInf`              | `Finite(Rung::MAX)`  |
| finite in range      | round-up rung         | round-down rung      |

Proptests verify the full Galois-law battery (adjointness, closure,
kernel, monotonicity) on the full `FloatExt<f64>` × `Extended<Rung>`
domain for F64F06 and F64F12 — the two structurally distinct PREC
regimes. F64F00 (identity-like) gets an expanded saturation
spot-check. Proptest config tuned (`cases: 64`, `max_shrink_iters:
512`, bounded float generator `-1e9..1e9`) to keep shrink time
bounded.

### U2 — Crate-level naming-convention doc

`src/lib.rs` gains a module-level doc table naming every tier code and
linking examples so future additions conform.

## What's deferred

Documented in `doc/plans/plan-2026-04-24-01.md §Deferred`:

- **`F32Fxx`** — narrowing `inner: i64 → f32` creates collapse classes
  up to ~120 000 Rung wide at Pico scale, forcing the correction loop
  into an O(plateau) walk. f32 callers widen losslessly at the
  boundary (`F64F06.ceil(FloatExt::Finite(arg_f32 as f64))`) until a
  binary-search correction unlocks the native shape.
- **`RATFxx`** — no current downstream consumer.
- **`Conn::then`** — still blocked on a closure-capturing `Conn`
  variant design.
- **f64 plateau at large `c`** — same mechanism as f32, different
  scale (~4500 rungs wide for F64F12 near `c = i64::MAX`). Real
  callers saturate to ±Inf before hitting it, but it's the same fix
  when it comes.

## Test plan

- [x] `cargo build` — clean.
- [x] `cargo test` — 377 passed, 0 failed, 0.49 s.
- [x] `cargo clippy --all-targets` — clean.
- [x] Local code-reviewer agent: zero must-fix items; 5 follow-ups all
  applied in a final `fix:` commit.

## Local review (2026-04-23)

**Branch:** `feat/naming-convention-and-float-conns`
**Commits:** 4 (origin/main..HEAD)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Four commits: `plan:`, `debt:`, `feat:`, `doc:`. Subjects are
present-tense imperative, all under 72 characters. The plan commit
lands first. Prefixes match the project's accepted set. No merge
commits visible. Clean.

### Code Quality

**Issue 1: `inner_as_f64` correctly handles f64, but the comment
describing f32 usage is misleading (confidence 80).**
`src/fixed.rs:177` — when `$float = f64`, `((c as f64) / PREC_F) as
f64 as f64` is a no-op round-trip. The comment reads as though f32
narrowing is a live feature of the current code, but F32Fxx is
deferred. A future contributor instantiating the macro for f32 would
hit the plateau-collapse regime the Deferred section warns about.
*Addressed in `fix:` commit.*

**Issue 2: `i64::MAX as f64` silently promotes to 2^63
(confidence 82).** `src/fixed.rs:198` — the guard `scaled > i64::MAX
as f64` is really `scaled > 2^63`, not `> 2^63 − 1`. Values in
`(2^63 − 1, 2^63]` fall through to the correction path, where the
saturating cast yields `i64::MAX`. Correct behaviour, but the guard
is subtly off-by-one relative to what its comment implied.
*Addressed in `fix:` commit.*

**Issue 3: `ceil` correction-loop `i64::MIN + 1` offset is correct but
non-obvious (confidence 80).** `src/fixed.rs:211` — the loop won't
reduce below `i64::MIN + 1`. Inputs that would legitimately round to
`i64::MIN` are caught by the earlier saturation guard, so the +1 is
correct. *Addressed in `fix:` commit.*

**Issue 4: `FloatExt::PartialOrd` arm ordering is correct but fragile
(confidence 80).** `src/float_ext.rs:52` — overlapping wildcard arms
(`(_, Top)`, `(Top, _)`) require first-match semantics. No current
bug; future-edit risk is bounded by the unit tests.

### Test Coverage

**Gap 1: only F64F06 and F64F12 get the Galois-law proptest battery
(confidence 82).** `src/fixed.rs:693` — F64F00/01/02/03/09 have only
spot checks. F64F00 especially is qualitatively different (PREC=1,
identity-like). *Addressed by adding `f64f00_saturation` spot checks
in the `fix:` commit.*

**Gap 2: `arb_f64_full` doesn't bias toward saturation-boundary
magnitudes (confidence 81).** `src/fixed.rs:499` — `f64::MAX /
MIN` are listed as boundary cases but not weighted, and the
saturation thresholds for F64F12 sit at `xf ≈ 9.22×10⁶` — inside the
`-1e9..1e9` uniform range, but uniform sampling doesn't concentrate
there. Acceptable gap given the spot checks and the `arb_extended_*`
coverage.

### Plan Conformance

The plan's original scope (F32Fxx + SAT variants + RATFxx ≈ 210
tests) shipped trimmed to F64Fxx + 14 proptests. All three deviations
are documented in the plan's Review § and Deferred §.

### Risks

**Risk 1: f64 plateau at large `c` (confidence 80, performance only).**
For F64F12 near `c = i64::MAX`, ~4500 consecutive rungs collapse onto
the same f64 — correction loop degrades to O(plateau) but still
terminates with the lawful answer. Real callers saturate before
reaching this regime. *Now documented in §Deferred.*

### Recommendations

- **Must fix before push:** None.
- **Follow-up:** Five items, all applied in the final `fix:` commit:
  inner_as_f64 comment tightened, `i64::MAX` / `i64::MIN as f64`
  asymmetry documented, `i64::MIN + 1` offset explained, `f64f00`
  saturation spot checks added, §Deferred updated with the f64
  large-`c` plateau.
