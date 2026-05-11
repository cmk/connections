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

<!-- glab-id: 3281890856 -->
<!-- glab-discussion: 717c4032c78822bb1c2281f10d2d766986b6c449 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/float_ext.rs:57` (2026-04-24 03:08 UTC) [open]

**[must-fix]** The `PartialOrd` match arms `(_, Top)` and `(Top, _)` overlap: when `self = Top` and `other = Top`, the first matching arm is `(_, Top)` (returns `Some(Less)`) before the `(Top, Top)` reflexivity case fires — but `(Top, Top)` is handled by the first arm `(Bot, Bot) | (Top, Top)`. Wait: actually `(Bot, Bot) | (Top, Top)` is listed first, so `(Top, Top)` does fire correctly. However when `self = Top` and `other` is anything except `Bot` or `Top`, the arm `(_, Top)` fires first and returns `Some(Less)`, making `Top < Top` impossible — but that case is already handled. The real bug: the `(_, Top)` arm (line 57 in the `match`) is reached for `(Top, Finite(_))` — it returns `Some(Less)`, but `Top` should be **greater** than any `Finite`. The arm `(_, Top) => Some(Ordering::Less)` means 'anything is less than Top', which is correct for the `self` side (self < Top), but when `self = Top` and `other = Finite(_)`, the arm `(Top, _) => Some(Ordering::Greater)` comes *after* `(_, Top)`, so `(Top, Finite(x))` matches `(_, Top)` first and returns `Less` instead of `Greater`. This is a correctness bug: `FloatExt::Top < FloatExt::Finite(1.0)` would return `true`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281890870 -->
<!-- glab-discussion: 6467bb92a823a6b6bf5c0ff8d670bf8f513138c2 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/fixed.rs:247` (2026-04-24 03:08 UTC) [open]

**[must-fix]** The `floor` correction loop uses `c > i64::MIN + 1` as its lower bound (mirroring the `ceil` loop), but the comment explaining why `i64::MIN + 1` is safe in `ceil` ("next iteration reads `inner_as_f64(c - 1)`") does not apply here: the `floor` loop decrements `c` directly (`c -= 1`) and then checks `inner_as_f64(c)`, so the guard should be `c > i64::MIN`, not `c > i64::MIN + 1`. Values that legitimately floor to `i64::MIN` are not all caught by the `scaled < i64::MIN as f64` early return (since `i64::MIN as f64` is exact, values equal to that boundary fall through), meaning the floor result can be off by one at the extreme lower boundary.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281890883 -->
<!-- glab-discussion: 6427757e886e9f385dfca9963129af9674622fa9 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/extended.rs:26` (2026-04-24 03:08 UTC) [open]

**[must-fix]** The `PartialOrd` match has overlapping wildcard arms: `(_, PosInf) => Some(Less)` appears before `(PosInf, _) => Some(Greater)`. When `self = PosInf` and `other = PosInf`, the `(PosInf, PosInf)` reflexivity arm fires first (correct), but when `self = PosInf` and `other = NegInf`, the arm `(_, PosInf)` cannot match (other is NegInf, not PosInf) so `(PosInf, _)` fires — that's fine. However for `self = Finite(x)` and `other = PosInf`, `(_, PosInf)` fires returning `Less` (correct). For `self = PosInf` and `other = Finite(x)`, `(_, NegInf)` doesn't match, `(_, PosInf)` matches and returns `Some(Less)` — meaning `PosInf < Finite(x)`, which is wrong. The `(_, PosInf) => Some(Less)` arm is reached before `(PosInf, _) => Some(Greater)` for the `(PosInf, Finite(_))` case, producing an incorrect result.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281890906 -->
<!-- glab-discussion: 208e98e4b9d016a94528d7a5064499dbeb3dd998 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/fixed.rs:660` (2026-04-24 03:08 UTC) [open]

**[follow-up]** The `le` helper comment says "incomparable inputs return `false`" (correct strict ≤), but then the property `prop_monotone` only checks one direction (`if le(&a1, &a2)`), silently skipping incomparable pairs. For `FloatExt` inputs where `a1 = Finite(NaN)` and `a2 = Finite(1.0)`, neither `le(&a1, &a2)` nor `le(&a2, &a1)` holds, so the body is never exercised — the monotonicity property is vacuously true for all NaN-containing pairs, reducing coverage of the saturation logic under the generators.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281890939 -->
<!-- glab-discussion: 3e4150e382a3b0126209dc5e137893c340abd9f0 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/lib.rs:34` (2026-04-24 03:08 UTC) [open]

**[follow-up]** The naming-convention table lists `F64` as a code for `FloatExt<f64>` in the `float_ext` module, but the actual public constants (`F64F00`…`F64F12`) live in `fixed` (exported from `src/fixed.rs`), not `float_ext`. The `float_ext` module only exports the `FloatExt<T>` type itself. A downstream user following the table link to `[float_ext]` to find `F64F06` will not find it there.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281900983 -->
<!-- glab-discussion: 717c4032c78822bb1c2281f10d2d766986b6c449 -->
#### ↳ cmk (2026-04-24 03:14 UTC) [open]

False positive. The match arms are:

```rust
(Bot, Bot) | (Top, Top) => Some(Equal),
(Bot, _) => Some(Less),
(_, Bot) => Some(Greater),
(_, Top) => Some(Less),
(Top, _) => Some(Greater),
```

For `(Top, Finite(x))`: arm 4 `(_, Top)` requires `other = Top`, but `other = Finite(x)`, so no match. Arm 5 `(Top, _)` matches and returns `Greater`. Verified by running `FloatExt::<f64>::Top.partial_cmp(&FloatExt::Finite(1.0_f64))` — gives `Some(Greater)`, as expected.

<!-- glab-id: 3281901508 -->
<!-- glab-discussion: 6467bb92a823a6b6bf5c0ff8d670bf8f513138c2 -->
#### ↳ cmk (2026-04-24 03:15 UTC) [open]

False positive on the off-by-one claim. At the extreme lower boundary:

- For `xf = (i64::MIN as f64) / PREC`: `scaled = i64::MIN as f64` (exact), the early-return guard `scaled < i64::MIN as f64` is false (equal, not strictly less), so we fall through.
- `scaled.floor() as i64 = i64::MIN` (saturating cast is a no-op here).
- First loop (`while c > i64::MIN + 1 && inner(c) > xf`) does not run — the guard prevents it, and that's correct: we can't walk down past `i64::MIN`.
- Second loop (`while c < i64::MAX && inner(c+1) <= xf`) walks up through the f64-plateau that xf landed in, producing the largest `c` in the collapse class with `inner(c) ≤ xf`. That is the *correct* floor under PartialOrd — `floor` is defined as the largest such `c`, and many consecutive rungs can share an f64 value.

Changing the guard to `c > i64::MIN` would let the first loop reach `c = i64::MIN` then try `c - 1 = i64::MIN - 1` on the next iteration, which would overflow. The current guard is what prevents the overflow; there is no correctness loss because the "true floor below `i64::MIN`" case is already caught by the early-return saturation path (`scaled < i64::MIN as f64`).

<!-- glab-id: 3281901901 -->
<!-- glab-discussion: 6427757e886e9f385dfca9963129af9674622fa9 -->
#### ↳ cmk (2026-04-24 03:15 UTC) [open]

False positive. The match arms are:

```rust
(NegInf, NegInf) => Some(Equal),
(PosInf, PosInf) => Some(Equal),
(NegInf, _) => Some(Less),
(_, NegInf) => Some(Greater),
(_, PosInf) => Some(Less),
(PosInf, _) => Some(Greater),
```

For `(PosInf, Finite(x))`: arm 5 `(_, PosInf)` requires `other = PosInf`, but `other = Finite(x)`, so no match. Arm 6 `(PosInf, _)` matches and returns `Greater`. Verified by running `Extended::<Uni>::PosInf.partial_cmp(&Extended::Finite(Uni(1)))` — gives `Some(Greater)`.

The review's reading inverts Rust's pattern-match semantics — `(_, PosInf)` is "any self, other=PosInf", not "self=PosInf, any other".

<!-- glab-id: 3281902244 -->
<!-- glab-discussion: 208e98e4b9d016a94528d7a5064499dbeb3dd998 -->
#### ↳ cmk (2026-04-24 03:15 UTC) [open]

Intentional — monotonicity is a statement about comparable pairs. The property `a₁ ≤ a₂ ⟹ f(a₁) ≤ f(a₂)` imposes no obligation when `a₁` and `a₂` are incomparable, so skipping the body there is semantically correct, not a gap.

NaN behaviour is covered by `prop_adjoint_l` / `prop_adjoint_r` at NaN input — which exercise the full saturation map (NaN → PosInf for ceil, NaN → NegInf for floor) against every target `b`. That's the property that *would* break if NaN handling regressed.

<!-- glab-id: 3281902596 -->
<!-- glab-discussion: 3e4150e382a3b0126209dc5e137893c340abd9f0 -->
#### ↳ cmk (2026-04-24 03:15 UTC) [open]

Fixed — dropped the "module" column from the table (codes name *types*, which was the real contract) and added a one-line note routing readers to the right module for each `Conn` constant flavour (`F??F??` → `fixed`, `S???S???` / `F??S???` → `sample`).
