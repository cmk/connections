# MR !28 — `conn::time` v2 Phase B: float ↔ `Duration` bridges

## Summary

Adds the float-seconds ↔ `Duration` bridges deferred from Phase A
(MR !23): `F064DURN` and `F032DURN`, both hosted in
`conn::time::duration` per the **specific > general** placement
rule. Walks step on the discrete `Duration` rung (1ns ULPs); the
correction loops are generated from the `def_walk_helpers!` macro
that landed with the float-half sprint (MR !22).

The Galois battery for both bridges runs at `cases: 64` (down from
the 128 used in pure-integer Conns) because `f64_idempotent` /
`f32_idempotent` exercise the walks twice per case. The full
crate's lib suite now sits at 1809 + 28 = 1837 tests.

Plan + design rationale: [`plan-2026-04-27-06.md`][plan].

[plan]: ../plans/plan-2026-04-27-06.md

## Highlights

- **Two new Conn consts** (`conn::time::duration`):
  - `F064DURN: Conn<F064, Extended<Duration>>`
  - `F032DURN: Conn<F032, Extended<Duration>>`
- **Walk infrastructure** — `shift_duration(n_ns: i32, d) -> d`
  saturating ±n-ns shift on `whole_nanoseconds() (i128)`; thin
  `duration_to_f64` / `duration_to_f32` widen helpers; two
  `def_walk_helpers!` invocations. Reused across both bridges.
- **Saturation arms derived from N5**:
  `ceil(NaN) = PosInf`, `floor(NaN) = NegInf`;
  `ceil(+∞) = PosInf`, `floor(+∞) = Finite(Duration::MAX)`
  (and symmetric for `-∞`). The asymmetry between ceil/floor at
  `Extend(±∞)` is the same shape as DATEJDAY / TIMENANO /
  DURNSECS — `Top` is strictly above `Extend(f64::INFINITY)` so
  Galois forces it.
- **Plateau-aware proptest strategies** — `arb_duration_bounded_f64`
  (±10⁹ s) and `arb_duration_bounded_f32` (±10 s), plus matching
  `arb_extended_*` wrappers and a tightened `arb_f32_bounded`
  (`|x| ≤ 10`). Beyond those magnitudes the 1ns walk hits a
  multi-million-step plateau that hangs the law battery.
- **README** — Quick-tour example using `F064DURN` (0.5s exact
  round-trip + NaN saturation), updated family-table row, layout
  tree note.

## Verification

```
cargo build --offline                              # green
cargo test  --lib --offline                        # 1837 passed; 0 failed (~6 min)
cargo test  --doc --offline                        # 31 passed; 3 ignored
cargo fmt   --all -- --check                       # clean
cargo clippy --offline --all-targets --no-deps -- -D warnings  # clean
```

The two `*_idempotent` tests dominate the lib runtime (each
~2 minutes of walk iteration). All other Galois laws run in
seconds.

## Decisions worth flagging

- **Specific > general placement.** Even though `F064DURN` /
  `F032DURN` look like float-family Conns, the `Duration` side is
  the specific time-domain endpoint, so the consts live in
  `conn::time::duration`, not `conn::float::*`. Captured in the
  `feedback_conn_placement_specific_over_general.md` memory for
  future Conns where the rule needs to override a same-tier
  right-wins tiebreaker.
- **Tightened `arb_f32_bounded`** (`|x| ≤ 10`, was `|x| ≤ 1e9`).
  No other Conn currently consumes `arb_f32_bounded` —
  `extended_float_f32` (also new this MR) is its only call site.
  Future F32-source Conns into bounded integer rungs may want a
  wider strategy; revisit if/when that lands.
- **`f32_one_second_brackets_plateau`.** The natural-feeling
  assertion `F032DURN.ceil(1.0_f32) == Finite(Duration::seconds(1))`
  is *false* under proper Galois: `ceil` returns the **bottom** of
  the f32 plateau (~30 ns *below* `Duration::seconds(1)`). The
  spot test asserts the actual contract — both `ceil` and `floor`
  bracket `Duration::seconds(1)`, both round-trip to `1.0_f32`
  via `inner`.

## Deferred

- **`F016DURN` / `B016DURN` (half-precision bridges)**. f16 ULP at
  magnitude 1 s is ~10⁻³ s = 10⁶ ns of plateau per call; bf16 is
  ~8× wider. Linear 1ns walks are infeasible at those plateau
  widths under any practical proptest budget. Plan: revisit when
  the walk-helpers macro grows a binary-search shift variant.
- **`Weekday` / `Month` / `UtcOffset` enum tags** still blocked on
  the upstream `Eq + PartialOrd` story (Phase A documented the
  same gap; nothing changes here).

## Files changed

- `src/conn/time/duration.rs` — `+372`/`-3` (helpers, two consts,
  `float_durn_tests` mod).
- `src/conn/time.rs` — re-export `F032DURN` / `F064DURN`.
- `src/property/arb.rs` — six new generators
  (`arb_f32_bounded`, `extended_float_f32`,
  `arb_duration_bounded_f64`, `arb_duration_bounded_f32`,
  `arb_extended_duration_bounded_f64`,
  `arb_extended_duration_bounded_f32`); also updated rustdoc on
  the existing `arb_f32_bounded` slot.
- `README.md` — Quick-tour example, family-table row, layout tree.
- `doc/plans/plan-2026-04-27-06.md` — this MR's design rationale.
- `doc/reviews/review-00028.md` — this file.
