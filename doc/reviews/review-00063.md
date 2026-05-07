# MR !63 — `hifi` cargo feature + `hifi/duration.rs` (Sprint 1 of hifitime integration)

## Summary

- New optional `hifi` cargo feature pulls
  [`hifitime`](https://docs.rs/hifitime) v4.3 with
  `default-features = false` (no-std-friendly; downstream re-enables
  what it needs).
- `connections::hifi::duration` ships four Conns over
  `hifitime::Duration`: `HDURNANO` (i128 total nanoseconds, OFDTNANO
  shape), `HDURSECS` (i64 whole seconds, OFDTSECS shape),
  `F064HDUR` / `F032HDUR` (IEEE float seconds via 1 ns ULP walks,
  F064DURN / F032DURN shape).
- All four use **single-side `Extended<…>`** — no two-sided wrapping.
  Sets the precedent for the rest of the hifitime sprints (see
  `doc/plans/plan-2026-05-06-04.md` for the master integration plan).

## Test plan

- [ ] `cargo build --no-default-features` — feature genuinely optional
- [ ] `cargo build --features hifi`
- [ ] `cargo test --features hifi,testing` — all suites green
      (1212 lib + 4 hifi doctests)
- [ ] `cargo clippy --features hifi,testing --all-targets -- -D warnings`
- [ ] `RUSTDOCFLAGS=-Dwarnings cargo doc --features hifi,testing,macros
      --no-deps --document-private-items`
- [ ] Galois L laws hold over `arb_extended_hifi_duration` × `any::<i128>()`
      (and the i64 / float-bridge analogs) across all six Conns
- [ ] `HDURNANO` round-trips `arb_hifi_total_nanos_in_range` exactly

<!-- glab-id: 3322165599 -->
<!-- glab-discussion: 296fb4d0f61007aa1c74c33ba087d0269fb12813 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/duration.rs:57` (2026-05-06 23:31 UTC) [open]

**[must-fix]** The `hd_min_secs()` comment claims that `HD::MIN.to_seconds()` is exactly representable at this magnitude, but `HD::MIN` is the most-negative sentinel whose total nanoseconds ≈ −1.03 × 10²³ ns, which is about −1.03 × 10¹⁴ s. That value (≈ −1.03 × 10¹⁴) requires ~47 bits of integer part and exceeds f64's exact-integer range of 2⁵³ ≈ 9 × 10¹⁵, so the cast is actually lossless _only accidentally_ at this magnitude. More critically, `HD::MAX.to_seconds()` (used in `hd_max_secs`) has a similar issue: `HD::MAX` uses `nanoseconds == NANOSECONDS_PER_CENTURY` (non-canonical, one past the boundary), so `to_seconds()` may not return an exact integer — the `as i64` truncation could then produce a `max_s` that is off by one, making `hdursecs_inner(max_s)` return `PosInf` instead of `Finite(HD::MAX)` and breaking the `hdursecs_min_max_round_trip` property. Verify that `HD::MAX.to_seconds() as i64 * 1_000_000_000 == HD::MAX.total_nanoseconds()` holds, or compute `max_s` via integer arithmetic directly from `total_nanoseconds()`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322165613 -->
<!-- glab-discussion: d5da7b5a8bcc4f2538a034ae77c5e67eae6f6f88 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/duration.rs:254` (2026-05-06 23:31 UTC) [open]

**[must-fix]** The plan's Verification table lists `hdursecs_roundtrip_ceil` as a must-pass property (the `HDURNANO` analog), but no such proptest exists in this diff — the Review section acknowledges this gap and defers it to MR `!64`. The repo convention states "Each commit must leave the repo in a state where `cargo test` passes" and properties in the Verification table "must pass for the sprint to ship"; shipping MR `!63` with a documented missing must-pass property violates both the sprint contract and the convention. The missing `arb_hifi_total_secs_in_range` strategy and `hdursecs_roundtrip_ceil` proptest should be added before this MR merges rather than deferred.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322165623 -->
<!-- glab-discussion: 32c38a451ee654556f44df4246d95f6119e83776 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/prop/arb.rs:1071` (2026-05-06 23:31 UTC) [open]

**[follow-up]** The `arb_hifi_duration` strategy feeds `any::<i128>()` through `HD::from_total_nanoseconds` with the comment that it "saturates to MIN/MAX outside the i16-century range". If hifitime silently saturates rather than panicking, values near `i128::MIN`/`i128::MAX` will all collapse to `HD::MIN`/`HD::MAX`, dramatically over-weighting the boundary values in the Galois-law tests and potentially masking failures in the interior. The comment should explicitly confirm this saturation behaviour (with a version-pinned reference to hifitime's docs or source), or the range should be clipped to `[HD::MIN.total_nanoseconds(), HD::MAX.total_nanoseconds()]` to make the distribution intent-driven.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322165639 -->
<!-- glab-discussion: d47a64d585140d03301ea170fb7a3e23704177e5 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/duration.rs:294` (2026-05-06 23:31 UTC) [open]

**[follow-up]** The `HDURSECS` doc comment says "`floor = ceil` under `new_left`" and describes the rounding as "away from zero on positive sub-second residues", but the spot test `hdursecs_negative_subsec_rounds_toward_zero` shows −5.000_000_001 s → ceil = −5, which is rounding *toward* zero (i.e., *up* on the number line). The description "rounds away from zero" is only accurate for positive inputs; the doc should instead say "rounds toward +∞" (or "ceiling division") to be unambiguous for both signs.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322328924 -->
<!-- glab-discussion: 296fb4d0f61007aa1c74c33ba087d0269fb12813 -->
#### ↳ cmk (2026-05-07 01:07 UTC) [open]

Fixed — `hd_min_secs` / `hd_max_secs` now derive via `total_nanoseconds() / 1_000_000_000` (i128 integer arithmetic; result lands at ±10¹⁴, well inside i64). The f64 path was lossy at HD::MIN/MAX magnitudes (±10²³ exceeds 2⁵³), and HD::MAX's non-canonical `nanoseconds == NANOSECONDS_PER_CENTURY` made it especially fragile. Same fix in `arb_hifi_total_secs_in_range`.

<!-- glab-id: 3322329140 -->
<!-- glab-discussion: d5da7b5a8bcc4f2538a034ae77c5e67eae6f6f88 -->
#### ↳ cmk (2026-05-07 01:07 UTC) [open]

Fixed — added `hdursecs_roundtrip_ceil` proptest plus the `arb_hifi_total_secs_in_range` strategy in this round, so MR !63 ships the full '5 + 1' set the plan promised. The earlier deferral to !64 was the wrong call.

<!-- glab-id: 3322330196 -->
<!-- glab-discussion: 32c38a451ee654556f44df4246d95f6119e83776 -->
#### ↳ cmk (2026-05-07 01:08 UTC) [open]

Fixed — added a comment confirming hifitime 4.3's saturation behavior on `Duration::from_total_nanoseconds` (verified by reading `hifitime/src/duration/mod.rs:172`) and explaining why the over-weighted boundary is intentional alongside the explicit interior `Just`s. Clipping the range would suppress the saturation arms from receiving any sampling at all.

<!-- glab-id: 3322330549 -->
<!-- glab-discussion: d47a64d585140d03301ea170fb7a3e23704177e5 -->
#### ↳ cmk (2026-05-07 01:08 UTC) [open]

Fixed — reworded the rounding doc to 'ceiling division (rounds toward +∞), uniform across both signs' with the worked `-5.000_000_001 s → -5` example. The prior 'rounds away from zero' phrasing only held for positive inputs.

<!-- glab-id: 3322342392 -->
<!-- glab-discussion: fd5a1204fd8718f7d315d5a1806dcab856780665 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/duration.rs:341` (2026-05-07 01:16 UTC) [open]

**[must-fix]** The `hdursecs_synthetic_arms` spot-check computes `max_s` via `HD::MAX.to_seconds() as i64`, the exact f64-cast path that the plan's Review section and the `hd_max_secs` doc both explicitly warn against (f64 can't represent `±1.03 × 10¹⁴` exactly and `HD::MAX` is non-canonical). The implementation functions (`hd_max_secs`) were fixed to use integer arithmetic, but this test still uses the lossy path — so if the boundary is ever off by one, the test won't catch it and may even silently agree with a wrong value.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322342440 -->
<!-- glab-discussion: 821a80bf4054ff57d77f36e34a9ecc3bfd0de458 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/prop/arb.rs:1060` (2026-05-07 01:16 UTC) [open]

**[follow-up]** The comment says `any::<i128>()` is left unbounded so saturation arms get proportional sampling, but it simultaneously claims the explicit `Just`s above cover interior values. With the i128 range being `~1.6 × 10¹⁵` times larger than the HD range, effectively all draws from this slot collapse to `HD::MIN` or `HD::MAX`, making the 12-weight slot almost entirely redundant with the `1 => Just(HD::MIN)` and `1 => Just(HD::MAX)` slots and providing zero interior coverage beyond the named constants. A bounded range (`HD::MIN.total_nanoseconds()..=HD::MAX.total_nanoseconds()`) with a separate small-weight unbounded slot for the saturation arms would match the stated intent.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322393923 -->
<!-- glab-discussion: fd5a1204fd8718f7d315d5a1806dcab856780665 -->
#### ↳ cmk (2026-05-07 01:58 UTC) [open]

Fixed — the test now derives `max_s` via `(HD::MAX.total_nanoseconds() / 1_000_000_000) as i64`, matching the integer-arithmetic path `hd_max_secs` was migrated to. Good catch — the round-1 fix updated the helpers but missed this test fixture, so a boundary drift wouldn't have been caught.

<!-- glab-id: 3322393960 -->
<!-- glab-discussion: 821a80bf4054ff57d77f36e34a9ecc3bfd0de458 -->
#### ↳ cmk (2026-05-07 01:58 UTC) [open]

Fixed — split into a weight-11 bounded slot (uniform interior coverage over `[HD::MIN.total_ns(), HD::MAX.total_ns()]`) plus a weight-1 unbounded slot (saturation arms only). The round-1 comment was incorrect: with i128 ~10¹⁵× wider than HD, the unbounded slot collapsed essentially every draw to MIN/MAX, providing zero interior coverage.

<!-- glab-id: 3322401732 -->
<!-- glab-discussion: b489caabbd25f34631fba8e1a5ffa66f49279d33 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/duration.rs:381` (2026-05-07 02:05 UTC) [open]

**[must-fix]** The `f064hdur_ceil` function uses `HD::MAX.to_seconds()` and `HD::MIN.to_seconds()` (f64 casts) for the out-of-range guard, but the implementation commentary and the `hd_max_secs`/`hd_min_secs` helpers were explicitly migrated away from this path because `HD::MAX`/`HD::MIN` are at `±1.03 × 10²³` s magnitude — far past `f64`'s exact-integer range of `2⁵³ ≈ 9 × 10¹⁵`. Using lossy f64 casts here means the bounds comparison may admit or reject values the integer-arithmetic path would not, causing `f064hdur_ceil` to return `PosInf` or `Finite(HD::MIN)` for inputs that should round-trip to a finite `Duration`. Replace `HD::MAX.to_seconds()` / `HD::MIN.to_seconds()` with `hd_max_nanos() as f64 / 1e9` or equivalent integer-derived constants, matching the fix already applied to `hd_max_secs`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322401745 -->
<!-- glab-discussion: 037b70f71b2c06c1004e3fb89f8ae69c5d1ce08b -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/duration.rs:431` (2026-05-07 02:05 UTC) [open]

**[must-fix]** The `f032hdur_ceil` function similarly uses `HD::MAX.to_seconds() as f32` and `HD::MIN.to_seconds() as f32` for the saturation guards. Beyond the same f64-precision loss at `±1.03 × 10¹⁴` s already identified for `f064hdur_ceil`, the additional `as f32` narrowing can shift the threshold by ULPs further, meaning the boundary check may pass or fail one step too early. The HD range is far larger than f32 can represent distinctly at those magnitudes, so the guard should derive its limit from integer arithmetic rather than a double lossy cast.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322401757 -->
<!-- glab-discussion: 2dbc040fd18040437725f8aaecf9ee36a3a03a7e -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/prop/arb.rs:1156` (2026-05-07 02:05 UTC) [open]

**[follow-up]** The `arb_hifi_total_secs_in_range` strategy bounds are computed at strategy-construction time via `HD::MIN/MAX.total_nanoseconds()`, which are `const`-eligible values, but the range literal `min_s..=max_s` captures runtime `i64` locals. This is correct but the strategy silently excludes the `min_s - 1` and `max_s + 1` saturation points that `hdursecs_inner` maps to `NegInf`/`PosInf`; a small-weight `Just(min_s - 1)` / `Just(max_s + 1)` slot (mirroring `arb_hifi_total_nanos_in_range`'s implicit all-in-range design) would confirm the boundary exactly where `hdursecs_galois_l` is most likely to fail.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322448446 -->
<!-- glab-discussion: b489caabbd25f34631fba8e1a5ffa66f49279d33 -->
#### ↳ cmk (2026-05-07 02:36 UTC) [open]

Fixed — `f064hdur_ceil` now derives bounds via `hd_max_secs() as f64` / `hd_min_secs() as f64`. The i64 helpers already do `total_nanoseconds() / 1_000_000_000` (i128 integer arithmetic), landing at `±10¹⁴` — well inside f64's exact-integer range (`2⁵³ ≈ 9 × 10¹⁵`), so the trailing `as f64` cast is precise. Same fix shape as round-2's `etaif064_ceil` migration on MR !64.

<!-- glab-id: 3322448495 -->
<!-- glab-discussion: 037b70f71b2c06c1004e3fb89f8ae69c5d1ce08b -->
#### ↳ cmk (2026-05-07 02:36 UTC) [open]

Fixed — same migration shape as `f064hdur_ceil`: bounds via `hd_{min,max}_secs() as f32`. The i64 helpers route through i128 integer arithmetic first, eliminating the f64 detour; the trailing `as f32` is still inherently lossy at `±10¹⁴` magnitude, but at least the *additive* boundary error from going through f64 first is gone. The walk's plateau dominates f32 precision at any non-trivial magnitude anyway, so the residual ULP shift is dwarfed by the plateau width.

<!-- glab-id: 3322448569 -->
<!-- glab-discussion: 2dbc040fd18040437725f8aaecf9ee36a3a03a7e -->
#### ↳ cmk (2026-05-07 02:36 UTC) [open]

Partial — added a separate `hdursecs_inner_saturation_boundary` spot test instead of extending the strategy. The bot's suggestion can't go directly into `arb_hifi_total_secs_in_range` because that strategy feeds `hdursecs_roundtrip_ceil`, which would fail at saturation values: `ceil(inner(min_s - 1)) = i64::MIN`, not `min_s - 1`. The targeted spot check captures the same boundary (`upper(min_s - 1) = NegInf`, `upper(max_s + 1) = PosInf`) without breaking round-trip. Galois-L coverage at the i64 extremes is already provided by `hdursecs_galois_l(b in any::<i64>())`.

<!-- glab-id: 3322469631 -->
<!-- glab-discussion: ae240a23c3eb10397d628ebef922ce897d392640 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/duration.rs:270` (2026-05-07 02:44 UTC) [open]

**[must-fix]** The `hdursecs_ceil` doc comment says `inner` saturates `i64` outside `[MIN.to_secs(), MAX.to_secs()]`, but `hd_min_secs()` / `hd_max_secs()` use `total_nanoseconds() / 1_000_000_000` (floor division), which truncates toward negative infinity for `HD::MIN` and toward zero for `HD::MAX`. This means `min_s = floor(MIN_ns / 1e9)` and `max_s = floor(MAX_ns / 1e9)`, so `hdursecs_inner(max_s)` returns `Finite(HD::from_total_nanoseconds(max_s * 1e9))` — a Duration potentially one second less than `HD::MAX` — while `hdursecs_inner(max_s + 1)` returns `PosInf`. The `hdursecs_roundtrip_ceil` strategy draws `max_s` and asserts `ceil(inner(max_s)) == max_s`, but `inner(max_s)` constructs a Duration at exactly `max_s` seconds, which `ceil` returns as `max_s` only if it has no sub-second nanoseconds; verify that `HD::MAX.total_nanoseconds() % 1_000_000_000 == 0` (i.e., `HD::MAX` is a whole number of seconds) or the round-trip will fail silently.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322469651 -->
<!-- glab-discussion: f66fb02af8eab6168aecda88b2a963d6c1959312 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/duration.rs:375` (2026-05-07 02:44 UTC) [open]

**[follow-up]** The `f064hdur_ceil` fast-path `if v <= min_secs { return Extended::Finite(HD::MIN) }` uses `hd_min_secs() as f64` as the threshold. Since `hd_min_secs()` floors `HD::MIN.total_nanoseconds() / 1_000_000_000` (truncation toward −∞), the threshold may be one second more negative than the true minimum representable whole-second value, causing `f64` values in `(true_min_f64, min_secs_as_f64]` to be fast-pathed to `HD::MIN` instead of entering the walk — which is correct behavior but should be documented explicitly, since the existing comment only explains why `HD::MAX.to_seconds()` was replaced, not why the fast-path bound is conservative by one second.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322469669 -->
<!-- glab-discussion: 671ad11395d9efce61d5cca1a1288cf28d9238d5 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/prop/arb.rs:1156` (2026-05-07 02:44 UTC) [open]

**[follow-up]** The `arb_hifi_total_secs_in_range` strategy comment says bounds are derived via integer arithmetic rather than `to_seconds() as i64`, which is correct, but `hd_min_secs()` uses `total_nanoseconds() / 1_000_000_000` (Rust integer truncation, not Euclidean division). For `HD::MIN` whose `total_nanoseconds()` is negative, truncation gives a result closer to zero than floor division would — i.e., `min_s` is one larger than the true floor. This means the strategy may include the value `true_floor_min_s = min_s - 1` (an i64 that `hdursecs_inner` maps to `NegInf`) if `HD::MIN.total_nanoseconds() % 1_000_000_000 != 0`, breaking `hdursecs_roundtrip_ceil`. Add an assertion or static check confirming `HD::MIN.total_nanoseconds() % 1_000_000_000 == 0`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322499014 -->
<!-- glab-discussion: ae240a23c3eb10397d628ebef922ce897d392640 -->
#### ↳ cmk (2026-05-07 03:05 UTC) [open]

Push-back — `HD::MIN.total_nanoseconds()` and `HD::MAX.total_nanoseconds()` are both **exact multiples of 10⁹**, so truncation-vs-floor is moot at the boundary. Each `NANOSECONDS_PER_CENTURY` is `100 × 365.25 × 86400 × 10⁹` ns = `3 155 760 000 × 10⁹` (divisible by 10⁹), and HD::{MIN, MAX} are integer-century multiples of that constant (HD::MAX uses `nanoseconds == NANOSECONDS_PER_CENTURY` at i16::MAX-1 century, which `from_total_nanoseconds` normalizes to i16::MAX with ns=0 — still divisible). The `hdursecs_roundtrip_ceil(max_s)` proptest verifies `ceil(inner(max_s)) == max_s` and is currently green; that wouldn't hold under the divisibility-failure scenario the comment describes.

Pinned the invariant explicitly via a new `hd_min_max_total_ns_divisible_by_billion` test (`commit 4ad05e5`) so any future hifitime change that breaks divisibility flips the test red immediately.

<!-- glab-id: 3322499150 -->
<!-- glab-discussion: f66fb02af8eab6168aecda88b2a963d6c1959312 -->
#### ↳ cmk (2026-05-07 03:06 UTC) [open]

Push-back — the fast-path bound is **not** conservative by one second. `HD::MIN.total_nanoseconds() % 1_000_000_000 == 0` (each `NANOSECONDS_PER_CENTURY` is divisible by 10⁹), so `hd_min_secs() = HD::MIN.total_ns() / 10⁹` is the exact floor, not "one second more negative than the true minimum." The interval `(true_min_f64, hd_min_secs() as f64]` the comment posits is empty. The new `hd_min_max_total_ns_divisible_by_billion` test (commit `4ad05e5`) guards the invariant.

<!-- glab-id: 3322499213 -->
<!-- glab-discussion: 671ad11395d9efce61d5cca1a1288cf28d9238d5 -->
#### ↳ cmk (2026-05-07 03:06 UTC) [open]

Fixed — added `hd_min_max_total_ns_divisible_by_billion` test that asserts `HD::{MIN, MAX}.total_nanoseconds() % 1_000_000_000 == 0`. Currently both hold (per-century arithmetic is divisible by 10⁹), so the strategy never includes a `min_s - 1` value that would flip `inner` to NegInf. The test pins the invariant against future hifitime drift.

<!-- glab-id: 3322528165 -->
<!-- glab-discussion: c280b475ac90bca0b5b4186d7d308c364a887d9d -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/duration.rs:304` (2026-05-07 03:27 UTC) [open]

**[must-fix]** The comment in `hdursecs_ceil`'s `Finite` arm says `div_euclid` / `rem_euclid` give "floor-division semantics" and then describes rounding "away from zero on the floor side", but the function is `ceil` — it rounds toward +∞. The description "away from zero on the floor side" is a copy-paste error from an older draft; for negative sub-second values the residue is non-zero and the function returns `s_floor + 1`, which is *toward* +∞ (toward zero for negative inputs), not away from zero. This contradicts the corrected doc comment on `HDURSECS` itself (which was fixed in review round 1) and will mislead anyone reading the implementation body.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322528180 -->
<!-- glab-discussion: 2c13b16f6285220f45294cd2a24daf2e39d524ba -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/hifi/duration.rs:372` (2026-05-07 03:27 UTC) [open]

**[must-fix]** In `f064hdur_ceil` the `v == f64::NEG_INFINITY` arm returns `Extended::Finite(HD::MIN)`, but the doc comment for `F064HDUR` states `ceil(Extend(−∞)) → Finite(HD::MIN)` as intended behavior. However, `F064DURN` (the model this is ported from) maps `NEG_INFINITY` to `Finite(Duration::MIN)` because `Duration::MIN` is the smallest *finite* rung value; the Galois law requires `ceil(a) ≤ b ⇔ a ≤ inner(b)`, so for `a = Extend(NEG_INFINITY)` we need `ceil(a)` to be the *least* rung element reachable by `inner`. If `Extended::NegInf` is already handled (it returns `Extended::NegInf` ≤ everything), then `f64::NEG_INFINITY` as a distinct arm returning `Finite(HD::MIN)` is correct only if the rung order treats `Finite(HD::MIN)` as the bottom of the `Extended<HD>` lattice — but `Extended::NegInf` is the actual bottom. Any rung value `b` for which `inner(b) = Extended::NegInf` would satisfy `Finite(HD::MIN) ≤ inner(b)` vacuously only if `Finite(HD::MIN) ≤ Extended::NegInf`, which is false. Verify that no `Extended<HD>` rung value `b` exists for which `inner(b) = Extended::NegInf` while `Finite(HD::MIN) ≤ b`; if such `b` exists, the Galois law fails for the `a = Extend(NEG_INFINITY)` case.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322528194 -->
<!-- glab-discussion: 4848997b487331b1caeb18d6d321b599f7b5bdf3 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/prop/arb.rs:1062` (2026-05-07 03:27 UTC) [open]

**[follow-up]** The `arb_hifi_duration` strategy gates its `#[cfg]` on `feature = "hifi"` but the strategies are also needed by `#[cfg(all(feature = "testing", feature = "hifi"))]` test blocks — the arb functions themselves are unconditionally pub-re-exported under `#[cfg(feature = "hifi")]` rather than `#[cfg(all(feature = "testing", feature = "hifi"))]`. This means a downstream crate that enables only `hifi` (not `testing`) gets the proptest strategy symbols exported into their dependency, pulling in the `proptest` dev-dep into production builds. The re-export should be gated on `all(feature = "testing", feature = "hifi")` to match the convention used by the rest of `arb.rs`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3322653979 -->
<!-- glab-discussion: c280b475ac90bca0b5b4186d7d308c364a887d9d -->
#### ↳ cmk (2026-05-07 04:48 UTC) [open]

Fixed — reworded the inline comment to "ceiling division — `s_floor + 1` is toward zero for negatives, away from zero for positives" (commit `37db2be`). Good catch; the prior phrasing only held for positive inputs and contradicted the doc-comment fix from round 1.

<!-- glab-id: 3322654306 -->
<!-- glab-discussion: 2c13b16f6285220f45294cd2a24daf2e39d524ba -->
#### ↳ cmk (2026-05-07 04:48 UTC) [open]

Push-back — the analysis conflates two distinct match arms. `f064hdur_ceil`'s match dispatches on `ExtendedFloat<f64>`, which has three variants: `Bot` (the synthetic NegInf), `Top` (PosInf), and `Extend(f64)` (a finite or non-finite f64). The first two return `Extended::NegInf` / `Extended::PosInf` directly. The `f64::NEG_INFINITY` check fires *only* for `Extend(NEG_INFINITY)` — i.e., the user passed an f64 that happens to be -∞ wrapped inside `Extend`, NOT the synthetic `Bot`.

Returning `Finite(HD::MIN)` for `Extend(NEG_INFINITY)` is correct per Galois L: we need the smallest `b ∈ Extended<HD>` such that `Extend(NEG_INFINITY) ≤ inner(b)`. `inner(NegInf) = Bot` (extreme), `inner(Finite(HD::MIN)) = Extend(HD::MIN.to_seconds())` (a finite f64). For `Extend(NEG_INFINITY) ≤ Bot`, false (NegInf < Extend(NEG_INFINITY) per `ExtendedFloat`'s order: Bot < every Extend < Top). For `Extend(NEG_INFINITY) ≤ Extend(HD::MIN.to_seconds())`, true (NEG_INFINITY < any finite f64). So the smallest valid `b` is `Finite(HD::MIN)` — exactly what we return. Same pattern as `F064DURN`.

<!-- glab-id: 3322654453 -->
<!-- glab-discussion: 4848997b487331b1caeb18d6d321b599f7b5bdf3 -->
#### ↳ cmk (2026-05-07 04:48 UTC) [open]

Push-back — the entire `arb` module is gated `#[cfg(any(test, feature = "testing"))]` at `src/prop.rs:64-66`. So all of `arb`'s contents — including the `hifi_dur` submodule and its `pub use` — only compile when the `testing` feature is on (or under `cargo test`). Inner `cfg(feature = "hifi")` gates stack on top, so the effective gating IS `all(test_or_testing, hifi)`. A downstream that enables only `hifi` (no `testing`) does not pull in `arb` at all; `proptest` stays a dev-dep. No leak.
