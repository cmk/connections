# PR #22 — Add `?` (Try) impls for Interval/Extended/ExtendedFloat

## Summary

Fills three small holes in the wrapper-type API:

1. **`?`-operator support** (`core::ops::Try` + `FromResidual`) for
   [`Interval`], [`Extended`], and [`ExtendedFloat`], so the success
   payload is extracted and the boundary variants short-circuit —
   carrying *which* boundary was hit.
2. **`Extended::finite(self) -> Option<T>`**, the stable, bound-
   forgetting projection to `Option`.

### `?` semantics

| Type            | `?` extracts (Continue) | Short-circuits (Break)         |
|-----------------|-------------------------|--------------------------------|
| `Interval<A>`   | `Closed { lo, hi }` → `(lo, hi)` | `Empty`                |
| `Extended<T>`   | `Finite(t)` → `t`       | `NegInf` / `PosInf`            |
| `ExtendedFloat<T>` | `Extend(t)` → `t`    | `Bot` / `Top`                  |

Each residual type is the corresponding wrapper over
`core::convert::Infallible` (`Extended<Infallible>`, …). The success
arm is then uninhabited, so the only inhabited residual values are the
boundary variants — which is exactly what lets `?` inside a
`Wrapper<U>`-returning fn **reconstitute the specific boundary at a
fresh payload type** (`NegInf` stays `NegInf`, `Bot` stays `Bot`,
`Empty` stays `Empty`). `Try::Residual` is bound by `Residual<Output>`,
so each `…<Infallible>` type also gets a one-line `core::ops::Residual`
impl.

Deliberate asymmetry worth a reviewer's eye: for `ExtendedFloat`,
**`Extend(NaN)` is a success payload, not a short-circuit.** Only the
synthetic ±∞ endpoints (`Bot` / `Top`) break; a wrapped NaN flows
through `?` as an ordinary `Extend`, matching the variant's role as the
extension slot (which may hold NaN or ±∞) rather than a finiteness
claim. Covered by `extended_float_nan_is_a_payload_not_a_shortcircuit`.

### Nightly gating (mirrors `f16`)

`try_trait_v2` is unstable (tracking
[#84277](https://github.com/rust-lang/rust/issues/84277)), so the impls
sit behind a new **`try_trait` cargo feature**, gated exactly like the
existing `f16` feature:

- `#![cfg_attr(feature = "try_trait", feature(try_trait_v2))]` (plus the
  `_residual` half) in `lib.rs`.
- Default **stable** builds skip the impls entirely; `Cargo.toml` keeps
  it out of the `docs.rs` / stable-CI feature sets.
- The only CI job that compiles the code is `doc-nightly.yml`
  (`cargo +nightly doc --all-features`), which I ran locally clean with
  `RUSTDOCFLAGS=-D warnings`.

This is the forced choice — `Try` cannot be implemented on stable at
all — and it matches repo precedent. `finite()` is **not** gated; it is
ordinary stable code.

### Two design choices flagged for review

- **`Interval`'s `Try::Output` is the endpoint pair `(A, A)`**, matching
  `Interval::endpts`. The natural "unwrap" of a `Closed` is its two
  endpoints; the `Residual` impl is `impl<A> Residual<(A, A)> for
  Interval<Infallible>`.
- **`finite()` carries a `T: Copy` bound** so it can stay a `const fn`
  on stable. A `const fn` that consumes a generic enum can't evaluate
  its destructor without the nightly `const_precise_live_drops` feature
  (E0493); `Copy` types have no destructor. The bound is free for every
  `Extended<T>` used as a `Conn` endpoint (that machinery requires
  `A: Copy, B: Copy`), but it does exclude non-`Copy` payloads such as
  `Extended<String>` — the public type is not itself Copy-restricted.
  Non-`Copy` callers use the bound-free (non-`const`) equivalent
  `x.fold(None, None, Some)`. I chose to keep the requested `const fn …
  -> Option<T>` signature; the alternative is to drop `const` and take
  unbounded `T`.

### Soundness note (`Interval::from_output`)

`Try::from_output((lo, hi))` reconstructs `Closed { lo, hi }` **without**
re-running the `Interval::new` preorder check, exactly like direct
`Closed { .. }` field construction. `?` only ever feeds it endpoints
previously extracted from a valid `Closed` via `branch`, so the "no
`Closed` holds a non-reflexive value" invariant (on which `Eq`
soundness rests) is preserved in practice. A caller writing
`Try::from_output((hi, lo))` by hand bypasses the gate just as direct
construction already does — the same documented escape hatch, no new
one.

### Testing

`tests/try_impls.rs` (feature-gated; empty on stable, so outside the
stable CI gate — same posture as `f16` tests). Covers `?` extraction,
boundary propagation, payload-type change, the NaN case, and per-type
`branch` / `from_output` / `from_residual` round-trip **properties**
(proptest). Verified locally:

- `cargo +nightly test --features …,try_trait --test try_impls` — 9
  passed.
- `cargo +nightly doc --all-features` with `-D warnings` — clean.
- Stable gate (default toolchain 1.88): `cargo test` (full features),
  `cargo clippy --all-targets -D warnings`, `cargo doc -D warnings`,
  `cargo fmt --check`, `check_pii.sh`, `check_readme_mirror.sh` — all
  green; the `finite()` doctest passes on stable.

### Gardener notes

- `README.md` feature table gained a `try_trait` row. Pre-existing drift
  (not fixed here, out of scope): the table is **missing a `uhlc` row**
  and the `proptest`/`macros` prose still calls the strategy feature
  `testing`. Deferred.
- `cargo +nightly clippy -D warnings` is pre-existingly red (22 unused-
  import lints in `src/fixed/*` + `float.rs:129`, none from this diff) —
  which is why the clippy gate runs on stable. Not touched.

## Files

- `Cargo.toml` — `try_trait` feature.
- `src/lib.rs` — `try_trait_v2` / `try_trait_v2_residual` gates.
- `src/extended.rs` — `finite()` + `Try` / `FromResidual` / `Residual`.
- `src/float.rs` — `Try` / `FromResidual` / `Residual` for `ExtendedFloat`.
- `src/interval.rs` — `Try` / `FromResidual` / `Residual` for `Interval`.
- `tests/try_impls.rs` — new, nightly feature-gated.
- `README.md` — feature-table row.

[`Interval`]: https://docs.rs/connections/latest/connections/interval/enum.Interval.html
[`Extended`]: https://docs.rs/connections/latest/connections/extended/enum.Extended.html
[`ExtendedFloat`]: https://docs.rs/connections/latest/connections/float/enum.ExtendedFloat.html

## Local review (2026-07-06)

**Branch:** feat/try-impls
**Commits:** 2 (origin/main..feat/try-impls)
**Reviewer:** Codex (`codex review --base origin/main`)
**Prompt fingerprint:** AGENTS.md=4563f590caa7dbba5ea9eae973fa59182f1a6470 calibration=missing

---

I did not identify any actionable correctness issues in the diff. The new nightly-gated Try/Residual impls and tests appear consistent with the documented feature gating and existing API patterns.


<!-- gh-id: 4642032916 -->
### copilot-pull-request-reviewer[bot] — COMMENTED ([2026-07-07 05:51 UTC](https://github.com/cmk/connections/pull/22#pullrequestreview-4642032916))

## Pull request overview

This PR extends the crate’s wrapper-type ergonomics by adding nightly-gated `?`-operator support (`core::ops::Try` / `FromResidual` / `Residual`) for `Interval`, `Extended`, and `ExtendedFloat`, plus a stable `Extended::finite(self) -> Option<T>` projection.

**Changes:**
- Add a new `try_trait` Cargo feature that enables nightly-only `Try`/`FromResidual`/`Residual` impls for `Interval`, `Extended`, and `ExtendedFloat`.
- Add `Extended::finite` as a stable (const) projection to `Option<T>` (bound-forgetting).
- Add a feature-gated nightly integration test suite covering `?` behavior (including NaN-as-payload for `ExtendedFloat`) and residual round-trips.

### Reviewed changes

Copilot reviewed 8 out of 8 changed files in this pull request and generated 1 comment.

<details>
<summary>Show a summary per file</summary>

| File | Description |
| ---- | ----------- |
| `Cargo.toml` | Adds the `try_trait` feature flag and documents its intended semantics/gating. |
| `src/lib.rs` | Enables nightly `try_trait_v2` / `try_trait_v2_residual` behind the `try_trait` feature. |
| `src/extended.rs` | Adds `Extended::finite` and implements `Try`/`FromResidual`/`Residual` for `Extended` behind `try_trait`. |
| `src/float.rs` | Implements `Try`/`FromResidual`/`Residual` for `ExtendedFloat` behind `try_trait`. |
| `src/interval.rs` | Implements `Try`/`FromResidual`/`Residual` for `Interval` behind `try_trait`. |
| `tests/try_impls.rs` | Adds nightly-only integration tests for `?` semantics and residual round-trips (proptest). |
| `README.md` | Documents the new `try_trait` feature in the optional-features table. |
| `doc/reviews/review-00022.md` | Adds/updates the PR review record (audit-trail document). |
</details>







<!-- gh-id: 3533933864 -->
### Copilot on [`src/extended.rs:204`](https://github.com/cmk/connections/pull/22#discussion_r3533933864) (2026-07-07 05:51 UTC)

Doc comment claims the `T: Copy` bound “excludes no real caller”, but `Extended<T>` is a public wrapper that can be used with non-`Copy` payloads (e.g. `Extended<String>`), for which this method will be unavailable. Consider rephrasing to avoid implying the bound is cost-free, and point readers to the stable non-`Copy` alternative (`fold(None, None, Some)`).

<!-- gh-id: 3533975477 -->
#### ↳ cmk ([2026-07-07 06:01 UTC](https://github.com/cmk/connections/pull/22#discussion_r3533975477))

Fixed — reworded the doc to drop the "excludes no real caller" overclaim. It now says the bound is free only for `Extended` used as a `Conn` endpoint but does exclude non-`Copy` payloads such as `Extended<String>`, and points readers to the stable, bound-free (non-`const`) equivalent `x.fold(None, None, Some)` — with a doctest exercising the `String` case.
