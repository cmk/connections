# MR !72 — Unify Conn naming across `time/` and `hifi/`

## Summary

- Bring `time/` and `hifi/` Conn-constant names into one coherent
  scheme: Duration family uses suffix `-DUR` (`TDUR`/`SDUR`/`HDUR`),
  DateTime family uses suffix `-DTM` (`PDTM`/`ODTM`), Epoch family
  keeps prefix `E-` + 3-letter scale tag.
- Fix four classes of drift: the duration trio (`DURN`/`STDR`/`HDUR`
  → `TDUR`/`SDUR`/`HDUR`), the `EUTC*` reference-epoch ambiguity
  (J1900-anchored stays in `EUTC*`; UNIX-anchored split out to
  `EUNX*`), the **side-position bug** in nine `E*F064` Conns
  (`ETAIF064` → `F064ETAI`, …; the type was `Conn<F064, …>` but
  the name had F064 trailing), and the non-canonical `MONTNZ08`
  → `MONTN008` (`A123` shape per `fixed/i8.rs`'s `I008N008`).
- Mechanical rename only — no semantic changes; all 85 lib + 45 doc
  + 25 integration tests pass post-rename. Lint hook to prevent
  recurrence is deferred to a follow-up MR.

## Test plan

- [ ] `cargo build --all-targets --features hifi` — clean.
- [ ] `cargo test --features hifi` — 85 + 45 + 9 ignored, all pass.
- [ ] `cargo test --doc --features hifi` — 66 pass (9 pre-existing ignored).
- [ ] `cargo clippy --all-targets --features hifi -- -D warnings` — clean.
- [ ] `RUSTDOCFLAGS=-D warnings cargo doc --no-deps --document-private-items --features hifi` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `scripts/check_readme_mirror.sh` — clean.
- [ ] CI green on the MR pipeline.

## Local review (2026-05-07)

**Branch:** sprint/conn-name-unify
**Commits:** 1 (origin/main..sprint/conn-name-unify)
**Reviewer:** Claude (sonnet, independent)

---

Reviewing `sprint/conn-name-unify` (commit `4ef54ed`) — diff between `origin/main` and HEAD, 4887 lines across 22 files.

### Commit Hygiene

Single commit, `refactor:` prefix, 72-char subject. Body explains all four bug-classes and the T5/T6 deferral. Clean.

### Critical

**`hdurnano_*` helpers corrupted to `htdurano_*` in `src/hifi/duration.rs`**

Confidence: 95

The Const `HDURNANO` was correctly left alone (the `HDUR` family was not part of the rename map), but the private helpers that implement it — `hdurnano_ceil` and `hdurnano_inner` — were renamed to `htdurano_ceil` and `htdurano_inner` (note the transposition: `hdur` → `htdur`, dropping the `nano` suffix and inverting the `dur`/`ano` order). The test function names suffered the same corruption: `hdurnano_zero` → `htdurano_zero`, `hdurnano_galois_l` → `htdurano_galois_l`, and so on across approximately 12 test functions. The Kani harness in `src/kani_proofs/hifi_pure.rs:172` reflects the same corruption:

```rust
prove_l!(htdurano, HDURNANO, arb_ext_hd, arb_i128);
```

The conventional pattern throughout the codebase is that private helpers mirror their Const name in lower-snake-case: `tdursecs_ceil` for `TDURSECS`, `eunxnano_ceil` for `EUNXNANO`. Here the helpers should remain `hdurnano_ceil` and `hdurnano_inner`. The code compiles because these are private, but the convention is violated and the helpers are now unsearchable by their Const name.

Root cause: a broad `s/durn/tdur/g` substitution in the rename script matched the `durn` substring inside `hdurnano`.

Fix: rename `htdurano_ceil` → `hdurnano_ceil`, `htdurano_inner` → `hdurnano_inner`, and the ~12 test functions from `htdurano_*` back to `hdurnano_*`. Apply the same fix to `kani_proofs/hifi_pure.rs:172`. Total: 18 stale tokens (`grep -c htdur` in `src/`).

### Important

**`src/hifi/epoch.rs` module header not fully updated — two stale references**

Confidence: 88

Lines 11 and 33 of `src/hifi/epoch.rs` describe pre-rename state:

Line 11 (`EUTC*` reference epoch):
```
//! - **`EUTC*`** uses **UNIX EPOCH UTC** (1970-01-01 00:00:00) as the
//!   implicit zero — matches the "unix nanoseconds" semantic of
```

This description was accurate when `EUTCNANO` and `EUTCF064` were in the `EUTC*` family. After this MR those two Conns moved to `EUNX*`. The only remaining `EUTC*` member is `EUTCHDUR`, which uses J1900 UTC. The sentence now misdescribes the family. The `src/hifi.rs` module-level doc was correctly updated (the `## Reference epochs` section now says `EUTC* → J1900 UTC, leap-second-aware`), but the `epoch.rs` local header was not.

Line 33 (`E{xx}F064` shape bullet):
```
//! - **`E{xx}F064`** — `F064 → Extended<Epoch>` via 1 ns ULP walks
```

This still uses the old name shape. The entire point of the side-position fix was that the float belongs on the left side of the name: `F064E{xx}`. The bullet should read `**`F064E{xx}`**`.

Fix (two-line patch to `epoch.rs` module header):
- Line 11: change to describe J1900 UTC and reference `EUNX*` for the UNIX-anchored family.
- Line 33: change `**`E{xx}F064`**` to `**`F064E{xx}`**`.

### Code Quality

**Mechanical-rename completeness — clean (apart from the `htdur` corruption above)**

`grep -rn 'durn|stdr|ofdt|eutcnano|eutcf064|montnz08'` across `src/` returns only legitimate `HDURNANO`/`HDURSECS` hits (the `HDUR` family was correctly not renamed) plus one `arb.rs` comment mentioning `DURNFD09` (a downstream identifier). No stale `DURNSECS`, `F064DURN`, `STDRU064`, `OFDTNANO`, `EUTCNANO`, `MONTNZ08` references survive. `tests/` is clean. History docs (`doc/plans/`, `doc/reviews/`, `doc/notes/`) are correctly untouched — only `plan-2026-05-07-05.md` and `review-00072.md` are added.

**Name-position invariant (sample)**

- `EUNXNANO`: `pub EUNXNANO : Extended<Epoch> => i128`. Left = `Extended<Epoch>` → `EUNX`; right = `i128` → `NANO`. ✓
- `F064EUNX`: `pub F064EUNX : F064 => Extended<Epoch>`. Left = `F064`; right = `Extended<Epoch>` → `EUNX`. ✓ (confirms the side-position flip from the old `EUTCF064 : F064 => Extended<Epoch>`).
- `MONTN008`: `pub MONTN008 : Extended<MonthName> => NonZeroU8`. ✓ Consistent with `fixed::i8::I008N008`.

**Cross-module collisions — none.** `time::` re-exports (`TDUR*`, `SDUR*`, `ODTM*`, `PDTM*`) and `hifi::` re-exports (`HDUR*`, `E***`, `MONT*`, `WKDY*`) are disjoint.

**Drive-by escape fix** in `src/hifi.rs` constants table — `\[1,12\]`, `\[0,6\]` is the correct fix (suppresses rustdoc intra-doc-link parsing).

**README mirror sync**: `README.md` references `TDURSECS`/`SDURU064` matching `src/time.rs`'s doctest.

**Duration-trio uniformity**: All three families use suffix-DUR consistently: `TDUR` (time), `SDUR` (std), `HDUR` (hifitime).

### Test Coverage

No new tests added (appropriate for a mechanical rename). Existing proptest batteries renamed in parallel with their Conns. The `htdurano_*` corruption means those test names violate the convention but the tests still pass because `HDURNANO` itself is untouched.

### Plan Conformance

All 20 entries in the rename map are present in the diff. T1-T4 complete. T5/T6 (lint hook) correctly deferred — no `scripts/check_conn_names.py` appears.

### Risks

No TODOs or FIXMEs introduced. No semantic changes; `cargo build` passes per the author. The `htdur*` corruption compiles fine (private helpers) but should be fixed for searchability and convention.

### Recommendations

**Must fix before push:**

1. `src/hifi/duration.rs` — rename `htdurano_ceil` → `hdurnano_ceil`, `htdurano_inner` → `hdurnano_inner`, and the ~12 test functions from `htdurano_*` back to `hdurnano_*`. The section comment on line 95 still reads `// ── HDURNANO ─` which confirms intent was to leave these helpers alone.

2. `src/kani_proofs/hifi_pure.rs:172` — change the Kani `prove_l!` tag from `htdurano` to `hdurnano`.

3. `src/hifi/epoch.rs` module header — update line 11 to describe J1900 UTC for `EUTC*` (cross-reference `EUNX*` for UNIX), and line 33 to use `F064E{xx}` shape.

**Follow-up (future work):**

- T5/T6 lint hook (`scripts/check_conn_names.py` + `.githooks/pre-commit` wiring) — correctly deferred; would have caught both the `htdurano` helper names and the stale module header lines automatically. The lint should also forbid `s/X/Y/g`-style overzealous substitution by validating that no identifier outside the registry survives a rename.
- `arb_extended_sdur_nanos_in_range` in `src/prop/arb.rs` is defined but not called from any test (pre-existing gap; the old `_stdr_` form had the same issue). Track separately.
