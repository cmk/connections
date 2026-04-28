# Review 00039 — Plan 25: fold int/ + NonZero into fixed/

## Summary

- Folds `connections::int::*` into `connections::fixed::*` (every
  std-int Conn is structurally a Q*N*.0 fixed-point) and renames
  every intra-fixed Conn prefix `I`/`U` → `Q` so prefix letters alone
  disambiguate Fixed wrappers from std primitives. ~150 constants
  renamed; std-int names (e.g. `I064I128`, `U008I016`) keep their
  letter prefixes since they target std primitives.
- Adds two new families on top of the merge: 10 NonZero Conns
  (`fixed::iN::I{NN}N{NN}`, `fixed::uN::U{NN}N{NN}` of type
  `Conn<{i,u}N, NonZero<{i,u}N>>` — signed is the asymmetric-adjoint
  showcase, both Galois laws hold) and 10 cross-crate iso Conns
  (`fixed::iN::Q000I{NN}` etc., bridging `Fixed{I,U}<U0>` and the
  matching primitive). Lands a `Conn::new_iso` constructor used by
  the iso family.
- Resets `Cargo.toml` to `version = "0.0.0"` (crate is unpublished;
  first crates.io release will be `0.0.1`). Internal-only refactor
  — no migration concern outside the repo.

## Test plan

- [x] `cargo test --workspace` clean across all 18 binaries (1171
      lib tests + 16 integration tests + doctests).
- [x] `cargo clippy --all-targets -- -D warnings` clean.
- [x] `cargo build` clean.
- [x] Depcheck: `git grep "connections::int::"` and `crate::int::`
      return zero hits in `src/`, `tests/`, `README.md`, `CLAUDE.md`.
- [x] T2.5 audit: `git grep -E 'fix_fix_[iu][0-9]+!\([IU][0-9]{3}[IU][0-9]{3}'`
      returns zero hits (every intra-fixed Conn prefix is now `Q`).
- [x] NonZero spot tests on i8 (signed) + u8 (unsigned) cover
      asymmetric `floor`/`ceil` at zero, total inner embedding,
      finite round-trip, infinity / saturation behaviour.
- [x] NonZero proptest: `i008n008_galois_l` + `i008n008_galois_r` +
      `i008n008_inner_then_ceil_recovers_nonzero` all pass on the
      signed Conn (full triple). Unsigned `u008n008_galois_l` +
      round-trip pass; `galois_r` is correctly *not* asserted (fails
      at the unsigned bottom plateau by type-theoretic necessity).
- [x] Iso proptest: `q000i008_galois_l` + `_r` +
      `q000i008_round_trip_both_directions` all pass.
- [ ] Property-test battery on all 10 NonZero widths and all 10 iso
      widths (currently only i8 + u8 representatives are exercised;
      the macros guarantee uniformity, but a parity check would be
      cheap insurance). Tracked as a follow-up in the plan's
      Recommendations.
