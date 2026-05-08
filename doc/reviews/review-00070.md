# MR !70 — Plan 47: feature-flagged `byte` module

## Summary

- Add `byte` cargo feature gating a new `connections::byte::*` module
  that ships **14 sortable byte-encoding Conns**: `{u,i}{8..128} ↔
  [u8; N]` (big-endian for unsigned; sign-flipped BE for signed),
  `f{16,32,64} ↔ [u8; N]` (IEEE 754 totalOrder pre-encoding via the
  same algebra `signed32` already uses for ULP walks), and a one-sided
  `BOOLOBYT`. Right-side constant code is `OBYT` ("Ordered BYTes").
- All 13 isos are degenerate Galois (`floor = ceil = forward`) with
  bit-exact round-trip; lex byte order matches host numeric order
  (`total_cmp` for floats). No new third-party dependencies — the
  implementation only touches std's `to_be_bytes` / `from_be_bytes`.
  Default builds (no `byte` feature) are unaffected.
- Verification: 73 proptests + 7 doctests + **43 Kani SMT proofs**
  (1- and 2-byte hosts exhaustive; 4-byte under 64-bit symex on the
  two-input order-preservation predicate). 8/16-byte hosts are
  proptest-only; CBMC stalls on 128/256-bit two-input symex.

## Test plan

- `cargo test --workspace` — default-feature build, all 1166 existing
  tests pass; byte module is invisible.
- `cargo test --workspace --features byte` — adds 69 byte proptests +
  7 byte doctests, all green.
- `cargo clippy --all-targets --features byte -- -D warnings` — clean.
- `cargo kani --features byte --harness 'byte_'` — 43/43 SMT proofs
  green.
- `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features byte`
  — docs render without intra-link breakage.

<!-- glab-id: 3326269701 -->
<!-- glab-discussion: 0b45519b69fa1261b3e2839ace10fa78bd2a4ad8 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/byte/one.rs:155` (2026-05-07 22:31 UTC) [open]

**[follow-up]** The `bool_obyt_galois_l` proptest asserts `conn_laws::galois_l(&BOOLOBYT, a, b)`, but `BOOLOBYT` is defined via `conn_l!`, not `iso!`. The Galois-L law `ceil(a) ≤ b ⟺ a ≤ inner(b)` requires `inner` to be order-reflecting, which fails for all bytes `b ≥ 2`: `ceil(true) = [1] ≤ [2] = b` is true, but `true ≤ inner([2]) = true` is `true ≤ true` which is true — so it accidentally holds here, but only because `bool` has two elements. The comment says "Galois L still holds" without a proof sketch; it would be worth adding a one-line explanation that the collapsing of `0x02..=0xFF` to `true` doesn't violate L because `ceil(true) = [1]` is the only non-`[0]` canonical value.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3326269746 -->
<!-- glab-discussion: 5b89896772d598df07be49e8525a48cd344ad3ff -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/byte/one.rs:116` (2026-05-07 22:31 UTC) [open]

**[must-fix]** The plan (T4, §Deferred) and the doc-comment both say `BOOLOBYT` is a one-sided `conn_l!` (not an iso), and explicitly state that `roundtrip_ceil` (i.e. `ceil ∘ inner = id`) **fails** for bytes `0x02..=0xFF`. Yet `bool_obyt_iso_roundtrip_l` at line 169 calls `conn_laws::iso_roundtrip_l(&BOOLOBYT, a)` which only tests the *host-side* direction (`inner ∘ ceil = id`), not the byte-side direction — and the comment above it misleadingly labels it `iso_roundtrip_l` without clarifying that the byte-side roundtrip is intentionally absent. More critically, there is **no** `roundtrip_ceil` test for `BOOLOBYT` at all — the comment at line 153 says it is skipped, which is correct, but the test name `bool_obyt_iso_roundtrip_l` implies a full iso roundtrip. Rename the test to `bool_obyt_host_roundtrip_l` (or similar) to match the one-sided claim, so future readers do not add a byte-side roundtrip assertion expecting it to pass.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3326269801 -->
<!-- glab-discussion: 4007ef1d9497b302b598b2ccb1f8664bd6dafd6f -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/byte/four.rs:75` (2026-05-07 22:31 UTC) [open]

**[follow-up]** The `obyt_to_f32` inverse incorrectly branches on whether the _sortable_ MSB is set rather than whether the _original_ sign bit was set. For a positive float (original bit 31 = 0), `f32_to_obyt` sets bit 31 of `sortable` to 1 (XOR with `0x80000000`). The inverse must recover the original by XORing again — so the branch `if sortable & 0x8000_0000 != 0` → `sortable ^ 0x8000_0000` is correct for that case. For a negative float (original bit 31 = 1), `f32_to_obyt` produces `!bits`, whose MSB is 0. The inverse must be `!sortable` when `sortable & 0x8000_0000 == 0`. The current code does this correctly, but the logic is the mirror image of what the comment describes; consider adding an inline comment that the sortable MSB being 1 means the original was positive, to prevent future confusion and mismatched edits.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3326269841 -->
<!-- glab-discussion: 144b22c5bcd3221a771f2c7eea8978ab504c3d44 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/kani_proofs/byte_one.rs:77` (2026-05-07 22:31 UTC) [open]

**[follow-up]** The `any_bool()` helper derives a `bool` from `kani::any::<u8>() != 0`, meaning Kani will explore 255 `true` paths and one `false` path in `order_preserving`, giving the symbolic executor a heavily skewed tree. A more symmetric construction is `kani::any::<bool>()` if Kani supports it, or `kani::any::<u8>() >= 128` to split the space 50/50. The current formulation will still verify correctness but wastes solver budget and may obscure coverage statistics.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3326619955 -->
<!-- glab-discussion: 0b45519b69fa1261b3e2839ace10fa78bd2a4ad8 -->
#### ↳ cmk (2026-05-08 01:54 UTC) [open]

Fixed — extended the doc comment on `obyt_to_bool` with the one-line algebra (`ceil(true) = [1]` and `inner` returns `true` exactly for `b ≥ [1]`, so `b ≥ ceil(a)` matches `inner(b) ≥ a` for both `a` values).

<!-- glab-id: 3326620116 -->
<!-- glab-discussion: 5b89896772d598df07be49e8525a48cd344ad3ff -->
#### ↳ cmk (2026-05-08 01:54 UTC) [open]

Fixed — renamed both the proptest and Kani harness from `*_iso_roundtrip_l` to `*_host_roundtrip_l` and clarified in the test comment that the byte-side roundtrip is intentionally absent (because `BOOLOBYT` is one-sided).

<!-- glab-id: 3326620256 -->
<!-- glab-discussion: 4007ef1d9497b302b598b2ccb1f8664bd6dafd6f -->
#### ↳ cmk (2026-05-08 01:54 UTC) [open]

Fixed — added an inline comment to `obyt_to_f32` (and the parallel comment to `obyt_to_f64`) noting that sortable MSB set means the original was positive (forward XORed it) and sortable MSB clear means the original was negative (forward inverted everything).

<!-- glab-id: 3326620393 -->
<!-- glab-discussion: 144b22c5bcd3221a771f2c7eea8978ab504c3d44 -->
#### ↳ cmk (2026-05-08 01:54 UTC) [open]

Pushing back — the 255:1 byte split doesn't translate into a solver-budget skew since CBMC explores the symbolic `u8` exhaustively and both bool cases (`n=0` and `n>0`) are reachable; the solver unifies the analysis at the abstract bool level, not per-byte. `kani::any::<bool>()` was the original construction and triggered the spurious-counterexample bug we documented (`bool/PartialOrd` interaction in Kani 0.67), which is why the workaround exists. Switching to `n >= 128` would change the byte distribution without affecting either correctness or coverage, and would trade a clear documented workaround for a comment-less encoding.
