# MR !31 — Reestablish `compose!` macro tests on `conn::fixed::i8`

## Summary

The decimal-removal MR (!29) dropped the FD-based `compose!` test
battery without backfill, leaving the macro covered only by its
inline doctest. This MR reestablishes the multi-step compose tests
against the binary fixed-point Q-format ladder in
`conn::fixed::i8` — a natural multi-step chain that ships in the
crate and admits a hand-coded non-adjacent shortcut (`I008I000`)
to compare composed Conns against.

Coverage:

- **2-step**: `compose!(I008I004, I004I000) == I008I000` at boundary
  i8 samples.
- **3-step**: `compose!(I008I006, I006I004, I004I000) == I008I000`.
  (Odd parent count exercises the recursive `$rest` splicing arm.)
- **4-step**: `compose!(I008I006, I006I004, I004I002, I002I000) ==
  I008I000`. Same domain as 2- and 3-step; the distinct expansion
  shape exercises the macro's longest tail.
- **Identity laws**: `compose!(id, c)` and `compose!(c, id)` are
  pointwise equal to `c` (exhaustive over all 256 i8 values).
- **Galois-law preservation**: the 4-step composed Conn satisfies
  `conn_galois_l/r`, `conn_monotone_l/r`, `conn_idempotent`. Tests
  use `any::<i8>()` (the full 256-pattern domain is cheap; no
  bounded-range strategy needed since there's no overflow risk on
  the i8-backed ladder).
- **Const-context coercion**: every `const COMPOSED_*` declaration
  in the test mod fails to compile if the macro's non-capturing
  closures don't coerce to bare `fn`-pointers, so the
  Copy/const-constructible shape is verified at build time.

`floor ≤ ceil` is intentionally *not* asserted as a proptest law:
the `fix_fix_i8!` macro uses saturation-fixup arms at
`bits == ±i8::MAX` that pin one adjoint to the opposite end of the
range, violating the simple ordering at exactly those two boundary
inputs. Per-pair tests in `conn::fixed::i8` document and accept this
trade-off (it preserves the 1-ULP closure bound). The other Galois
adjoint laws hold unconditionally on the composed Conn.

Diff: src/conn.rs only, +~140 lines under the existing
`#[cfg(test)] mod tests` block.

## Test plan

- [ ] CI green (fmt, clippy, test, doc).
- [ ] `cargo test --lib` runs the new 5 unit tests + 5 proptests
      cleanly (verified pre-push: 1193 lib tests pass).
- [ ] `cargo doc --no-deps --all-features --document-private-items`
      under `RUSTDOCFLAGS="-D warnings"` clean (verified pre-push).
- [ ] `cargo clippy --all-targets -- -D warnings` clean (verified
      pre-push).
