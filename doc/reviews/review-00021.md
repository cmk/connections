# PR #21 — Hoist full Conn API onto ConnL/ConnR/ConnK methods

## Summary

Markers and `Conn` values now share one uniform, method-call surface.
Before this change, every accessor was **inherent on `Conn` values** and
the two-sided helpers were **free functions**, so using an adjoint-triple
marker (`conn_k!` / `iso!` / `compose_k!` / `lift_k!` / `nz_int_ext!`)
meant projecting first — `NDURU064.view_l().ceil(x)` in-crate, or the
`NDURU064.swap_r().ceil(x)` workaround downstream. The goal was for users
to rarely (ideally never) need `view_l` / `view_r`.

The accessor API is now hoisted onto the capability traits as **default
methods** over the single required primitive (`swap_l` / `swap_r`):

| Trait   | Required          | Provided (default) methods                                                          |
|---------|-------------------|-------------------------------------------------------------------------------------|
| `ConnL` | `swap_l`          | `view_l`, `ceil`, `upper`, `ceil1`, `ceil2`, `upper1`, `upper2`                     |
| `ConnR` | `swap_r`          | `view_r`, `floor`, `lower`, `floor1`, `floor2`, `lower1`, `lower2`                  |
| `ConnK` | — (blanket impl)  | `interval`, `truncate`, `truncate1`, `truncate2`, `round`, `round1`, `round2`, `median` |

So `MARKER.ceil(a)`, `MARKER.round(x)`, `MARKER.interval(x)`,
`MARKER.median(x, y, z)` now work directly. `median` is gated to the
diagonal `A = (B, B)` markers it always required.

### How it fits together

- **Blanket impls** join `Conn<A, B, L>` / `Conn<A, B, R>` values to
  `ConnL` / `ConnR`. A value is only *one* of the two, so it never
  becomes `ConnK` — the two-sided helpers stay triple-only, which is
  correct.
- **Const composition is untouched.** The inherent `const fn` accessors
  stay on `Conn` values as the base; value receivers keep resolving to
  them (inherent wins method resolution over a trait default), so
  `compose_*!` / `lift_*!` and every `const` position behave exactly as
  before. The new trait methods are not `const` (trait methods can't be
  on stable Rust) and only bind on marker / generic receivers.
- **Marker inherent `view_l` / `view_r` are now `pub`** (were
  `pub(crate)`), matching their sibling `swap_l` / `swap_r`. This lets
  downstream reach the raw `Conn` when it wants one, and prevents the
  now-added trait `view_l` default from being shadowed by a private
  inherent method (a privacy error, not a fall-through).
- **Free fns are retained as forwarders** (`view_l` / `view_r` plus the
  eight two-sided). Deleting them and migrating every remaining call
  site is a follow-up sweep.

### Notable implementation detail

Adding a trait `view_l` default changed method resolution inside each
marker's `impl ConnL::swap_l(&self)` body (`self.view_l().swap_l()`): on
a concrete `&self` receiver the trait default now wins over the inherent
by-value `view_l`, which recursed (`swap_l → view_l → swap_l`) into a
stack overflow. Fixed by having the trait swap impls call the inherent
const swap by path (`$name::swap_l(*self)`), across all four emitters.
The regression is guarded by the existing law batteries plus a new
`tests/trait_method_api.rs` proving the method form equals the
inherent-view and free-fn forms for every accessor.

### Verification

- `tests/trait_method_api.rs` — method == `view_l()`/`view_r()` ==
  free-fn for every per-side accessor and two-sided helper (proptest over
  `F064F032`), `median` method == free fn on a diagonal i32 triple, and a
  `const` item asserting a value's `swap_l` stays const.
- Full suite green under `--features fixed,time,hifi,uhlc,proptest,macros`
  (1925 lib + 514 + 2664 + 9 integration + 5 new + 108 doctests, 0
  failed), clippy `--all-targets -D warnings` clean, `cargo doc`
  `-D warnings` clean.
- `compile_fail/round_on_l_conn` re-blessed: `round` still rejects a
  one-sided L-value (now for lacking `ConnR` rather than both traits).

### Scope

EXAMPLES.md Example 3 / 7 and the `TDURSECS` module doctest switch to the
direct method form as demonstrations. Deferred: deleting the free fns and
sweeping the remaining internal call sites; `From`/`Into` for `iso!`
markers; the downstream `gitjig-lib` migration.

## Local review (2026-07-06)

**Branch:** plan/2026-07-06-03
**Commits:** 4 (origin/main..plan/2026-07-06-03)
**Reviewer:** Codex (`codex review --base origin/main`)
**Prompt fingerprint:** AGENTS.md=4563f590caa7dbba5ea9eae973fa59182f1a6470 calibration=missing

---

No actionable correctness issues were found in the diff. The trait-method forwarding and marker visibility changes appear consistent with the intended API expansion.

