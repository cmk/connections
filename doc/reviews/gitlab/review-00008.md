# MR !8 — Plan 03: Bi-Heyting + Symmetric + Boolean trait methods and properties

## Summary

Flesh out the lattice trait hierarchy with provided methods and port
all property test functions from `Data.Lattice` / `Data.Lattice.Property`.

### What changed

- **Trait methods**: `Heyting` gains `neg`, `mid` (provided).
  `Coheyting` gains `coimp` (renamed from `sub`), `coneg`, `comid`
  (provided). `Symmetric` gains `xor` (provided). Free functions
  `converse_l`, `converse_r` added.

- **Documentation**: Full Haddock-equivalent doc comments ported from
  `Data.Lattice` for every trait (`Join`, `Meet`, `Heyting`,
  `Coheyting`, `Symmetric`, `Boolean`) and every method/function,
  including law listings.

- **Property test functions**: 55+ generic predicates in `property.rs`
  parameterized over trait bounds. Covers Heyting (h0–h17), Coheyting
  (c0–c20), bi-Heyting (s1), Symmetric (symmetric2–symmetric13), and
  Boolean (boolean0–boolean6). Downstream crates instantiate them in
  `proptest!` blocks with their own strategies.

### Why

The downstream `agogo` crate (Plan 16) implemented bi-Heyting algebra
on its Grid lattice using standalone functions. Promoting the derived
operations into traits lets any implementer get them for free, and
the generic property functions make it trivial to verify new
implementations.
