# Revision history for connections

## 0.3.2  -- 2021-xx-xx

* Add left-hand float and double connections.

## 0.3.1  -- 2021-05-30

* Add `Data.Connection.Time`.
* Add float-word connections.
* Move infix join/meet to `Data.Lattice`
* Re-organize top-level exports.
* New dependencies on `time` and `extended-reals`.

## 0.3.0  -- 2021-03-14

* Add `Data.Connection.Fixed`.

## 0.2.0  -- 2021-02-21

* Change integral connection instances to non-shifting behavior.
* Move all one-sided `Connection` instances to `Connection 'L`.
* Consolidate floating point utilities into one module.
* Rename some functions in `Class.hs` and `Conn.hs` for clarity.
* Move `<` and `>` to `Syntax.hs`.
* Remove niche instances w/ upstream dependencies.
* Add misc new instances.

## 0.1.0  -- 2020-07-07

* Unify `Connection` and `Triple` into a single class
* Add `Heyting`, `Symmetric`, and `Boolean` algebras
* Add misc new instances

## 0.0.3  -- 2020-02-17

* `Data.Connection.Float` : float utils
* `Data.Connection.Ratio` : add rational connections

