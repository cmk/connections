# Revision history for connections

## 0.0.3  -- 2020-02-17

* `Data.Connection.Float` : float utils
* `Data.Connection.Ratio` : add rational connections

## 0.1.0  -- 2020-07-07

* Unify `Connection` and `Triple` into a single class
* Add `Heyting`, `Symmetric`, and `Boolean` algebras
* Add misc new instances

## 0.2.0  -- 2021-02-21

* Change integral connection instances to non-shifting behavior.
* Move all one-sided `Connection` instances to `Connection 'L`.
* Consolidate floating point utilities into one module.
* Rename some functions in `Class.hs` and `Conn.hs` for clarity.
* Move `<` and `>` to `Syntax.hs`.
* Remove niche instances w/ upstream dependencies.
* Add misc new instances.
