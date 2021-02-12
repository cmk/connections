{-# Language Safe                #-}

module Data.Connection (
  module Data.Connection.Conn,
  module Data.Connection.Class,
) where


import safe Data.Connection.Conn
import safe Data.Connection.Class

{- 0.2.0 TODO

 - update changelog
 - add package-level documentation
 - fix doctests or remove notation and cabal target
 - add buildkite or circleci CI, lock master
 - combine Double.hs & Float.hs?
 
 - subst Precision for Extended?
     data Precision a = Negative (Maybe a) | Precise a | Positive (Maybe a) ?
 - add time / clock connections
 - add scientific?

-}
