{-# LANGUAGE DeriveFunctor       #-}
module Data.Semilattice.MaxMin where

import Control.Applicative
import Data.Prd
import Data.Prd.Nan
import Data.Connection
import Data.Semilattice
import Data.Semifield

import Prelude hiding ((<=))

newtype MaxMin a = MaxMin { unMaxMin :: a } deriving (Show, Functor)

instance Applicative MaxMin where
  pure = MaxMin
  MaxMin f <*> MaxMin a = MaxMin (f a)

instance Prd a => Prd (MaxMin a) where
  MaxMin a <= MaxMin b = a <= b

instance Prd a => Eq (MaxMin a) where
  (==) = (=~)

instance Ord a => Semigroup (Join (MaxMin a)) where
  (<>) = liftA2 . liftA2 $ max

instance (Ord a, Minimal a) => Monoid (Join (MaxMin a)) where
  mempty = pure . pure $ minimal

instance Ord a => Semigroup (Meet (MaxMin a)) where
  (<>) = liftA2 . liftA2 $ min

instance (Ord a, Maximal a) => Monoid (Meet (MaxMin a)) where
  mempty = pure . pure $ maximal

instance (Ord a, Bound a) => Lattice (MaxMin a)
