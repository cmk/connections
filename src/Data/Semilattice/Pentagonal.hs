module Data.Semilattice.Pentagonal where

import Control.Applicative
import Data.Prd
import Data.Prd.Nan
import Data.Connection
import Data.Group
import Data.Magma
import Data.Semilattice
import Data.Semiring
import Data.Semifield

import Prelude hiding (Num(..), Ord(..), Fractional(..))

-- | Lift a 'Semifield' into a non-modular lattice.
--
-- See <https://en.wikipedia.org/wiki/Modular_lattice#Examples>
--
newtype N5 a = N5 { fromN5 :: a } deriving Show

joinN5 :: (Minimal a, Semifield a) => N5 a -> N5 a -> N5 a
joinN5 (N5 x) (N5 y) = case pcompare x y of
  Just LT -> N5 y
  Just EQ -> N5 x
  Just GT -> N5 x
  Nothing -> N5 pinf

meetN5 :: (Minimal a, Semifield a) => N5 a -> N5 a -> N5 a
meetN5 (N5 x) (N5 y) = case pcompare x y of
  Just LT -> N5 x
  Just EQ -> N5 x
  Just GT -> N5 y
  Nothing -> N5 minimal


instance (Minimal a, Semifield a) => Prd (N5 a) where

  -- | 
  -- @ 'anan' '<=' 'pinf' @
  -- @ 'anan' '>=' 'ninf' @
  pcompare (N5 x) (N5 y) | x =~ minimal = Just LT
                         | y =~ minimal = Just GT
                         | x =~ pinf = Just GT
                         | y =~ pinf = Just LT
                         | otherwise    = pcompare x y

instance (Minimal a, Semifield a) => Eq (N5 a) where
  (==) = (=~)

instance (Minimal a, Semifield a) => Minimal (N5 a) where
  minimal = N5 minimal

instance (Bound a, Semifield a) => Maximal (N5 a) where
  maximal = N5 maximal

instance (Minimal a, Semifield a) => Semigroup (Meet (N5 a)) where
  (<>) = liftA2 meetN5 

instance (Minimal a, Semifield a) => Monoid (Meet (N5 a)) where
  mempty = Meet $ N5 pinf

instance (Minimal a, Semifield a) => Semigroup (Join (N5 a)) where
  (<>) = liftA2 joinN5

instance (Minimal a, Semifield a) => Monoid (Join (N5 a)) where
  mempty = Join $ N5 minimal

instance (Minimal a, Semifield a) => Lattice (N5 a)

instance (Additive-Semigroup) a => Semigroup (Additive (N5 a)) where
  (<>) = liftA2 (+)

instance (Additive-Monoid) a => Monoid (Additive (N5 a)) where
  mempty = pure zero
 
instance (Additive-Group) a => Magma (Additive (N5 a)) where
  (<<) = liftA2 (-)

instance (Additive-Group) a => Quasigroup (Additive (N5 a))
instance (Additive-Group) a => Loop (Additive (N5 a))
instance (Additive-Group) a => Group (Additive (N5 a))

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (N5 a)) where
  (<>) = liftA2 (*)

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (N5 a)) where
  mempty = pure one
 
instance (Multiplicative-Group) a => Magma (Multiplicative (N5 a)) where
  (<<) = liftA2 (/)

instance (Multiplicative-Group) a => Quasigroup (Multiplicative (N5 a))
instance (Multiplicative-Group) a => Loop (Multiplicative (N5 a))
instance (Multiplicative-Group) a => Group (Multiplicative (N5 a))

instance Presemiring a => Presemiring (N5 a)
instance Semiring a => Semiring (N5 a)
instance Ring a => Ring (N5 a)
instance Semifield a => Semifield (N5 a)
instance Field a => Field (N5 a)
