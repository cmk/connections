{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Semilattice.Top where

import Control.Applicative
import Data.Data (Data, Typeable)
import Data.Prd
import Data.Prd.Nan
import Data.Connection
import Data.Semilattice
import Data.Semifield
import GHC.Generics (Generic, Generic1)
import Data.Float

import Prelude hiding (Ord(..), Bounded)

type Bottom a = Maybe a
type Bounded a = Bottom (Top a)
type Lifted a = Nan (Top a)
type Lowered a = Nan (Bottom a)
type Extended a = Nan (Bounded a)

data Top a = Fin a | Top
  deriving (Show, Generic, Generic1, Functor, Foldable, Traversable)

-- analagous to Maybe Semigroup instance
instance Semigroup a => Semigroup (Top a) where
  Top <> _ = Top
  _ <> Top = Top
  Fin x <> Fin y = Fin $ x <> y

instance Monoid a => Monoid (Top a) where
  mempty = Fin mempty

instance Prd a => Prd (Top a) where
  _ <= Top = True
  Top <= _ = False
  Fin a <= Fin b = a <= b

instance Minimal a => Minimal (Top a) where
  minimal = Fin minimal

instance Prd a => Maximal (Top a) where
  maximal = Top

-- analagous to Maybe (Meet-Semigroup) instance
instance (Join-Semigroup) a => Semigroup (Join (Top a)) where
  Join Top <> _                      = Join Top
  Join (x@Fin{}) <> Join Top      = Join Top
  Join (Fin x) <> Join (Fin y) = Join . Fin $ x ∨ y

-- analagous to Maybe (Meet-Monoid) instance
instance (Join-Monoid) a => Monoid (Join (Top a)) where
  mempty = Join $ Fin bottom

instance (Meet-Semigroup) a => Semigroup (Meet (Top a)) where
  Meet (Fin x) <> Meet (Fin y) = Meet . Fin $ x ∧ y
  Meet (x@Fin{}) <> _             = Meet x
  Meet Top <> y                      = y

instance (Meet-Semigroup) a => Monoid (Meet (Top a)) where
  mempty = Meet Top

instance Lattice a => Lattice (Top a)

{-

instance Covered (Top Float) where
  Bounded x <. Bounded y = shiftf 1 x == y

instance Graded (Top Float) where
  rank (Bounded x) | ind x = 0
                   | otherwise = r where
    x' = floatInt32 x
    y' = floatInt32 ninf
    r = fromIntegral . abs $ x' - y'
-}


isTop :: Bounded a -> Bool
isTop = bounded False (const False) True

isBottom :: Bounded a -> Bool
isBottom = bounded True (const False) False

isFin :: Bounded a -> Bool
isFin = bounded False (const True) False

fin :: a -> Bounded a
fin = Just . Fin

toTop :: Prd a => LowerBoundedLattice b => (a -> b) -> Bounded a -> Top b
toTop f = bounded (Fin bottom) (Fin . f) Top

toBottom :: Prd a => UpperBoundedLattice b => (a -> b) -> Bounded a -> Bottom b
toBottom f = bounded Nothing (Just . f) (Just top)

topped :: (a -> b) -> b -> Top a -> b
topped f _ (Fin a) = f a
topped _ b Top = b

lifted :: Semifield b => (a -> b) -> Lifted a -> b
lifted f = nan' $ topped f pinf 

bounded :: b -> (a -> b) -> b -> Bounded a -> b
bounded b _ _ Nothing = b
bounded _ f _ (Just (Fin a)) = f a
bounded _ _ b (Just Top) = b

-- | Interpret @'Bounded' a@ using the 'BoundedLattice' of @a@.
--
-- This map is monotone when /f/ is.
--
bounded' :: BoundedLattice b => (a -> b) -> Bounded a -> b
bounded' f = bounded bottom f top

extended :: Field b => (a -> b) -> Extended a -> b
extended f = nan' $ bounded ninf f pinf

-- this is a monotone map
liftTop :: Maximal a => (a -> b) -> a -> Top b
liftTop f = g where
  g i | i =~ maximal = Top
      | otherwise = Fin $ f i

liftTop' :: Maximal a => (a -> b) -> a -> Bounded b
liftTop' f a = Just $ liftTop f a

-- This map is a lattice morphism when /f/ is.
liftBottom :: Minimal a => (a -> b) -> a -> Bottom b
liftBottom f = g where
  g i | i =~ minimal = Nothing
      | otherwise = Just $ f i

liftBottom' :: Minimal a => (a -> b) -> a -> Bounded b
liftBottom' f = liftBottom (Fin . f)

-- this is a monotone map
liftBounded :: Bound a => (a -> b) -> a -> Bounded b
liftBounded f = liftBottom (liftTop f)

-- Lift all exceptional values
liftExtended :: Bound a => Field a => (a -> b) -> a -> Extended b
liftExtended f = liftNan (liftBounded f)