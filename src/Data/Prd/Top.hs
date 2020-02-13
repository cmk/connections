{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Prd.Top where

import Data.Prd
import Data.Prd.Nan
import GHC.Generics (Generic, Generic1)
import Prelude hiding (Ord(..), Bounded)

type Bottom a = Maybe a
type Bound a = Bottom (Top a)
type Lifted a = Nan (Top a)
type Lowered a = Nan (Bottom a)
type Extended a = Nan (Bound a)

data Top a = Fin a | Top
  deriving (Show, Generic, Generic1, Functor)

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

isTop :: Bound a -> Bool
isTop = bound False True (const False)

isBottom :: Bound a -> Bool
isBottom = bound True False (const False)

isFin :: Bound a -> Bool
isFin = bound False False (const True)

fin :: a -> Bound a
fin = Just . Fin

toTop :: Prd a => Minimal b => (a -> b) -> Bound a -> Top b
toTop f = bound (Fin minimal) Top (Fin . f)

toBottom :: Prd a => Maximal b => (a -> b) -> Bound a -> Bottom b
toBottom f = bound Nothing (Just maximal) (Just . f)

topped :: b -> (a -> b) -> Top a -> b
topped _ f (Fin a) = f a
topped b _ Top = b

lifted :: RealFloat b => (a -> b) -> Lifted a -> b
lifted = nanf . topped (1/0)

bound :: b -> b -> (a -> b) -> Bound a -> b
bound b _ _ Nothing = b
bound _ b _ (Just Top) = b
bound _ _ f (Just (Fin a)) = f a

-- | Interpret @'Bound' a@ using the 'BoundLattice' of @a@.
--
-- This map is monotone when /f/ is.
--
bounded :: Bounded b => (a -> b) -> Bound a -> b
bounded = bound minimal maximal

extended :: Bounded b => b -> (a -> b) -> Extended a -> b
extended b f = nan b (bounded f)

-- this is a monotone map
liftTop :: Maximal a => (a -> b) -> a -> Top b
liftTop f = g where
  g i | i =~ maximal = Top
      | otherwise = Fin $ f i

liftTop' :: Maximal a => (a -> b) -> a -> Bound b
liftTop' f a = Just $ liftTop f a

-- This map is a lattice morphism when /f/ is.
liftBottom :: Minimal a => (a -> b) -> a -> Bottom b
liftBottom f = g where
  g i | i =~ minimal = Nothing
      | otherwise = Just $ f i

liftBottom' :: Minimal a => (a -> b) -> a -> Bound b
liftBottom' f = liftBottom (Fin . f)

-- this is a monotone map
liftBound :: Bounded a => (a -> b) -> a -> Bound b
liftBound f = liftBottom (liftTop f)

-- Lift all exceptional values
liftExtended :: Bounded a => Floating a => (a -> b) -> a -> Extended b
liftExtended f = liftNan (liftBound f)
