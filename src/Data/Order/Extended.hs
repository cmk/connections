{-# Language Safe                #-}
{-# Language DeriveFunctor       #-}
{-# Language DeriveGeneric       #-}

module Data.Order.Extended (
  -- * Lattice extensions
    type Lifted
  , type Lowered
  , Extended(..)
  , extended
  --, retract
  -- * Lattice Extensions
  , liftMaybe
  , liftEitherL
  , liftEitherR
  , liftExtended
) where

import safe Data.Order
import safe Data.Order.Syntax
import safe GHC.Generics
import safe Prelude hiding (Eq(..), Ord(..),Bounded)

type Lifted = Either ()

type Lowered a = Either a ()

-- | Add a bottom and top to a lattice.
--
-- The top is the absorbing element for the join, and the bottom is the absorbing
-- element for the meet.
--
data Extended a = Bottom | Extended a | Top
  deriving ( Eq, Ord, Show, Generic, Functor, Generic1 )

-- | Eliminate an 'Extended'.
extended :: b -> b -> (a -> b) -> Extended a -> b
extended b _ _ Bottom       = b
extended _ t _ Top          = t
extended _ _ f (Extended x) = f x

-------------------------------------------------------------------------------
-- Lattice extensions
-------------------------------------------------------------------------------


{-
lifts :: Minimal a => Eq a => (a -> b) -> a -> Lifted b
lifts = liftEitherL (== minimal)

lifted :: Minimal b => (a -> b) -> Lifted a -> b
lifted f = either (const minimal) f

lowered :: Maximal b => (a -> b) -> Lowered a -> b
lowered f = either f (const maximal)

lowers :: Maximal a => Eq a => (a -> b) -> a -> Lowered b
lowers = liftEitherR (== maximal) 
-}

liftMaybe :: (a -> Bool) -> (a -> b) -> a -> Maybe b
liftMaybe p f = g where
  g i | p i = Nothing
      | otherwise = Just $ f i

liftEitherL :: (a -> Bool) -> (a -> b) -> a -> Lifted b
liftEitherL p f = g where
  g i | p i = Left ()
      | otherwise = Right $ f i

liftEitherR :: (a -> Bool) -> (a -> b) -> a -> Lowered b
liftEitherR p f = g where
  g i | p i = Right ()
      | otherwise = Left $ f i

liftExtended :: (a -> Bool) -> (a -> Bool) -> (a -> b) -> a -> Extended b
liftExtended p q f = g where
  g i | p i = Bottom
      | q i = Top
      | otherwise = Extended $ f i

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Preorder a => Preorder (Extended a) where
  _ <~ Top = True
  Top <~ _ = False
  Bottom <~ _ = True
  _ <~ Bottom = False
  Extended x <~ Extended y = x <~ y

{-
instance Universe a => Universe (Extended a) where
    universe = Top : Bottom : map Extended universe
instance Finite a => Finite (Extended a) where
    universeF = Top : Bottom : map Extended universeF
    cardinality = fmap (2 +) (retag (cardinality :: Tagged a Natural))
-}
