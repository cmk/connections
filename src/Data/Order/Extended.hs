{-# Language Safe                #-}
{-# Language DeriveFunctor       #-}
{-# Language DeriveGeneric       #-}

module Data.Order.Extended (
  -- * Lattice extensions
    type Lifted
  , type Lowered
  , Extended(..)
  , extended
  -- * Lattice Extensions
  , lifts
  , lifted
  , lowers
  , lowered
  , liftEitherL
  , liftEitherR
  , liftExtended
) where

import safe Control.Applicative (liftA2)
import safe Data.Order
import safe Data.Lattice
import safe Data.Int
import safe GHC.Generics
import safe Prelude hiding (Ord(..),Bounded,ceiling,floor)
import safe qualified Prelude as P

type Lifted a = Either () a

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

lifts :: (Join-Monoid) a => Eq a => (a -> b) -> a -> Lifted b
lifts = liftEitherL (== bottom)

lifted :: (Join-Monoid) b => (a -> b) -> Lifted a -> b
lifted f = either (const bottom) f

lowered :: (Meet-Monoid) b => (a -> b) -> Lowered a -> b
lowered f = either f (const top)

lowers :: (Meet-Monoid) a => Eq a => (a -> b) -> a -> Lowered b
lowers = liftEitherR (== top) 

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

instance Semigroup (Join a) => Semigroup (Join (Extended a)) where
  (<>) = liftA2 joinExtended

instance Semigroup (Meet a) => Semigroup (Meet (Extended a)) where
  (<>) = liftA2 meetExtended

instance Semigroup (Join a) => Monoid (Join (Extended a)) where
  mempty = pure Bottom

instance Semigroup (Meet a) => Monoid (Meet (Extended a)) where
  mempty = pure Top

instance Lattice a => Lattice (Extended a)
instance Lattice a => Bounded (Extended a)
instance Distributive a => Distributive (Extended a)

{-
instance Universe a => Universe (Extended a) where
    universe = Top : Bottom : map Extended universe
instance Finite a => Finite (Extended a) where
    universeF = Top : Bottom : map Extended universeF
    cardinality = fmap (2 +) (retag (cardinality :: Tagged a Natural))
-}

joinExtended :: (Join-Semigroup) a => Extended a -> Extended a -> Extended a
joinExtended Top          _            = Top
joinExtended _            Top          = Top
joinExtended (Extended x) (Extended y) = Extended (x \/ y)
joinExtended Bottom       y            = y
joinExtended x            Bottom       = x

meetExtended :: (Meet-Semigroup) a => Extended a -> Extended a -> Extended a
meetExtended Top          y            = y
meetExtended x            Top          = x
meetExtended (Extended x) (Extended y) = Extended (x /\ y)
meetExtended Bottom       _            = Bottom
meetExtended _            Bottom       = Bottom

