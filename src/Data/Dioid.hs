{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Dioid where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Maybe
import safe Data.Either
import safe Data.Fixed
import safe Data.Foldable hiding (sum, product)
import safe Data.Group
import safe Data.Int
--import safe Data.List
import safe Data.List.NonEmpty
import safe Data.Magma
import safe Data.Prd
import safe Data.Ord
import safe Data.Semiring
import safe Data.Semigroup
import safe Data.Semigroup.Join
import safe Data.Semigroup.Meet
import safe Data.Semigroup.Additive hiding (Ordered)
import safe Data.Semigroup.Multiplicative as M
import safe Data.Semigroup.Foldable
import safe Data.Semigroup.Multiplicative
import safe Data.Tuple
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic)
import safe GHC.Real hiding (Fractional(..), div, (^^), (^), (%))
import safe Numeric.Natural

import safe Prelude ( Eq(..), Ord(..), Show, Ordering(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, Float, Double)
import safe qualified Prelude as P

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet



-- Generic Predioid
type Ordered = Additive -- TODO expand to newtype

type PredioidLaw a = (Prd a, (Ordered-Semigroup) a, (Multiplicative-Semigroup) a)

-- Generic Dioid
type DioidLaw a = (Prd a, (Ordered-Monoid) a, (Multiplicative-Monoid) a)

-- A constraint kind for topological dioids
--type Topological a = (Dioid a, Kleene a, Yoneda a)



-- | Right pre-dioids and dioids.
--
-- A right-dioid is a semiring with a right-canonical pre-order relation relative to '+':
--
-- @ 
-- a '<=' b '<==>' b == a '+' c
-- a '<=' (a '+' b) '==' 'True'
-- @
--
-- Consequently '<=' is both reflexive and transitive:
--
-- @
-- a '<=' a '==' 'True'
-- a '<=' b && b '<=' c ==> a '<=' c '==' 'True'
-- @
--
-- Finally '<=' is an order relation:
--
-- @(a '=~' b) '<==>' (a '==' b)@
--
-- See 'Data.Semiring.Property'
--
class (Presemiring a, PredioidLaw a) => Predioid a

class (Semiring a, Predioid a) => Dioid a


-- | Evaluate a < https://en.wikipedia.org/wiki/Tropical_semiring min-plus > dioid expression.
--
-- >>> minPlus [[1..4 :: Int], [0..2 :: Int]]
-- 3
minPlus :: (Additive-Monoid) a => Maximal a => Ord a => Functor f => Functor g => Foldable f => Foldable g => f (g a) -> a
minPlus = getMin . evalWith Min

-- | Evaluate a max-plus dioid expression.
--
-- >>> maxPlus [[1..4 :: Int], [0..2 :: Int]]
-- 10
maxPlus :: (Additive-Monoid) a => Minimal a => Ord a => Functor f => Functor g => Foldable f => Foldable g => f (g a) -> a
maxPlus a = b where (Down b) = getMin $ evalWith (Min . Down) a

-- | Evaluate a min-times dioid expression.
--
-- >>> minTimes [[1..4 :: Int], [0..2 :: Int]]
-- 0
minTimes :: (Multiplicative-Monoid) a => Maximal a => Ord a => Functor f => Functor g => Foldable f => Foldable g => f (g a) -> a
minTimes a = b where (Down b) = getMax $ evalWith (Max . Down) a

-- | Evaluate a max-times dioid expression.
--
-- >>> maxTimes [[1..4 :: Int], [0..2 :: Int]]
-- 24
maxTimes :: (Multiplicative-Monoid) a => Minimal a => Ord a => Functor f => Functor g => Foldable f => Foldable g => f (g a) -> a
maxTimes = getMax . evalWith Max

-- Predioids
instance Predioid ()
instance Predioid Bool
instance Predioid Word
instance Predioid Word8
instance Predioid Word16
instance Predioid Word32
instance Predioid Word64
instance Predioid Natural
instance Predioid (Ratio Natural)

-- Idempotent Predioids
instance (Prd a, (Additive-Semigroup) a) => Predioid [a]
instance (Prd a, Prd b, Predioid a, Predioid b) => Predioid (Either a b)
instance (Prd a, Predioid a) => Predioid (Maybe a)


instance Predioid IntSet.IntSet
instance Ord a => Predioid (Set.Set a)
instance (Prd a, Predioid a) => Predioid (IntMap.IntMap a)
instance (Ord k, Prd a, Predioid a) => Predioid (Map.Map k a)
instance (Prd a, Dioid a) => Dioid (IntMap.IntMap a)
instance (Ord k, (Multiplicative-Monoid) k, Prd a, Dioid a) => Dioid (Map.Map k a)

-- Dioids
instance Dioid ()
instance Dioid Bool
instance Dioid Word
instance Dioid Word8
instance Dioid Word16
instance Dioid Word32
instance Dioid Word64
instance Dioid Natural
instance Dioid (Ratio Natural)

--instance Dioid CFloat
--instance Dioid CDouble

-- Idempotent Dioids
instance (Prd a, (Additive-Monoid) a) => Dioid [a]
instance (Prd a, Dioid a) => Dioid (Maybe a)


-- Selective Dioids






-- p. 337 e.g. (N, lcm, (*))
-- 1 is not absorbing for (*) (indeed, for a∈E,a=1,a×1=a /=1). (N, lcm,×) is therefore neither a semiring nor a dioid.

{-
instance Prd a => Prd (V2 a) where
  V2 a b <= V2 d e = a <= d && b <= e

instance Prd a => Prd (V4 a) where
  V4 a b c d <= V4 e f g h = a <= e && b <= f && c <= g && d <= h

instance (Monoid a, Dioid a) => Dioid (V4 a) where
-}

{-
instance Minimal a => Minimal (Dual a) where
  minimal = Dual minimal
instance Maximal a => Maximal (Dual a) where
  maximal = Dual maximal

-}

--instance Prd a => Prd (First a) where First a <= _ = True -- TODO would these instances be legal?
--instance Prd a => Prd (Last a) where Last a <= Last b = a <= b 
{-
instance (Prd a, Ord a, (Max-Monoid) a, (Multiplicative-Semigroup) a) => Predioid (Max a)
instance (Prd a, Ord a, (Min-Monoid) a, (Additive-Semigroup) a) => Predioid (Min a)

instance (Prd a, Ord a, Bounded a, Minimal a, (Max-Monoid) a, (Multiplicative-Monoid) a) => Dioid (Max a)
--instance (Ord a, Bounded a) => Monoid (Min a)
instance (Prd a, Ord a, Bounded a, Maximal a, (Min-Monoid) a, (Additive-Monoid) a) => Dioid (Min a) --WTF remove Bounded
-}

--instance ((Max-Semigroup) a, (Additive-Semigroup) a) => Presemiring (Max a)
instance (Ord a, (Multiplicative-Semigroup) a) => Presemiring (Max a) --MaxTimes
instance (Ord a, (Additive-Semigroup) a) => Presemiring (Min a) --MinPlus

instance (Ord a, Minimal a, (Additive-Monoid) (Max a), (Multiplicative-Monoid) a) => Semiring (Max a)
instance (Ord a, Maximal a, (Additive-Monoid) (Min a), (Additive-Monoid) a) => Semiring (Min a)

instance (Prd a, Ord a, (Multiplicative-Semigroup) a) => Predioid (Max a)
instance (Prd a, Ord a, (Additive-Semigroup) a) => Predioid (Min a)

instance (Ord a, Minimal a, (Additive-Monoid) (Max a), (Multiplicative-Monoid) a) => Dioid (Max a)
instance (Ord a, Maximal a, (Additive-Monoid) (Min a), (Additive-Monoid) a) => Dioid (Min a)

--instance (Ord a, Prd a, Maximal a) => Monoid (Additive (Min a)) where  mempty = pure . pure $ maximal


--instance Dioid (Ratio Integer, Ratio Natural)

{-

--p. 339
-- e.g. (MinPlus (Positive Double), Integer), (MinPlus (Inf Natural), Integer)
instance (Dioid a, Ring b) => Semiring (a, b)
instance (Maximal a, Ord a, Ring b) => Semiring (Min a, 

--p. 336
instance (Predioid a, Ring g) => Presemiring (a, b)


--p. 341
instance Dioid (Double, Positive Double)
--p. 341
instance Dioid (Ratio Integer, Ratio (Positive Natural))


--p. 343
instance Semiring (Double, Nonneg Double) where
  (a1, b1) + (a2, b2) | a1 < a2 || a1 == a2 && b1 > b2 = (a1, b1)
                      | otherwise = (a2, b2)

  (a1, b1) * (a2, b2) = (a1 + b1*a2, b1 * b2)

  one = (zero, one)

instance Dioid (Double, Nonneg Double)
--p. 343


-}





{-


type Positive = Ratio Natural


class (Prd a, Semiring a) => Dioid a where

  -- | A dioid homomorphism from the naturals to /a/.
  fromNatural :: Natural -> a

instance Dioid () where
  fromNatural _ = ()

instance Dioid Bool where
  fromNatural 0 = False
  fromNatural _ = True

instance Dioid Word8 where
  fromNatural = connr w08nat

instance Dioid Word16 where
  fromNatural = connr w16nat

instance Dioid Word32 where
  fromNatural = connr w32nat

instance Dioid Word64 where
  fromNatural = connr w64nat

instance Dioid Natural where
  fromNatural = id

instance Dioid Positive where
  fromNatural x = x :% sunit

instance (Monoid a, Monoid b, Dioid a, Dioid b) => Dioid (a, b) where
  fromNatural x = (fromNatural x, fromNatural x)

instance (Monoid a, Monoid b, Monoid c, Dioid a, Dioid b, Dioid c) => Dioid (a, b, c) where
  fromNatural x = (fromNatural x, fromNatural x, fromNatural x)
-}
