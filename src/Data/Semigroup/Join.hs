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

module Data.Semigroup.Join where

import Control.Applicative
import Data.Bool
import Data.Maybe
import Data.Either
import Data.Foldable hiding (sum)
import Data.List
import Data.List.NonEmpty
import Data.Ord
import Data.Prd
import Data.Semigroup
import Data.Semigroup.Additive
import Data.Semigroup.Meet
import Data.Semigroup.Foldable
import Data.Semigroup.Multiplicative
import Data.Tuple
import GHC.Generics (Generic)

import Numeric.Natural
import Data.Word
import Data.Int
import Data.Fixed
import Data.Ratio

import Prelude ( Eq(..), Ord(..), Show, Ordering(..), Bounded(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, Float, Double)
import qualified Prelude as P

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet

infixr 5 ∨

-- | Join operation on a semilattice.
--
-- >>> (> (0::Int)) ∧ ((< 10) ∨ (== 15)) $ 10
-- False
--
-- >>> IntSet.fromList [1..5] ∧ IntSet.fromList [2..5]
-- fromList [2,3,4,5]
(∨) :: (Join-Semigroup) a => a -> a -> a
a ∨ b = unJoin (Join a <> Join b)
{-# INLINE (∨) #-}

bottom :: (Join-Monoid) a => a
bottom = unJoin mempty
{-# INLINE bottom #-}

type JoinSemilattice a = (Prd a, (Join-Semigroup) a)

-- | The partial ordering induced by the join-semilattice structure.
--
--
-- Normally when /a/ implements 'Prd' we should have:
-- @ 'joinLeq' x y ≡ x '<=' y @
--
joinLeq :: Eq a => (Join-Semigroup) a => a -> a -> Bool
joinLeq x y = x ∨ y == y

-- | The partial ordering induced by the join-semilattice structure.
--
-- Normally when /a/ implements 'Prd' we should have:
-- @ 'joinGeq' x y ≡ x '>=' y @
--
joinGeq :: Eq a => (Join-Semigroup) a => a -> a -> Bool
joinGeq x y = x ∨ y == x

-- | Partial version of 'Data.Ord.compare'.
--
-- Normally when /a/ implements 'Prd' we should have:
-- @ 'pcompareJoin' x y ≡ 'pcompare' x y @
--
pcompareJoin :: Eq a => (Join-Semigroup) a => a -> a -> Maybe Ordering
pcompareJoin x y
  | x == y = Just EQ
  | x ∨ y == y && x /= y = Just LT
  | x ∨ y == x && x /= y = Just GT
  | otherwise = Nothing

-- | A commutative 'Semigroup' under '∨'.
newtype Join a = Join { unJoin :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Join where
  pure = Join
  Join f <*> Join a = Join (f a)

-- >>> Down True ∨ Down False
-- Down False
instance (Meet-Semigroup) a => Semigroup (Join (Down a)) where
  (<>) = liftA2 . liftA2 $ (∧) 

-- >>> bottom :: Down Bool
-- Down True
instance (Meet-Monoid) a => Monoid (Join (Down a)) where
  mempty = pure . pure $ top

-- >>> Down True ∧ Down False
-- Down True
instance (Join-Semigroup) a => Semigroup (Meet (Down a)) where
  (<>) = liftA2 . liftA2 $ (∨) 

-- >>> top :: Down Bool
-- Down False
instance (Join-Monoid) a => Monoid (Meet (Down a)) where
  mempty = pure . pure $ bottom


instance Semigroup (Max a) => Semigroup (Join (Max a)) where
  (<>) = liftA2 (<>)

instance (Join-Semigroup) (Max a) => Semigroup (Additive (Max a)) where
  (<>) = liftA2 (∨)

instance (Join-Monoid) (Max a) => Monoid (Additive (Max a)) where
  mempty = pure bottom

-- workaround for poorly specified entailment: instance (Ord a, Bounded a) => Monoid (Max a)
instance (Minimal a, Semigroup (Max a)) => Monoid (Join (Max a)) where
  mempty = pure $ Max minimal

---------------------------------------------------------------------
-- Idempotent and selective instances
---------------------------------------------------------------------

{-
instance Ord a => Semigroup (Join (Down a)) where
  (<>) = liftA2 . liftA2 $ (∨)

instance (Join-Monoid) a => Monoid (Join (Down a)) where
  mempty = pure . pure $ bottom
-}


{-
instance (Join-Semigroup) a => Semigroup (Join (Dual a)) where
  (<>) = liftA2 . liftA2 $ flip (∨)

instance (Join-Monoid) a => Monoid (Join (Dual a)) where
  mempty = pure . pure $ bottom



instance (Join-Semigroup) a => Semigroup (Join (Down a)) where
  (<>) = liftA2 . liftA2 $ (∨) 

instance (Join-Monoid) a => Monoid (Join (Down a)) where
  --Join (Down a) <> Join (Down b)
  mempty = pure . pure $ bottom

instance Semigroup (Max a) => Semigroup (Join (Max a)) where
  (<>) = liftA2 (<>)

-- MinPlus Predioid
-- >>> Min 1  `mul`  Min 2 :: Min Int
-- Min {getMin = 3}
instance (Join-Semigroup) a => Semigroup (Multiplicative (Min a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 (∨) a b

-- MinPlus Dioid
instance (Join-Monoid) a => Monoid (Multiplicative (Min a)) where
  mempty = Multiplicative $ pure bottom
-}


--instance ((Join-Semigroup) a, Minimal a) => Monoid (Join a) where
--  mempty = Join minimal

-- instance (Meet-Monoid) (Down a) => Monoid (Meet (Down a)) where mempty = Down <$> mempty

instance ((Join-Semigroup) a, (Join-Semigroup) b) => Semigroup (Join (a, b)) where
  Join (x1, y1) <> Join (x2, y2) = Join (x1 ∨ x2, y1 ∨ y2)

instance (Join-Semigroup) a => Semigroup (Join (Maybe a)) where
  Join (Just x) <> Join (Just y) = Join . Just $ x ∨ y
  Join (x@Just{}) <> _           = Join x
  Join Nothing  <> y             = y

instance (Join-Semigroup) a => Monoid (Join (Maybe a)) where
  mempty = Join Nothing

instance ((Join-Semigroup) a, (Join-Semigroup) b) => Semigroup (Join (Either a b)) where
  Join (Right x) <> Join (Right y) = Join . Right $ x ∨ y

  Join(x@Right{}) <> _     = Join x
  Join (Left x)  <> Join (Left y)  = Join . Left $ x ∨ y
  Join (Left _)  <> y     = y

instance Ord a => Semigroup (Join (Set.Set a)) where
  (<>) = liftA2 Set.union 

instance (Ord k, (Join-Semigroup) a) => Semigroup (Join (Map.Map k a)) where
  (<>) = liftA2 (Map.unionWith (∨))

instance (Join-Semigroup) a => Semigroup (Join (IntMap.IntMap a)) where
  (<>) = liftA2 (IntMap.unionWith (∨))

instance Semigroup (Join IntSet.IntSet) where
  (<>) = liftA2 IntSet.union 

instance Monoid (Join IntSet.IntSet) where
  mempty = Join IntSet.empty

instance (Join-Semigroup) a => Monoid (Join (IntMap.IntMap a)) where
  mempty = Join IntMap.empty

instance Ord a => Monoid (Join (Set.Set a)) where
  mempty = Join Set.empty

instance (Ord k, (Join-Semigroup) a) => Monoid (Join (Map.Map k a)) where
  mempty = Join Map.empty


#define deriveJoinSemigroup(ty)             \
instance Semigroup (Join ty) where {        \
   a <> b = (P.max) <$> a <*> b             \
;  {-# INLINE (<>) #-}                      \
}

deriveJoinSemigroup(())
deriveJoinSemigroup(Bool)

deriveJoinSemigroup(Int)
deriveJoinSemigroup(Int8)
deriveJoinSemigroup(Int16)
deriveJoinSemigroup(Int32)
deriveJoinSemigroup(Int64)
deriveJoinSemigroup(Integer)

deriveJoinSemigroup(Word)
deriveJoinSemigroup(Word8)
deriveJoinSemigroup(Word16)
deriveJoinSemigroup(Word32)
deriveJoinSemigroup(Word64)
deriveJoinSemigroup(Natural)

deriveJoinSemigroup(Uni)
deriveJoinSemigroup(Deci)
deriveJoinSemigroup(Centi)
deriveJoinSemigroup(Milli)
deriveJoinSemigroup(Micro)
deriveJoinSemigroup(Nano)
deriveJoinSemigroup(Pico)


#define deriveJoinMonoid(ty)                \
instance Monoid (Join ty) where {           \
   mempty = pure minimal                    \
;  {-# INLINE mempty #-}                    \
}

deriveJoinMonoid(())
deriveJoinMonoid(Bool)

deriveJoinMonoid(Int)
deriveJoinMonoid(Int8)
deriveJoinMonoid(Int16)
deriveJoinMonoid(Int32)
deriveJoinMonoid(Int64)

deriveJoinMonoid(Word)
deriveJoinMonoid(Word8)
deriveJoinMonoid(Word16)
deriveJoinMonoid(Word32)
deriveJoinMonoid(Word64)
deriveJoinMonoid(Natural)
