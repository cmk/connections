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

module Data.Semigroup.Meet (
    type (-)
  , module Data.Semigroup.Meet
) where

import safe Data.Ord
import safe Data.Prd
import safe Control.Applicative
import safe Data.Bool
import safe Data.Maybe
import safe Data.Either
import safe Data.Foldable as Foldable (Foldable, foldr', foldl')
import safe Data.List
import safe Data.List.NonEmpty
import safe Data.Semigroup
import safe Data.Semigroup.Additive
import safe Data.Semigroup.Multiplicative
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Tuple
import safe GHC.Generics (Generic)
--import safe Prelude ( Eq, Ord, Show, Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, Float, Double)
import safe qualified Prelude as P

import safe Prelude ( Eq(..), Ord, Show, Ordering(..), Bounded(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, Float, Double)
import safe qualified Prelude as P

import safe Numeric.Natural
import safe Data.Word
import safe Data.Int
import safe Data.Fixed
import safe Data.Ratio

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Sequence as Seq

infixr 6 ∧ 

-- | Meet operation on a semilattice.
--
-- >>> (> (0::Int)) ∧ ((< 10) ∨ (== 15)) $ 15
-- True
--
(∧) :: (Meet-Semigroup) a => a -> a -> a
a ∧ b = unMeet (Meet a <> Meet b)
{-# INLINE (∧) #-}

top :: (Meet-Monoid) a => a
top = unMeet mempty
{-# INLINE top #-}

newtype Meet a = Meet { unMeet :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Meet where
  pure = Meet
  Meet f <*> Meet a = Meet (f a)

-- >>> Min 1 ∧ Min 2 :: Min Int
-- Min {getMin = 1}
instance Semigroup (Min a) => Semigroup (Meet (Min a)) where
  (<>) = liftA2 (<>)

instance (Meet-Semigroup) (Min a) => Semigroup (Additive (Min a)) where
  (<>) = liftA2 (∧) 

instance (Meet-Monoid) (Min a) => Monoid (Additive (Min a)) where
  mempty = pure top

-- workaround for poorly specified entailment: instance (Ord a, Bounded a) => Monoid (Min a)
-- >>> zero :: Min Natural
-- Min {getMin = 0}
instance (Maximal a, Semigroup (Min a)) => Monoid (Meet (Min a)) where
  mempty = pure $ Min maximal

---------------------------------------------------------------------
-- Semigroup Instances
---------------------------------------------------------------------

--instance ((Meet-Semigroup) a, Maximal a) => Monoid (Meet a) where
--  mempty = Meet maximal


-- MaxTimes Predioid

instance (Meet-Semigroup) a => Semigroup (Meet (Max a)) where
  Meet a <> Meet b = Meet $ liftA2 (∧) a b

-- MaxTimes Dioid
instance (Meet-Monoid) a => Monoid (Meet (Max a)) where
  mempty = Meet $ pure top

instance ((Meet-Semigroup) a, (Meet-Semigroup) b) => Semigroup (Meet (a, b)) where
  Meet (x1, y1) <> Meet (x2, y2) = Meet (x1 ∧ x2, y1 ∧ y2)

instance (Meet-Semigroup) b => Semigroup (Meet (a -> b)) where
  (<>) = liftA2 . liftA2 $ (∧)
  {-# INLINE (<>) #-}

instance (Meet-Monoid) b => Monoid (Meet (a -> b)) where
  mempty = pure . pure $ top

instance (Meet-Semigroup) a => Semigroup (Meet (Maybe a)) where
  Meet Nothing  <> _             = Meet Nothing
  Meet (x@Just{}) <> Meet Nothing   = Meet Nothing
  Meet (Just x) <> Meet (Just y) = Meet . Just $ x ∧ y

  -- Mul a <> Mul b = Mul $ liftA2 (∧) a b

instance (Meet-Monoid) a => Monoid (Meet (Maybe a)) where
  mempty = Meet $ pure top

instance ((Meet-Semigroup) a, (Meet-Semigroup) b) => Semigroup (Meet (Either a b)) where
  Meet (Right x) <> Meet (Right y) = Meet . Right $ x ∧ y
  Meet(x@Right{}) <> y     = y
  Meet (Left x) <> Meet (Left y)  = Meet . Left $ x ∧ y
  Meet (x@Left{}) <> _     = Meet x

instance Ord a => Semigroup (Meet (Set.Set a)) where
  (<>) = liftA2 Set.intersection 

instance (Ord k, (Meet-Semigroup) a) => Semigroup (Meet (Map.Map k a)) where
  (<>) = liftA2 (Map.intersectionWith (∧))

instance (Meet-Semigroup) a => Semigroup (Meet (IntMap.IntMap a)) where
  (<>) = liftA2 (IntMap.intersectionWith (∧))

instance Semigroup (Meet IntSet.IntSet) where
  (<>) = liftA2 IntSet.intersection 

{-
instance (Ord k, (Meet-Monoid) k, (Meet-Monoid) a) => Monoid (Meet (Map.Map k a)) where
  mempty = Meet $ Map.singleton top top

instance (Meet-Monoid) a => Monoid (Meet (IntMap.IntMap a)) where
  mempty = Meet $ IntMap.singleton 0 top --TODO check
-}

{-


instance Monoid a => Semiring (Seq.Seq a) where
  (*) = liftA2 (<>)
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ Seq.singleton mempty

instance (Ord k, Monoid k, Monoid a) => Semiring (Map.Map k a) where
  xs * ys = foldMap (flip Map.map xs . (<>)) ys
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ Map.singleton mempty mempty

instance Monoid a => Semiring (IntMap.IntMap a) where
  xs * ys = foldMap (flip IntMap.map xs . (<>)) ys
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ IntMap.singleton 0 mempty
-}

{-
instance Semigroup (Meet ()) where
  _ <> _ = pure ()
  {-# INLINE (<>) #-}

instance Monoid (Meet ()) where
  mempty = pure ()
  {-# INLINE mempty #-}

instance Semigroup (Meet Bool) where
  a <> b = (P.&&) <$> a <*> b
  {-# INLINE (<>) #-}

instance Monoid (Meet Bool) where
  mempty = pure True
  {-# INLINE mempty #-}
-}

#define deriveMeetSemigroup(ty)             \
instance Semigroup (Meet ty) where {        \
   a <> b = (P.min) <$> a <*> b             \
;  {-# INLINE (<>) #-}                      \
}

deriveMeetSemigroup(())
deriveMeetSemigroup(Bool)

deriveMeetSemigroup(Int)
deriveMeetSemigroup(Int8)
deriveMeetSemigroup(Int16)
deriveMeetSemigroup(Int32)
deriveMeetSemigroup(Int64)
deriveMeetSemigroup(Integer)

deriveMeetSemigroup(Word)
deriveMeetSemigroup(Word8)
deriveMeetSemigroup(Word16)
deriveMeetSemigroup(Word32)
deriveMeetSemigroup(Word64)
deriveMeetSemigroup(Natural)

deriveMeetSemigroup(Uni)
deriveMeetSemigroup(Deci)
deriveMeetSemigroup(Centi)
deriveMeetSemigroup(Milli)
deriveMeetSemigroup(Micro)
deriveMeetSemigroup(Nano)
deriveMeetSemigroup(Pico)

deriveMeetSemigroup(Rational)
deriveMeetSemigroup((Ratio Natural))

#define deriveMeetMonoid(ty)                \
instance Monoid (Meet ty) where {           \
   mempty = pure maximal                    \
;  {-# INLINE mempty #-}                    \
}

deriveMeetMonoid(())
deriveMeetMonoid(Bool)

deriveMeetMonoid(Int)
deriveMeetMonoid(Int8)
deriveMeetMonoid(Int16)
deriveMeetMonoid(Int32)
deriveMeetMonoid(Int64)

deriveMeetMonoid(Word)
deriveMeetMonoid(Word8)
deriveMeetMonoid(Word16)
deriveMeetMonoid(Word32)
deriveMeetMonoid(Word64)
