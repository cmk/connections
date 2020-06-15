{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Lattice (
  -- * Constraint kinds
    type (-)
  , type Semilattice
  , type LatticeLaw
  , type BoundedLaw
  -- * Lattices
  , Lattice(..)
  , (\/), (/\)
  , join, meet
  , joinWith, meetWith
  -- ** Bounded lattices
  , type LowerBounded
  , type UpperBounded
  , Bounded(..)
  , bottom, top
  , join1, meet1
  , joinWith1, meetWith1
  -- ** Distributive lattices
  , Distributive(..)
  -- * Semilattices
  , Join(..), Meet(..)
) where

import safe Control.Applicative
import safe Data.Bool hiding (not)
import safe Data.Either
import safe Data.Foldable
import safe Data.Functor.Apply
import safe Data.Functor.Contravariant
import safe Data.Order
import safe Data.Int
import safe Data.Maybe
import safe Data.Semigroup
import safe Data.Semigroup.Foldable
import safe Data.Semigroup.Join
import safe Data.Universe.Class (Finite(..))
import safe Data.Word
import safe GHC.Generics (Generic, Generic1)
import safe GHC.Real (Ratio(..))
import safe Numeric.Natural
import safe Prelude hiding (Ord(..),Bounded)
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set

-------------------------------------------------------------------------------
-- Lattices
-------------------------------------------------------------------------------

-- | Lattices.
--
-- A lattice is a partially ordered set in which every two elements have a unique join 
-- (least upper bound or supremum) and a unique meet (greatest lower bound or infimum). 
--
-- /Associativity/
--
-- @
-- x '\/' (y '\/' z) = (x '\/' y) '\/' z
-- x '/\' (y '/\' z) = (x '/\' y) '/\' z
-- @
--
-- /Commutativity/
--
-- @
-- x '\/' y = y '\/' x
-- x '/\' y = y '/\' x
-- @
--
-- /Idempotency/
--
-- @
-- x '\/' x = x
-- x '/\' x = x
-- @
--
-- < http://en.wikipedia.org/wiki/Absorption_law /Absorption/ >
--
-- @
-- (x '\/' y) '/\' y = y
-- (x '/\' y) '\/' y = y
-- @
--
-- Note that distributivity is _not_ a requirement for a lattice.
--
-- See <http://en.wikipedia.org/wiki/Lattice_(order)>.
--
class (Preorder a, LatticeLaw a) => Lattice a where

    -- | Reduce a free lattice expression:
    -- 
    -- > (a11 /\ ... /\ a1m) \/ (a21 /\ ... /\ a2n) \/ ...
    --
    reduce1 :: (Foldable1 f, Functor f) => f (f a) -> a
    reduce1 = join1 . fmap meet1
    {-# INLINE reduce1 #-}

-------------------------------------------------------------------------------
-- Bounded lattices
-------------------------------------------------------------------------------

type LowerBounded a = (Lattice a, (Join-Monoid) a)

type UpperBounded a = (Lattice a, (Meet-Monoid) a)

-- | Bounded lattices.
--
-- A bounded lattice is a lattice with two neutral elements wrt join and meet
-- operations:
--
-- /Neutrality/
--
-- @
-- x '\/' 'bottom' = x
-- x '/\' 'top' = x
-- @
--
-- See < https://en.wikipedia.org/wiki/Lattice_(order)#Bounded_lattice >.
--
class (Lattice a, BoundedLaw a) => Bounded a where

    -- | Reduce a free bounded lattice expression.
    -- 
    -- >>> reduce [[1, 2], [3, 4 :: Int]] -- 1 /\ 2 \/ 3 /\ 4
    -- 3
    -- >>> reduce $ sequence [[1, 2], [3, 4 :: Int]] -- (1 \/ 2) /\ (3 \/ 4)
    -- 2
    --
    reduce :: (Foldable f, Functor f) => f (f a) -> a
    reduce = join . fmap meet
    {-# INLINE reduce #-}

-------------------------------------------------------------------------------
-- Distributive lattices
-------------------------------------------------------------------------------

-- | Distributive lattices.
--
-- Distributive lattices obey the two (equivalent) additional laws: 
--
-- @ 
-- x '/\' (y '\/' z) = x '/\' y '\/' x '/\' z
-- x '\/' (y '/\' z) = (x '\/' y) '/\' (x '\/' z)
-- @
--
-- Distributivity implies < https://en.wikipedia.org/wiki/Modular_lattice modularity >:
-- 
-- > x <~ y implies x \/ (z /\ y) = (x \/ z) /\ y for every z
--
-- See < https://en.wikipedia.org/wiki/Distributive_lattice >.
--
class Lattice a => Distributive a where

    -- | Greatest lower bound operator.
    --
    -- If the lattice is distributive then 'glb' has the following properties.
    --
    -- @ 
    -- 'glb' 'bottom' x 'top' = x
    -- 'glb' x y y = y
    -- 'glb' x y z = 'glb' z x y
    -- 'glb' x y z = 'glb' x z y
    -- 'glb' ('glb' x w y) w z = 'glb' x w ('glb' y w z)
    -- @
    --
    -- >>> glb 1.0 9.0 7.0
    -- 7.0
    -- >>> glb 1.0 9.0 (0.0 / 0.0)
    -- 9.0
    -- >>> glb (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: Set Int
    -- fromList [3,5]
    --
    -- See Birkhoff's self-dual < https://en.wikipedia.org/wiki/Median_algebra ternary median > operation.
    --
    glb :: a -> a -> a -> a
    glb x y z = (x \/ y) /\ (y \/ z) /\ (z \/ x)

    -- | Least upper bound operator.
    --
    -- The order dual of 'glb'.
    --
    -- >>> lub 1.0 9.0 7.0
    -- 7.0
    -- >>> lub 1.0 9.0 (0.0 / 0.0)
    -- 1.0
    --
    lub :: a -> a -> a -> a
    lub x y z = (x /\ y) \/ (y /\ z) \/ (z /\ x)

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Lattice Ordering
instance Bounded Ordering
instance Distributive Ordering

instance Lattice ()
instance Bounded ()
instance Distributive ()

instance Lattice Bool
instance Bounded Bool
instance Distributive Bool

instance Lattice Word8
instance Bounded Word8
instance Distributive Word8

instance Lattice Word16
instance Bounded Word16
instance Distributive Word16

instance Lattice Word32
instance Bounded Word32
instance Distributive Word32

instance Lattice Word64
instance Bounded Word64
instance Distributive Word64

instance Lattice Word
instance Bounded Word
instance Distributive Word

instance Lattice Natural
instance Distributive Natural

instance Lattice (Ratio Natural)
instance Bounded (Ratio Natural)

instance Lattice Int8
instance Bounded Int8
instance Distributive Int8

instance Lattice Int16
instance Bounded Int16
instance Distributive Int16

instance Lattice Int32
instance Bounded Int32
instance Distributive Int32

instance Lattice Int64
instance Bounded Int64
instance Distributive Int64

instance Lattice Int
instance Bounded Int
instance Distributive Int

instance Lattice Integer
instance Distributive Integer

instance Lattice (Ratio Integer)
instance Bounded (Ratio Integer)

instance Lattice Float
instance Bounded Float

instance Lattice Double
instance Bounded Double

instance Lattice a => Lattice (Down a)
instance Bounded a => Bounded (Down a)
instance Distributive a => Distributive (Down a)

instance (Preorder a, Finite a, Semigroup a) => Lattice (Endo a)
instance (Preorder a, Finite a, Monoid a) => Bounded (Endo a)
instance (Preorder a, Finite a, Monoid a) => Distributive (Endo a)

instance (Finite r, Lattice a) => Lattice (r -> a)
instance (Finite r, Bounded a) => Bounded (r -> a)
instance (Finite r, Distributive a) => Distributive (r -> a)

instance (Finite b, Lattice a) => Lattice (Op a b)
instance (Finite b, Bounded a) => Bounded (Op a b)
instance (Finite b, Distributive a) => Distributive (Op a b)

instance Finite a => Lattice (Predicate a)
instance Finite a => Bounded (Predicate a)
instance Finite a => Distributive (Predicate a)

instance Lattice a => Lattice (Maybe a)
instance (Lattice a, Monoid (Meet a)) => Bounded (Maybe a)
instance Distributive a => Distributive (Maybe a)

-- | All minimal elements of the upper lattice cover all maximal elements of the lower lattice.
instance (Lattice a, Lattice b) => Lattice (Either a b)
instance (Bounded a, Bounded b) => Bounded (Either a b)



--complement :: (TotalOrder a, Finite a) => Set.Set a -> Set.Set a
--complement xs = Set.fromList [ x | x <- universeF, Set.notMember x xs]

instance TotalOrder a => Lattice (Set.Set a)
instance (TotalOrder a, Finite a) => Bounded (Set.Set a)
instance TotalOrder a => Distributive (Set.Set a)

instance (TotalOrder k, Lattice a) => Lattice (Map.Map k a)
instance (TotalOrder k, Finite k, Bounded a) => Bounded (Map.Map k a)
instance (TotalOrder k, Distributive a) => Distributive (Map.Map k a)

instance Lattice IntSet.IntSet
instance Bounded IntSet.IntSet
instance Distributive IntSet.IntSet

instance Lattice a => Lattice (IntMap.IntMap a)
instance Bounded a => Bounded (IntMap.IntMap a)
instance Distributive a => Distributive (IntMap.IntMap a)


{-

instance (Join-Semigroup) (Max a) => Semigroup (Additive (Max a)) where
  (<>) = liftA2 (\/)

instance (Join-Monoid) (Max a) => Monoid (Additive (Max a)) where
  mempty = pure bottom

-- workaround for poorly specified entailment: instance (TotalOrder a, Bounded a) => Monoid (Max a)
instance (Minimal a, Semigroup (Max a)) => Monoid (Join (Max a)) where
  mempty = pure $ Max minimal

instance (Join-Semigroup) a => Semigroup (Join (Dual a)) where
  (<>) = liftA2 . liftA2 $ flip (\/)

instance (Join-Monoid) a => Monoid (Join (Dual a)) where
  mempty = pure . pure $ bottom


instance (Join-Semigroup) a => Semigroup (Join (Down a)) where
  (<>) = liftA2 . liftA2 $ (\/) 

instance (Join-Monoid) a => Monoid (Join (Down a)) where
  --Join (Down a) <> Join (Down b)
  mempty = pure . pure $ bottom

instance Semigroup (Max a) => Semigroup (Join (Max a)) where
  (<>) = liftA2 (<>)

-- MinPlus Predioid
-- >>> Min 1  `mul`  Min 2 :: Min Int
-- Min {getMin = 3}
instance (Join-Semigroup) a => Semigroup (Multiplicative (Min a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 (\/) a b

-- MinPlus Dioid
instance (Join-Monoid) a => Monoid (Multiplicative (Min a)) where
  mempty = Multiplicative $ pure bottom

--instance ((Meet-Semigroup) a, Maximal a) => Monoid (Meet a) where
--  mempty = Meet maximal

-- >>> Min 1 /\ Min 2 :: Min Int
-- Min {getMin = 1}
instance Semigroup (Min a) => Semigroup (Meet (Min a)) where
  (<>) = liftA2 (<>)

instance (Meet-Semigroup) (Min a) => Semigroup (Additive (Min a)) where
  (<>) = liftA2 (/\) 

instance (Meet-Monoid) (Min a) => Monoid (Additive (Min a)) where
  mempty = pure top

-- workaround for poorly specified entailment: instance (TotalOrder a, Bounded a) => Monoid (Min a)
-- >>> bottom :: Min Natural
-- Min {getMin = 0}
instance (Maximal a, Semigroup (Min a)) => Monoid (Meet (Min a)) where
  mempty = pure $ Min maximal

-- MaxTimes Predioid

instance (Meet-Semigroup) a => Semigroup (Meet (Max a)) where
  Meet a <> Meet b = Meet $ liftA2 (/\) a b

-- MaxTimes Dioid
instance (Meet-Monoid) a => Monoid (Meet (Max a)) where
  mempty = Meet $ pure top




-}

