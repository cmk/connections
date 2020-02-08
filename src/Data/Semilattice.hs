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

module Data.Semilattice (
    type (-)
  -- * Join semilattices
  , bottom
  , (∨)
  , Join(..)
  , JoinSemilattice
  , BoundedJoinSemilattice
  , join
  , joinWith
  , join1
  , joinWith1
  -- * Meet semilattices
  , top
  , (∧)
  , Meet(..)
  , MeetSemilattice
  , BoundedMeetSemilattice
  , meet
  , meetWith
  , meet1
  , meetWith1
  -- * Lattices
  , Lattice
  , LatticeLaw
  , BoundedLatticeLaw
  , BoundedLattice
  , LowerBoundedLattice
  , UpperBoundedLattice
  , glb
  , glbWith
  , lub
  , lubWith
  , eval
  , evalWith
  , eval1
  , evalWith1
  , cross
  , cross1
) where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Connection
import safe Data.Maybe
import safe Data.Either
import safe Data.Fixed
import safe Data.Float
import safe Data.Functor.Apply
import safe Data.Foldable hiding (join, meet)
import safe Data.Group
import safe Data.Int
import safe Data.List (unfoldr)
import safe Data.List.NonEmpty hiding (filter, unfoldr)
import safe Data.Magma
import safe Data.Prd
import safe Data.Ord (Ord)
import safe Data.Semiring hiding (eval, eval1, evalWith, evalWith1, cross, cross1)
import safe Data.Dioid
import safe Data.Semigroup
import safe Data.Semigroup
import safe Data.Semigroup.Join
import safe Data.Semigroup.Foldable
import safe Data.Semigroup.Meet
import safe Data.Tuple
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic)
import safe GHC.Real hiding (Fractional(..), div, (^^), (^), (%))
import safe Numeric.Natural
import safe Data.Ratio
import safe Prelude hiding (Ord(..), Fractional(..),Num(..))
import safe qualified Prelude as P

import qualified Control.Category as C 
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet




{-
--(a ∧ b) ⊗ c = (a ⊗ c) ∧ (b ⊗ c), c ⊗ (a ∧ b) = (c ⊗ a) ∧ (c ⊗ b)
-- (meet x y) ∧ z = x ∧ z `meet` y ∧ z

-- idempotent sup dioids ? complete (join-semi)lattices derived from <=?
--connr-distributivity (the group (E\{ε}, ⊗) is therefore reticulated)
--
-- mon zero = const Nothing

-- bounded meet semilattice
-- need the codistributive property & absorbtion & commutativity

If E is a distributive lattice, then (E, ∨, ∧) is a doublyidempotent dioid, the order relation (canonical) of the dioid being defined as:
a ≤ b ⇔ a ∨ b = b.
Conversely, let (E, ⊕, ⊗) be a doubly-idempotent dioid for which ≤, the canonical
order relation relative to the law ⊕ is also a canonical order relation for ⊗:
x ≤ y ⇔ x ⊗ y = x.
Then E is a distributive lattice.
-}


-- Lattice types


type LatticeLaw a = (JoinSemilattice a, MeetSemilattice a)

type BoundedLatticeLaw a = (BoundedJoinSemilattice a, BoundedMeetSemilattice a)

type BoundedLattice a = (Lattice a, BoundedLatticeLaw a)

type LowerBoundedLattice a = (Lattice a, (Join-Monoid) a)

type UpperBoundedLattice a = (Lattice a, (Meet-Monoid) a)

type BoundedJoinSemilattice a = (JoinSemilattice a, (Join-Monoid) a)

type BoundedMeetSemilattice a = (MeetSemilattice a, (Meet-Monoid) a)


-- | Lattices.
--
-- A lattice is a partially ordered set in which every two elements have a unique join 
-- (least upper bound or supremum) and a unique meet (greatest lower bound or infimum). 
--
-- /Neutrality/
--
-- @
-- x '∨' 'minimal' = x
-- x '∧' 'maximal' = x
-- @
--
-- /Associativity/
--
-- @
-- x '∨' (y '∨' z) = (x '∨' y) '∨' z
-- x '∧' (y '∧' z) = (x '∧' y) '∧' z
-- @
--
-- /Commutativity/
--
-- @
-- x '∨' y = y '∨' x
-- x '∧' y = y '∧' x
-- @
--
-- /Idempotency/
--
-- @
-- x '∨' x = x
-- x '∧' x = x
-- @
--
-- /Absorption/
--
-- @
-- (x '∨' y) '∧' y = y
-- (x '∧' y) '∨' y = y
-- @
--
-- See <http://en.wikipedia.org/wiki/Lattice_(order)> and <http://en.wikipedia.org/wiki/Absorption_law>.
--
-- Note that distributivity is _not_ a requirement for a lattice,
-- however distributive lattices are idempotent, commutative dioids.
-- 
class LatticeLaw a => Lattice a


-- | Birkhoff's self-dual < https://en.wikipedia.org/wiki/Median_algebra ternary median > operation.
--
-- If the lattice is distributive then 'glb' has the following properties.
--
-- @ 
-- 'glb' x y y = y
-- 'glb' x y z = 'glb' z x y
-- 'glb' x y z = 'glb' x z y
-- 'glb' ('glb' x w y) w z = 'glb' x w ('glb' y w z)
-- @
--
-- >>> glb 1 2 3 :: Int
-- 2
-- >>> glb (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: Set Int
-- fromList [3,5]
--
-- See 'Data.Semilattice.Property'.
-- 
glb :: Lattice a => a -> a -> a -> a
glb = glbWith id

-- >>> glbWith N5 1 9 7
-- N5 {fromN5 = 7.0}
-- >>> glbWith N5 1 9 (0/0)
-- N5 {fromN5 = 9.0}
glbWith :: Lattice r => (a -> r) -> a -> a -> a -> r
glbWith f x y z = (f x ∨ f y) ∧ (f y ∨ f z) ∧ (f z ∨ f x)

lub :: Lattice a => a -> a -> a -> a
lub = lubWith id

-- >>> lubWith N5 1 9 7
-- N5 {fromN5 = 7.0}
-- >>> lubWith N5 1 9 (0/0)
-- N5 {fromN5 = 1.0}
lubWith :: Lattice r => (a -> r) -> a -> a -> a -> r
lubWith f x y z = (f x ∧ f y) ∨ (f y ∧ f z) ∨ (f z ∧ f x)

-- @ 'join' :: 'Lattice' a => 'Minimal' a => 'Set' a -> a @
--
join :: (Join-Monoid) a => Lattice a => Foldable f => f a -> a
join = joinWith id

-- >>> joinWith Just [1..5 :: Int]
-- Just 5
-- >>> joinWith N5 [1,5,0/0]
-- N5 {fromN5 = Infinity}
-- >>> joinWith MaxMin $ [IntSet.fromList [1..5], IntSet.fromList [2..4]]
-- MaxMin {unMaxMin = fromList [2,3,4]}
joinWith :: (Join-Monoid) a => Foldable t => (b -> a) -> t b -> a
joinWith f = foldr' ((∨) . f) bottom
{-# INLINE joinWith #-}

meet :: (Meet-Monoid) a => Lattice a => Foldable f => f a -> a
meet = meetWith id

-- | Fold over a collection using the multiplicative operation of an arbitrary semiring.
-- 
-- @
-- 'meet' f = 'Data.foldr'' ((*) . f) 'top'
-- @
--
--
-- >>> meetWith Just [1..5 :: Int]
-- Just 1
-- >>> meetWith N5 [1,5,0/0]
-- N5 {fromN5 = -Infinity}
meetWith :: (Meet-Monoid) a => Foldable t => (b -> a) -> t b -> a
meetWith f = foldr' ((∧) . f) top
{-# INLINE meetWith #-}

-- | The join of a list of join-semilattice elements (of length at least top)
join1 :: Lattice a => Foldable1 f => f a -> a
join1 = joinWith1 id

-- | Fold over a non-empty collection using the join operation of an arbitrary join semilattice.
--
joinWith1 :: Foldable1 t => Lattice a => (b -> a) -> t b -> a
joinWith1 f = unJoin . foldMap1 (Join . f)
{-# INLINE joinWith1 #-}

-- | The meet of a list of meet-semilattice elements (of length at least top)
meet1 :: Lattice a => Foldable1 f => f a -> a
meet1 = meetWith1 id

-- | Fold over a non-empty collection using the multiplicative operation of a semiring.
--
-- As the collection is non-empty this does not require a distinct multiplicative unit:
--
-- >>> meetWith1 Just $ 1 :| [2..5 :: Int]
-- Just 120
-- >>> meetWith1 First $ 1 :| [2..(5 :: Int)]
-- First {getFirst = 15}
-- >>> meetWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Just 11}
--
meetWith1 :: Foldable1 t => Lattice a => (b -> a) -> t b -> a
meetWith1 f = unMeet . foldMap1 (Meet . f)
{-# INLINE meetWith1 #-}

-- | Evaluate a lattice expression.
-- 
-- @ (a11 ∧ .. ∧ a1m) ∨ (a21 ∧ .. ∧ a2n) ∨ ... @
--
-- >>> eval [[1, 2], [3, 4, 5], [6, 7 :: Int]] -- 1 * 2 + 3 * 4
-- 14
-- >>> eval $ sequence [[1, 2], [3, 4 :: Int]] -- 1 + 2 * 3 + 4
-- 21
--
eval :: BoundedLattice a => Functor f => Foldable f => Foldable g => f (g a) -> a
eval = join . fmap meet

-- >>> evalWith Max [[1..4 :: Int], [0..2 :: Int]]
-- Max {getMax = 24}
evalWith :: BoundedLattice r => Functor f => Functor g => Foldable f => Foldable g => (a -> r) -> f (g a) -> r
evalWith f = join . fmap meet . (fmap . fmap) f

eval1 :: Lattice a => Functor f => Foldable1 f => Foldable1 g => f (g a) -> a
eval1 = join1 . fmap meet1

-- >>>  evalWith1 (Max . Down) $ (1 :| [2..5 :: Int]) :| [-5 :| [2..5 :: Int]]
-- Max {getMax = Down 9}
-- >>>  evalWith1 Max $ (1 :| [2..5 :: Int]) :| [-5 :| [2..5 :: Int]]
-- Max {getMax = 15}
-- 
evalWith1 :: Lattice r => Functor f => Functor g => Foldable1 f => Foldable1 g => (a -> r) -> f (g a) -> r
evalWith1 f = join1 . fmap meet1 . (fmap . fmap) f

-- | Cross-multiply two collections.
--
-- >>> cross [1,3,5 :: Int] [2,4]
-- 4
--
-- >>> cross [1,2,3 :: Int] []
-- -9223372036854775808
--
cross :: Foldable f => Applicative f => LowerBoundedLattice a => f a -> f a -> a
cross a b = join $ liftA2 (∧) a b
{-# INLINE cross #-}

-- | Cross-multiply two non-empty collections.
--
cross1 :: Foldable1 f => Apply f => Lattice a => f a -> f a -> a
cross1 a b = join1 $ liftF2 (∧) a b
{-# INLINE cross1 #-}



-- Lattices
instance Lattice ()
instance Lattice Bool
instance Lattice Word
instance Lattice Word8
instance Lattice Word16
instance Lattice Word32
instance Lattice Word64
instance Lattice Natural

instance Lattice Int
instance Lattice Int8
instance Lattice Int16
instance Lattice Int32
instance Lattice Int64
instance Lattice Integer

instance Lattice Uni
instance Lattice Deci
instance Lattice Centi
instance Lattice Milli
instance Lattice Micro
instance Lattice Nano
instance Lattice Pico

instance Lattice a => Lattice (Down a)
instance (Lattice a, Lattice b) => Lattice (Either a b)
instance Lattice a => Lattice (Maybe a)
instance Lattice a => Lattice (IntMap.IntMap a)
instance Lattice IntSet.IntSet
instance Ord a => Lattice (Set.Set a)
instance (Ord k, Lattice a) => Lattice (Map.Map k a)
