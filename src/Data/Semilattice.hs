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

module Data.Semilattice where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Maybe
import safe Data.Either
import safe Data.Fixed
import safe Data.Foldable hiding (join, meet)
import safe Data.Group
import safe Data.Int
--import safe Data.List
import safe Data.List.NonEmpty
import safe Data.Magma
import safe Data.Prd
import safe Data.Ord
import safe Data.Semiring
import safe Data.Dioid
import safe Data.Semigroup
import safe Data.Semigroup.Join
import safe Data.Semigroup.Meet
import safe Data.Semigroup.Foldable
import safe Data.Semigroup.Meet
import safe Data.Tuple
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic)
import safe GHC.Real hiding (Fractional(..), div, (^^), (^), (%))
import safe Numeric.Natural
import safe Data.Ratio

import safe Prelude ( Eq(..), Ord(..), Show, Ordering(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), id, (.), ($), flip, (<$>), Integer, Float, Double)
import safe qualified Prelude as P

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet


{-

A partially ordered set is a directed-complete partial order (dcpo) if each of its directed subsets has a supremum. A subset of a partial order is directed if it is non-empty and every pair of elements has an upper bound in the subset. In the literature, dcpos sometimes also appear under the label up-complete poset.



-}

--(a ∧ b) ⊗ c = (a ⊗ c) ∧ (b ⊗ c), c ⊗ (a ∧ b) = (c ⊗ a) ∧ (c ⊗ b)
-- (meet x y) ∧ z = x ∧ z `meet` y ∧ z

-- idempotent sup dioids ? complete (join-semi)lattices derived from <~?
--connr-distributivity (the group (E\{ε}, ⊗) is therefore reticulated)
--
-- mon zero = const Nothing

-- bounded meet semilattice
-- need the codistributive property & absorbtion & commutativity

{-
If E is a distributive lattice, then (E, ∨, ∧) is a doublyidempotent dioid, the order relation (canonical) of the dioid being defined as:
a ≤ b ⇔ a ∨ b = b.
Conversely, let (E, ⊕, ⊗) be a doubly-idempotent dioid for which ≤, the canonical
order relation relative to the law ⊕ is also a canonical order relation for ⊗:
x ≤ y ⇔ x ⊗ y = x.
Then E is a distributive lattice.
-}


-- Lattice types
type Semilattice = Semigroup

type BoundedSemilattice = Monoid

type Distributive a = (Presemiring a, Lattice a)

type LatticeLaw a = (Prd a, (Join-Semilattice) a, (Meet-Semilattice) a)

type LowerBounded a = (Lattice a, (Join-Monoid) a)

type UpperBounded a = (Lattice a, (Meet-Monoid) a)

type BoundedLatticeLaw a = (Prd a, (Join-BoundedSemilattice) a, (Meet-BoundedSemilattice) a)

type MinimalLatticeLaw a = (Prd a, (Join-BoundedSemilattice) a, (Meet-Semilattice) a)

type MaximalLatticeLaw a = (Prd a, (Join-Semilattice) a, (Meet-BoundedSemilattice) a)

-- | Lattices.
--
-- A lattice is a partially ordered set in which every two elements have a unique join 
-- (least upper bound or supremum) and a unique meet (greatest lower bound or infimum). 
--
-- /Neutrality/
--
-- @
-- x '∨' 'minimal' '==' x
-- x '∧' 'maximal' '==' x
-- @
--
-- /Associativity/
--
-- @
-- x '∨' (y '∨' z) '==' (x '∨' y) '∨' z
-- x '∧' (y '∧' z) '==' (x '∧' y) '∧' z
-- @
--
-- /Commutativity/
--
-- @
-- x '∨' y '==' y '∨' x
-- x '∧' y '==' y '∧' x
-- @
--
-- /Idempotency/
--
-- @
-- x '∨' x '==' x
-- x '∧' x '==' x
-- @
--
-- /Absorption/
--
-- @
-- (x '∨' y) '∧' y '==' y
-- (x '∧' y) '∨' y '==' y
-- @
--
-- See <http://en.wikipedia.org/wiki/Lattice_(order)> and <http://en.wikipedia.org/wiki/Absorption_law>.
--
-- Note that distributivity is _not_ a requirement for a lattice,
-- however distributive lattices are idempotent, commutative dioids.
-- 
class LatticeLaw a => Lattice a


class (Lattice a, BoundedLatticeLaw a) => BoundedLattice a

-- | Birkhoff's self-dual < https://en.wikipedia.org/wiki/Median_algebra ternary median > operation.
--
-- @ 
-- 'median' x y y '==' y
-- 'median' x y z '==' 'median' z x y
-- 'median' x y z '==' 'median' x z y
-- 'median' ('median' x w y) w z '==' 'median' x w ('median' y w z)
-- @
--
-- >>> median 1 2 3 :: Int
-- 2
-- >>> median (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: Set Int
-- fromList [3,5]
--
-- This operation requires a distributive lattice.
--
-- See 'Data.Dioid.Property'.
-- 
median :: Distributive a => a -> a -> a -> a
median x y z = (x ∨ y) ∧ (y ∨ z) ∧ (z ∨ x)

-- @ 'join' :: 'Lattice' a => 'Minimal' a => 'Set' a -> a @
--
join :: (Join-BoundedSemilattice) a => Lattice a => Foldable f => f a -> a
join = joinWith id

-- >>> joinWith MaxMin $ [IntSet.fromList [1..5], IntSet.fromList [2..4]]
-- MaxMin {unMaxMin = fromList [2,3,4]}
joinWith :: (Join-Monoid) a => Foldable t => (b -> a) -> t b -> a
joinWith f = foldr' ((∨) . f) bottom
{-# INLINE joinWith #-}

meet :: (Meet-BoundedSemilattice) a => Lattice a => Foldable f => f a -> a
meet = meetWith id

-- | Fold over a collection using the multiplicative operation of an arbitrary semiring.
-- 
-- @
-- 'meet' f '==' 'Data.foldr'' ((*) . f) 'top'
-- @
--
--
-- >>> meetWith Just [1..5 :: Int]
-- Just 120
--
meetWith :: (Meet-Monoid) a => Foldable t => (b -> a) -> t b -> a
meetWith f = foldr' ((∧) . f) top
{-# INLINE meetWith #-}

-- | The join of a list of join-semilattice elements (of length at least top)
join1 :: Lattice a => Foldable1 f => f a -> a
join1 = joinWith1 id

-- | Fold over a non-empty collection using the additive operation of an arbitrary semiring.
--

--(1 :| [2..5 :: Int]) ∧ (1 :| [2..5 :: Int])
-- First {getFirst = 1}
-- >>> joinWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Nothing}
-- >>> joinWith1 Just $ 1 :| [2..5 :: Int]
-- Just 15
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

{-
-- | Lattice morphism.
fromSubset :: Minimal a => Set a -> a
fromSubset = join

-- >>> join [1..5 :: Int]
-- 15
join :: (Join-Monoid) a => Lattice a => Foldable f => f a -> a
join = joinWith id

join1 :: Lattice a => Foldable1 f => f a -> a
join1 = joinWith1 id


-- >>> evalWith1 MaxMin $ (1 :| [2..5 :: Int]) :| [1 :| [2..5 :: Int]]
-- | Fold over a non-empty collection using the additive operation of an arbitrary semiring.
--
-- >>> joinWith1 First $ (1 :| [2..5 :: Int]) * (1 :| [2..5 :: Int])
-- First {getFirst = 1}
-- >>> joinWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Nothing}
-- >>> joinWith1 Just $ 1 :| [2..5 :: Int]
-- Just 15
--
joinWith1 :: Foldable1 t => Lattice a => (b -> a) -> t b -> a
joinWith1 f = unJoin . foldMap1 (Join . f)
{-# INLINE joinWith1 #-}

-- >>> meet [1..5 :: Int]
-- 120
meet :: (Meet-Monoid) a => Lattice a => Foldable f => f a -> a
meet = meetWith id

--
-- | The meet of at a list of semiring elements (of length at least top)
meet1 :: Lattice a => Foldable1 f => f a -> a
meet1 = meetWith1 id



-- | Cross-multiply two collections.
--
-- >>> cross [1,2,3 :: Int] [1,2,3]
-- 36
--
-- >>> cross [1,2,3 :: Int] []
-- 0
--
cross :: Foldable f => Applicative f => Lattice a => (Join-Monoid) a => f a -> f a -> a
cross a b = join $ liftA2 (*) a b
{-# INLINE cross #-}

-- | Cross-multiply two non-empty collections.
--
-- >>> cross1 (Right 2 :| [Left "oops"]) (Right 2 :| [Right 3]) :: Either [Char] Int
-- Right 4
--
cross1 :: Foldable1 f => Apply f => Lattice a => f a -> f a -> a
cross1 a b = join1 $ liftF2 (*) a b
{-# INLINE cross1 #-}

-- | Evaluate a semiring expression.
-- 
-- @ (a11 * .. * a1m) + (a21 * .. * a2n) + ... @
--
-- >>> eval [[1, 2], [3, 4 :: Int]] -- 1 * 2 + 3 * 4
-- 14
-- >>> eval $ sequence [[1, 2], [3, 4 :: Int]] -- 1 + 2 * 3 + 4
-- 21
--
eval :: Semiring a => Functor f => Foldable f => Foldable g => f (g a) -> a
eval = join . fmap meet

-- >>> evalWith Max [[1..4 :: Int], [0..2 :: Int]]
-- Max {getMax = 24}
evalWith :: Semiring r => Functor f => Functor g => Foldable f => Foldable g => (a -> r) -> f (g a) -> r
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

-}

-- | The partial ordering induced by the join-semilattice structure
joinLeq :: Eq a => (Join-Semilattice) a => a -> a -> Bool
joinLeq x y = x ∨ y == y

-- | The partial ordering induced by the meet-semilattice structure
meetLeq :: Eq a => (Meet-Semilattice) a => a -> a -> Bool
meetLeq x y = x ∧ y == x

-- | The partial ordering induced by the join-semilattice structure
joinGeq :: Eq a => (Join-Semilattice) a => a -> a -> Bool
joinGeq x y = x ∨ y == x

-- | The partial ordering induced by the meet-semilattice structure
meetGeq :: Eq a => (Meet-Semilattice) a => a -> a -> Bool
meetGeq x y = x ∧ y == y

-- | Partial version of 'Data.Ord.compare'.
--
pcompareJoin :: Eq a => (Join-Semilattice) a => a -> a -> Maybe Ordering
pcompareJoin x y
  | x == y = Just EQ
  | x ∨ y == y && x /= y = Just LT
  | x ∨ y == x && x /= y = Just GT
  | otherwise = Nothing

-- | Partial version of 'Data.Ord.compare'.
--
pcompareMeet :: Eq a => (Meet-Semilattice) a => a -> a -> Maybe Ordering
pcompareMeet x y
  | x == y = Just EQ
  | x ∧ y == x && x /= y = Just LT
  | x ∧ y == y && x /= y = Just GT
  | otherwise = Nothing


{-

-- p. 337 e.g. (N, lcm, (*))
-- 1 is not absorbing for (*) (indeed, for a∈E,a=1,a×1=a /=1). (N, lcm,×) is therefore neither a semiring nor a dioid.


--Data.Semiring.Euclidean
newtype GCD a = GCD a
newtype LCM a = LCM a

instance Semigroup (Join (GCD Natural)) where (<>) = liftA2 gcd

instance Monoid (Join (GCD (PInf Natural))) where mempty = pure Inf

instance Semigroup (Meet (LCM Natural)) where (<>) = liftA2 lcm

instance Monoid (Meet (LCM Natural)) where mempty = pure 1 -- what about zero?


-}

-- Lattices
instance Lattice ()
instance Lattice Bool
instance Lattice Word
instance Lattice Word8
instance Lattice Word16
instance Lattice Word32
instance Lattice Word64
instance Lattice Natural
instance Lattice (Ratio Natural)

instance Lattice Int
instance Lattice Int8
instance Lattice Int16
instance Lattice Int32
instance Lattice Int64
instance Lattice Integer
instance Lattice Rational

instance Lattice Uni
instance Lattice Deci
instance Lattice Centi
instance Lattice Milli
instance Lattice Micro
instance Lattice Nano
instance Lattice Pico

instance (Prd a, Prd b, Lattice a, Lattice b) => Lattice (Either a b)
instance (Prd a, Lattice a) => Lattice (Maybe a)
instance (Prd a, Lattice a) => Lattice (IntMap.IntMap a)
instance Lattice IntSet.IntSet
instance Ord a => Lattice (Set.Set a)
instance (Ord k, Prd a, Lattice a) => Lattice (Map.Map k a)

newtype MaxMin a = MaxMin { unMaxMin :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative MaxMin where
  pure = MaxMin
  MaxMin f <*> MaxMin a = MaxMin (f a)

instance Prd a => Prd (MaxMin a) where
  MaxMin a <~ MaxMin b = a <~ b

instance Ord a => Semigroup (Join (MaxMin a)) where
  (<>) = liftA2 . liftA2 $ max

instance (Ord a, Minimal a) => Monoid (Join (MaxMin a)) where
  mempty = pure . pure $ minimal


instance Ord a => Semigroup (Meet (MaxMin a)) where
  (<>) = liftA2 . liftA2 $ min

instance (Ord a, Maximal a) => Monoid (Meet (MaxMin a)) where
  mempty = pure . pure $ maximal


instance (Ord a, Bound a) => Lattice (MaxMin a)


{-
instance (Ord a, Minimal a, (Additive-Monoid) (Max a), (Multiplicative-Monoid) a) => Semiring (Max a)
instance (Ord a, Maximal a, (Additive-Monoid) (Min a), (Additive-Monoid) a) => Semiring (Min a)

instance (Prd a, Ord a, (Multiplicative-Semigroup) a) => Predioid (Max a)
instance (Prd a, Ord a, (Additive-Semigroup) a) => Predioid (Min a)

instance (Ord a, Minimal a, (Additive-Monoid) (Max a), (Multiplicative-Monoid) a) => Dioid (Max a)
instance (Ord a, Maximal a, (Additive-Monoid) (Min a), (Additive-Monoid) a) => Dioid (Min a)
-}

instance BoundedLattice ()
instance BoundedLattice Bool
instance (Prd a, UpperBounded a) => BoundedLattice (Maybe a)
--instance (Prd a, UpperBounded a) => BoundedLattice (IntMap.IntMap a)
--instance (Ord k, (Meet-Monoid) k, Prd a, UpperBounded a) => BoundedLattice (Map.Map k a)
