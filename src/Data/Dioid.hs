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
{-
import safe Data.Word
import safe Data.Connection
import safe Data.Connection.Word
--import safe Data.Connection.Yoneda
import safe Data.Semiring
import safe Data.Prd
import safe Data.Ord
import safe Numeric.Natural
import safe GHC.Real

import safe Data.Semigroup.Additive
import safe Data.Semigroup.Multiplicative

import safe Data.Bool
import safe Data.Complex
import safe Data.Either
import safe Data.Fixed
import safe Data.Maybe
import safe Data.Group
import safe Data.Int
import safe Data.Semigroup.Foldable
import safe Data.Tuple
import safe Data.Word
import safe GHC.Generics (Generic)
import safe Numeric.Natural
import safe Prelude ( Eq(..), Ord, Ordering(..), Bounded(..), Show, Foldable(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, Float, Double)
import safe qualified Prelude as P

import safe Data.Foldable

import Data.Set (Set)--as Set

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
-}

type Ordered = Additive -- TODO expand to newtype
type Join = Additive

type Meet = Multiplicative

type Semilattice = Semigroup

type BoundedSemilattice = Monoid

-- Generic Predioid
type PredioidLaw a = (Prd a, (Ordered-Semigroup) a, (Multiplicative-Semigroup) a)

-- Generic Dioid
type DioidLaw a = (Prd a, (Ordered-Monoid) a, (Multiplicative-Monoid) a)

type LatticeLaw a = (Prd a, (Join-Semilattice) a, (Meet-Semilattice) a)

type BoundedLatticeLaw a = (Prd a, (Join-BoundedSemilattice) a, (Meet-BoundedSemilattice) a)

type MinimalLatticeLaw a = (Prd a, (Join-BoundedSemilattice) a, (Meet-Semilattice) a)

type MaximalLatticeLaw a = (Prd a, (Join-Semilattice) a, (Meet-BoundedSemilattice) a)

--Tropical semirings
{-
type MinPlus a = Min a
type MaxPlus a = Min (Down a)
type MinTimes a = Max (Down a)
type MaxTimes a = Max a
-}
-- >>> minPlus [[1..4 :: Int], [0..2 :: Int]]
-- 3
minPlus :: (Additive-Monoid) a => Maximal a => Ord a => Functor f => Functor g => Foldable f => Foldable g => f (g a) -> a
minPlus = getMin . evalWith Min

-- >>> maxPlus [[1..4 :: Int], [0..2 :: Int]]
-- 10
maxPlus :: (Additive-Monoid) a => Minimal a => Ord a => Functor f => Functor g => Foldable f => Foldable g => f (g a) -> a
maxPlus a = b where (Down b) = getMin $ evalWith (Min . Down) a

-- >>> minTimes [[1..4 :: Int], [0..2 :: Int]]
-- 0
minTimes :: (Multiplicative-Monoid) a => Maximal a => Ord a => Functor f => Functor g => Foldable f => Foldable g => f (g a) -> a
minTimes a = b where (Down b) = getMax $ evalWith (Max . Down) a

-- >>> maxTimes [[1..4 :: Int], [0..2 :: Int]]
-- 24
maxTimes :: (Multiplicative-Monoid) a => Minimal a => Ord a => Functor f => Functor g => Foldable f => Foldable g => f (g a) -> a
maxTimes = getMax . evalWith Max



-- A constraint kind for topological dioids
--type Topological a = (Dioid a, Kleene a, Yoneda a)



-- | Right pre-dioids and dioids.
--
-- A right-dioid is a semiring with a right-canonical pre-order relation relative to '+':
--
-- @ a '<~' b '<==>' b == a '+' c @
--
-- In other words we have that:
--
-- @
-- a '<~' (a '+' b) '==' 'True'
-- @
--
-- Consequently '<~' is both reflexive and transitive:
--
-- @
-- a '<~' a '==' 'True'
-- a '<~' b && b '<~' c ==> a '<~' c '==' 'True'
-- @
--
-- Finally '<~' is an order relation:
--
-- @(a '=~' b) '<==>' (a '==' b)@
--
-- See 'Data.Semiring.Property'
--
class (Presemiring a, PredioidLaw a) => Predioid a

class (Semiring a, Predioid a) => Dioid a





{-
(i) a + b = zero ==> a == zero && b == zero
(ii) a * b = zero ==> a == zero || b == zero

every dioid satisfies (i).


  --Just $ recip a = star <$> mon one a --default for Dioid instances if one-a exists?
-}


{-

A partially ordered set is a directed-complete partial order (dcpo) if each of its directed subsets has a supremum. A subset of a partial order is directed if it is non-empty and every pair of elements has an upper bound in the subset. In the literature, dcpos sometimes also appear under the label up-complete poset.


distributivity: A join-semilattice is distributive if for all a, b, and x with x ≤ a ∨ b there exist a' ≤ a and b' ≤ b such that x = a' ∨ b' . Distributive meet-semilattices are defined dually. These definitions are justified by the fact that any distributive join-semilattice in which binary meets exist is a distributive lattice

morphisms: Given two join-semilattices (S, ∨) and (T, ∨), a homomorphism of (join-) semilattices is a function f: S → T such that

f(x ∨ y) = f(x) ∨ f(y).
Hence f is just a homomorphism of the two semigroups associated with each semilattice. If S and T both include a least element 0, then f should also be a monoid homomorphism, i.e. we additionally require that

f(0) = 0.
In the order-theoretic formulation, these conditions just state that a homomorphism of join-semilattices is a function that preserves binary joins and least elements, if such there be. The obvious dual—replacing ∧ with ∨ and 0 with 1—transforms this definition of a join-semilattice homomorphism into its meet-semilattice equivalent.

Note that any semilattice homomorphism is necessarily monotone with respect to the associated ordering relation.

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


-- p. 337 e.g. (N, lcm, (*))
-- 1 is not absorbing for (*) (indeed, for a∈E,a=1,a×1=a /=1). (N, lcm,×) is therefore neither a semiring nor a dioid.
--type MeetTimes a = ((Meet-BoundedSemilattice) a, (Multiplicative-Semigroup) a)

-- | Lattices.
--
-- A lattice is a partially ordered set in which every two elements have a unique join 
-- (least upper bound or supremum) and a unique meet (greatest lower bound or infimum). 
--
-- See <http://en.wikipedia.org/wiki/Lattice_(order)> and <http://en.wikipedia.org/wiki/Absorption_law>.
--
--
-- /Laws/
--
-- @
-- x '∨' 'maximal' ≡ x
-- @
--
-- /Corollary/
--
-- @
-- x '∨' 'maximal'
--   ≡⟨ identity ⟩
-- (x '∨' 'maximal') '∧' 'maximal'
--   ≡⟨ absorption ⟩
-- 'maximal'
-- @
--
-- @
-- x '∨' 'minimal' ≡ x
-- @
--
-- /Corollary/
--
-- @
-- x '∧' 'minimal'
--   ≡⟨ identity ⟩
-- (x '∧' 'minimal') '∨' 'minimal'
--   ≡⟨ absorption ⟩
-- 'minimal'
-- @
--
-- /Associativity/
--
-- @
-- x '∨' (y '∨' z) ≡ (x '∨' y) '∨' z
-- x '∧' (y '∧' z) ≡ (x '∧' y) '∧' z
-- @
--
-- /Commutativity/
--
-- @
-- x '∨' y ≡ y '∨' x
-- x '∧' y ≡ y '∧' x
-- @
--
-- /Idempotency/
--
-- @
-- x '∨' x ≡ x
-- x '∧' x ≡ x
-- @
--
-- /Absorption/
--
-- @
-- (x '∨' y) '∧' y ≡ y
-- (x '∧' y) '∨' y ≡ y
-- @
--
class (Predioid a, LatticeLaw a) => Lattice a


class (Dioid a, Lattice a) => BoundedLattice a



infixr 5 ∨

-- | Join operation on a semilattice.
--
-- >>> (> (0::Int)) ∧ ((< 10) ∨ (== 15)) $ 10
-- False
--
(∨) :: (Join-Semilattice) a => a -> a -> a
(∨) = add
{-# INLINE (∨) #-}

infixr 6 ∧ 

-- | Meet operation on a semilattice.
--
-- >>> (> (0::Int)) ∧ ((< 10) ∨ (== 15)) $ 15
-- True
--
(∧) :: (Meet-Semilattice) a => a -> a -> a
(∧) = mul
{-# INLINE (∧) #-}



-- | Birkhoff's self-dual ternary median operation.
--
-- @ median x x y ≡ x @
--
-- @ median x y z ≡ median z x y @
--
-- @ median x y z ≡ median x z y @
--
-- @ median (median x w y) w z ≡ median x w (median y w z) @
--
-- >>> median 1 2 3 :: Int
-- 2
--
median :: Lattice a => a -> a -> a -> a
median x y z = (x ∨ y) ∧ (y ∨ z) ∧ (z ∨ x)

bottom :: (Join-BoundedSemilattice) a => a
bottom = zero
{-# INLINE bottom #-}

top :: (Meet-BoundedSemilattice) a => a
top = one
{-# INLINE top #-}

-- @ 'join' :: 'Lattice' a => 'Minimal' a => 'Set' a -> a @
--
join :: (Join-BoundedSemilattice) a => Lattice a => Foldable f => f a -> a
join = sum

meet :: (Meet-BoundedSemilattice) a => Lattice a => Foldable f => f a -> a
meet = product

-- | The join of a list of join-semilattice elements (of length at least one)
join1 :: Lattice a => Foldable1 f => f a -> a
join1 = sum1

-- | The meet of a list of meet-semilattice elements (of length at least one)
meet1 :: Lattice a => Foldable1 f => f a -> a
meet1 = product1

-- | The partial ordering induced by the join-semilattice structure
joinLeq :: Eq a => (Join-Semilattice) a => a -> a -> Bool
joinLeq x y = x `add` y == y

-- | The partial ordering induced by the meet-semilattice structure
meetLeq :: Eq a => (Meet-Semilattice) a => a -> a -> Bool
meetLeq x y = x `mul` y == x

-- | The partial ordering induced by the join-semilattice structure
joinGeq :: Eq a => (Join-Semilattice) a => a -> a -> Bool
joinGeq x y = x `add` y == x

-- | The partial ordering induced by the meet-semilattice structure
meetGeq :: Eq a => (Meet-Semilattice) a => a -> a -> Bool
meetGeq x y = x `mul` y == y

-- | Partial version of 'Data.Ord.compare'.
--
pcompareJoin :: Eq a => (Join-Semilattice) a => a -> a -> Maybe Ordering
pcompareJoin x y
  | x == y = Just EQ
  | x `add` y == y && x /= y = Just LT
  | x `add` y == x && x /= y = Just GT
  | otherwise = Nothing

-- | Partial version of 'Data.Ord.compare'.
--
pcompareMeet :: Eq a => (Meet-Semilattice) a => a -> a -> Maybe Ordering
pcompareMeet x y
  | x == y = Just EQ
  | x `mul` y == x && x /= y = Just LT
  | x `mul` y == y && x /= y = Just GT
  | otherwise = Nothing



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
instance (Prd a, Predioid a) => Predioid (IntMap.IntMap a)
instance Predioid IntSet.IntSet
instance (Ord a, Prd a, Predioid a) => Predioid (Set.Set a)
instance (Ord k, Prd a, Predioid a) => Predioid (Map.Map k a)

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
instance (Prd a, Dioid a) => Dioid (IntMap.IntMap a)
instance (Ord k, (Multiplicative-Monoid) k, Prd a, Dioid a) => Dioid (Map.Map k a)


-- Selective Dioids






{-
instance Prd a => Prd (V2 a) where
  V2 a b <~ V2 d e = a <~ d && b <~ e

instance Prd a => Prd (V4 a) where
  V4 a b c d <~ V4 e f g h = a <~ e && b <~ f && c <~ g && d <~ h

instance (Monoid a, Dioid a) => Dioid (V4 a) where
-}

{-
instance Minimal a => Minimal (Dual a) where
  minimal = Dual minimal
instance Maximal a => Maximal (Dual a) where
  maximal = Dual maximal

-}

--instance Prd a => Prd (First a) where First a <~ _ = True -- TODO would these instances be legal?
--instance Prd a => Prd (Last a) where Last a <~ Last b = a <~ b 
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

data Sign = Neg | Pos | Zero | Indefinite -- qualitative addition

type Positive
newtype (Ratio Natural) a = (Ratio Natural) { } deriving
 -- p 328
instance Semigroup Max (Positive a)

instance Monoid (Max ((Ratio Natural) a)) where mempty = zero

instance Semigroup Min (Positive Double)

instance Monoid Min (Positive Double) where mempty = Positive $ one / zero

--Data.Semiring.Tropical
data PInf a = Finite a | PInf
-- Maybe a ~ NInf a

instance Ord a => Ord (PInf a) where


instance Monoid Min (PInf Natural) where mempty = PInf


--Data.Semiring.Euclidean
newtype GCD a = GCD a
newtype LCM a = LCM a

instance Semigroup (Join (GCD Natural)) where (<>) = liftA2 gcd

instance Monoid (Join (GCD (PInf Natural))) where mempty = pure Inf

instance Semigroup (Meet (LCM Natural)) where (<>) = liftA2 lcm

instance Monoid (Meet (LCM Natural)) where mempty = pure 1 -- what about zero?



type Rig a = (Semiring a, (Multiplicative-Monoid) a)

--p. 339
-- e.g. (MinPlus (Positive Double), Integer), (MinPlus (Inf Natural), Integer)
instance (Dioid a, Ring b) => Semiring (a, b)
instance (Maximal a, Ord a, Ring b) => Semiring (Min a, 


instance BoundedLattice a => Semiring a where
  (+) = (∨)
  (*) = (∧)
  zero = bottom
  one = top

--p. 340 
instance Semiring (Double, Sign)


type Predioid a = (Presemiring a, Prd a)

class (Semiring a, Predioid a) => Dioid a




--Prering
type Rng a = (Semiring a, (Additive-Group a))

class (Semiring a, Rng a) => Ring a
  (-)
  one

--p. 336
instance (Predioid a, Ring g) => Presemiring (a, b)



-}

-- Lattices
instance Lattice ()
instance Lattice Bool
instance (Prd a, Prd b, Lattice a, Lattice b) => Lattice (Either a b)
instance (Prd a, Lattice a) => Lattice (Maybe a)
instance (Prd a, Lattice a) => Lattice (IntMap.IntMap a)
instance Lattice IntSet.IntSet
instance (Ord a, Prd a, Lattice a) => Lattice (Set.Set a)
instance (Ord k, Prd a, Lattice a) => Lattice (Map.Map k a)

instance BoundedLattice ()
instance BoundedLattice Bool
instance (Prd a, BoundedLattice a) => BoundedLattice (Maybe a)
instance (Prd a, BoundedLattice a) => BoundedLattice (IntMap.IntMap a)
instance (Ord k, (Multiplicative-Monoid) k, Prd a, BoundedLattice a) => BoundedLattice (Map.Map k a)


{-




class Prd a => Lattice a where

  (∨) :: a -> a -> a

  (∧) :: a -> a -> a

  -- | Lattice morphism.
  fromSubset :: Minimal a => Set a -> a
  fromSubset = join





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
