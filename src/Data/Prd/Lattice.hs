{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE Safe #-}

module Data.Prd.Lattice where

import Data.Data (Data, Typeable)
import Data.Foldable
import Data.Function
import Data.Int as Int (Int, Int8, Int16, Int32, Int64)
import Data.Maybe
import Data.Monoid hiding (First, Last)
import Data.Ord
import Data.Prd
import Data.Semigroup (Semigroup(..))
import Data.Semigroup.Foldable
import Data.Set (Set)
import Data.Word (Word, Word8, Word16, Word32, Word64)
import GHC.Generics (Generic, Generic1)

import Prelude 

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Sequence as Seq


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
-- (meet x y) /\ z = x /\ z `meet` y /\ z

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

infixr 6 /\
infixr 5 \/

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
-- x '\/' 'maximal' ≡ x
-- @
--
-- /Corollary/
--
-- @
-- x '\/' 'maximal'
--   ≡⟨ identity ⟩
-- (x '\/' 'maximal') '/\' 'maximal'
--   ≡⟨ absorption ⟩
-- 'maximal'
-- @
--
-- @
-- x '\/' 'minimal' ≡ x
-- @
--
-- /Corollary/
--
-- @
-- x '/\' 'minimal'
--   ≡⟨ identity ⟩
-- (x '/\' 'minimal') '\/' 'minimal'
--   ≡⟨ absorption ⟩
-- 'minimal'
-- @
--
-- /Associativity/
--
-- @
-- x '\/' (y '\/' z) ≡ (x '\/' y) '\/' z
-- x '/\' (y '/\' z) ≡ (x '/\' y) '/\' z
-- @
--
-- /Commutativity/
--
-- @
-- x '\/' y ≡ y '\/' x
-- x '/\' y ≡ y '/\' x
-- @
--
-- /Idempotency/
--
-- @
-- x '\/' x ≡ x
-- x '/\' x ≡ x
-- @
--
-- /Absorption/
--
-- @
-- (x '\/' y) '/\' y ≡ y
-- (x '/\' y) '\/' y ≡ y
-- @
--
class Prd a => Lattice a where

  (\/) :: a -> a -> a

  (/\) :: a -> a -> a

  -- | Lattice morphism.
  fromSubset :: Minimal a => Set a -> a
  fromSubset = join

-- | The partial ordering induced by the join-semilattice structure
joinLeq :: Lattice a => a -> a -> Bool
joinLeq x y = x \/ y =~ y

meetLeq :: Lattice a => a -> a -> Bool
meetLeq x y = x /\ y =~ x

join :: (Minimal a, Lattice a, Foldable f) => f a -> a
join = foldr' (\/) minimal

meet :: (Maximal a, Lattice a, Foldable f) => f a -> a
meet = foldr' (/\) maximal

-- | The join of at a list of join-semilattice elements (of length at least one)
join1 :: (Lattice a, Foldable1 f) => f a -> a
join1 =  unJoin . foldMap1 Join

--
-- | The meet of at a list of meet-semilattice elements (of length at least one)
meet1 :: (Lattice a, Foldable1 f) => f a -> a
meet1 = unMeet . foldMap1 Meet

-- | Birkhoff's self-dual ternary median operation.
--
-- @ median x x y ≡ x @
--
-- @ median x y z ≡ median z x y @
--
-- @ median x y z ≡  median x z y @
--
-- @ median (median x w y) w z ≡ median x w (median y w z) @
--
median :: Lattice a => a -> a -> a -> a
median x y z = (x \/ y) /\ (y \/ z) /\ (z \/ x)

---------------------------------------------------------------------
--  Instances
---------------------------------------------------------------------

instance Lattice () where
  _ \/ _ = ()
  _ /\ _ = ()

instance (Lattice a, Lattice b) => Lattice (a, b) where
  (x1, y1) \/ (x2, y2) = (x1 \/ x2, y1 \/ y2)
  (x1, y1) /\ (x2, y2) = (x1 /\ x2, y1 /\ y2)

instance (Lattice a, Lattice b) => Lattice (Either a b) where
  Right x \/ Right y = Right $ x \/ y
  x@Right{} \/ _     = x
  Left x  \/ Left y  = Left $ x \/ y
  x@Left{}  \/ y     = y

  Right x /\ Right y = Right $ x /\ y
  x@Right{} /\ y     = y
  Left x  /\ Left y  = Left $ x /\ y
  x@Left{}  /\ _     = x

instance Lattice a => Lattice (Maybe a) where
  Just x \/ Just y    = Just $ x \/ y
  x@Just{} \/ _       = x
  Nothing  \/ Nothing = Nothing
  Nothing  \/ y       = y

  Just x /\ Just y    = Just $ x /\ y
  x@Just{} /\ y       = y
  Nothing  /\ _       = Nothing

instance Lattice Bool where
  (\/) = (||)
  (/\) = (&&)

instance Lattice All where
  All a \/ All b = All $ a \/ b
  All a /\ All b = All $ a /\ b

instance Minimal All where
  minimal = All False

instance Maximal All where
  maximal = All True

instance Lattice Any where
  Any a \/ Any b = Any $ a \/ b
  Any a /\ Any b = Any $ a /\ b

instance Minimal Any where
  minimal = Any False

instance Maximal Any where
  maximal = Any True

instance Lattice a => Lattice (Down a) where
  Down x \/ Down y = Down (x /\ y)
  Down x /\ Down y = Down (x \/ y)

instance Ord a => Lattice (Ordered a) where
  Ordered x \/ Ordered y = Ordered (max x y)
  Ordered x /\ Ordered y = Ordered (min x y)

instance Ord a => Lattice (Set.Set a) where
  (\/) = Set.union
  (/\) = Set.intersection

instance (Ord k, Lattice a) => Lattice (Map.Map k a) where
  (\/) = Map.unionWith (\/)
  (/\) = Map.intersectionWith (/\)

instance Lattice a => Lattice (IntMap.IntMap a) where
  (\/) = IntMap.unionWith (\/)
  (/\) = IntMap.intersectionWith (/\)

instance Lattice IntSet.IntSet where
  (\/) = IntSet.union
  (/\) = IntSet.intersection

---------------------------------------------------------------------
--  Newtypes
---------------------------------------------------------------------

newtype Join a = Join { unJoin :: a }
  deriving (Eq, Ord, Show, Typeable, Data, Generic)

instance Lattice a => Semigroup (Join a) where
  Join a <> Join b = Join (a \/ b)

instance (Lattice a, Minimal a) => Monoid (Join a) where
  mempty = Join minimal
  Join a `mappend` Join b = Join (a \/ b)

instance (Eq a, Lattice a) => Prd (Join a) where
  (Join a) <~ (Join b) = joinLeq a b

newtype Meet a = Meet { unMeet :: a }
  deriving (Eq, Ord, Show, Typeable, Data, Generic)

instance Lattice a => Semigroup (Meet a) where
  Meet a <> Meet b = Meet (a /\ b)

instance (Lattice a, Maximal a) => Monoid (Meet a) where
  mempty = Meet maximal
  Meet a `mappend` Meet b = Meet (a /\ b)
