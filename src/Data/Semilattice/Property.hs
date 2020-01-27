{-# Language AllowAmbiguousTypes #-}
{-# LANGUAGE Safe #-}

module Data.Semilattice.Property where
{- (
  -- * Required properties of lattices
    nonunital_on
  , preordered
  , monotone_join
  , monotone_join'
  , monotone_meet
  , commutative_join
  , commutative_meet
  --, morphism_bounded
  , morphism_lattice
  , morphism_joinsemilattice
  , morphism_meetsemilattice
  , associative_join_on
  , associative_meet_on
  , commutative_join_on
  , commutative_meet_on
  , idempotent_join
  , idempotent_join_on
  , idempotent_meet
  , idempotent_meet_on
  , absorbative_join_on
  , absorbative_join_on'
  , absorbative_meet_on
  , absorbative_meet_on'
  -- * Required properties of bounded lattices
  , neutral_join_on
  , neutral_meet_on
  , annihilative_meet_on
  , monotone_bottom
  , annihilative_unit
  , pos_addition
  , pos_multiplication
  , annihilative_join 
  , annihilative_join' 
  -- * Distributive semilattices and lattices
  , majority_median
  , commutative_median
  , commutative_median'
  , associative_median
  , morphism_distributive
  , distributive_on
  , codistributive
  , distributive_finite_on
  , distributive_finite1_on
  , distributive_cross_on
  , distributive_cross1_on
) where
-}
import Data.Dioid
import Data.Dioid.Property as Prop
import Data.Semigroup
import Data.List (unfoldr)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Prd
import Data.Semigroup.Join
import Data.Semigroup.Meet
import Data.Semilattice
--import Data.Semigroup.Property as Prop
import Data.Semiring hiding (nonunital)
import Data.Semiring.Property as Prop
import Numeric.Natural
import Test.Function  as Prop
import Test.Logic (Rel, (<==>),(==>))
import Test.Operation as Prop hiding (distributive_on)

import Prelude hiding (Ord(..), Num(..), sum)

------------------------------------------------------------------------------------
-- Required properties of join semilattices

-- | \( \forall a, b, c \in R: (a + b) + c \sim a + (b + c) \)
--
-- All semigroups must right-associate join.
--
-- This is a required property.
--
associative_join_on :: (Join-Semigroup) r => Rel r b -> r -> r -> r -> b
associative_join_on (~~) = Prop.associative_on (~~) (∨) 


-- | \( \forall a, b \in R: a + b \sim b + a \)
--
-- This is a an /optional/ property for semigroups, and a /required/ property for semirings.
--
commutative_join_on :: (Join-Semigroup) r => Rel r b -> r -> r -> b
commutative_join_on (~~) = Prop.commutative_on (~~) (∨) 

-- | Idempotency property for join semigroups.
--
-- @ 'idempotent_join' = 'absorbative_join' 'top' @
-- 
-- See < https://en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a required property for lattices.
--
idempotent_join_on :: (Join-Semigroup) r => Rel r b -> r -> b
idempotent_join_on (~~) r = (∨) r r ~~ r

morphism_join_on :: (Join-Semigroup) r => (Join-Semigroup) s => Rel s b -> (r -> s) -> r -> r -> b
morphism_join_on (~~) f x y = (f $ x ∨ y) ~~ (f x ∨ f y)

morphism_join_on' :: (Join-Monoid) r => (Join-Monoid) s => Rel s b -> (r -> s) -> b
morphism_join_on' (~~) f = (f bottom) ~~ bottom

-- | \( \forall a, b: f(a ∨ b) = f(a) ∨ f(b) \)
--
-- Given two join-semilattices (S, ∨) and (T, ∨), a homomorphism of (join-) semilattices 
-- is a function /f: S → T/ such that 
--
-- @ f (x '∨' y) '==' f x '∨' f y @
--
-- In the order-theoretic for(∧)ation, these conditions just state that a homomorphism 
-- of join-semilattices is a function that preserves binary joins and least elements, 
-- if such there be. 
--
morphism_joinsemilattice :: Prd r => Prd s => (Join-Semigroup) r => (Join-Semigroup) s => (r -> s) -> r -> r -> Bool
morphism_joinsemilattice f x y =
  Prop.monotone_on (<=) (<=) f x y &&
  morphism_join_on (=~) f x y

------------------------------------------------------------------------------------
-- Required properties of meet semilattices

-- | \( \forall a, b, c \in R: (a * b) * c \sim a * (b * c) \)
--
-- All semigroups must right-associate meet.
--
-- This is a required property.
--
associative_meet_on :: (Meet-Semigroup) r => Rel r b -> r -> r -> r -> b
associative_meet_on (~~) = Prop.associative_on (~~) (∧) 

-- | \( \forall a, b \in R: a * b \sim b * a \)
--
-- This is a an /optional/ property for semigroups, and a /optional/ property for semirings.
-- It is a /required/ property for rings.
--
commutative_meet_on :: (Meet-Semigroup) r => Rel r b -> r -> r -> b
commutative_meet_on (~~) = Prop.commutative_on (~~) (∧) 

-- | Idempotency property for semigroups.
--
-- @ 'idempotent_meet' = 'absorbative_meet' 'bottom' @
-- 
-- See < https://en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a an /optional/ property for semigroups, and a /optional/ property for semirings.
--
-- This is a /required/ property for lattices.
--
idempotent_meet_on :: (Meet-Semigroup) r => Rel r b -> r -> b
idempotent_meet_on (~~) r = (∧) r r ~~ r

-- |
--
-- The obvious dual replacing '∧' with '∨' and 'bottom' with 'top' transforms this
-- definition of a join-semilattice homomorphism into its meet-semilattice equivalent.
--
-- Note that any semilattice homomorphism is necessarily monotone with respect to the 
-- associated partial ordering relation.
--
morphism_meetsemilattice :: Prd r => Prd s => (Meet-Semigroup) r => (Meet-Semigroup) s => (r -> s) -> r -> r -> Bool
morphism_meetsemilattice f x y =
  Prop.monotone_on (>=) (>=) f x y &&
  morphism_meet_on (=~) f x y

morphism_meet_on :: (Meet-Semigroup) r => (Meet-Semigroup) s => Rel s b -> (r -> s) -> r -> r -> b
morphism_meet_on (~~) f x y = (f $ x ∧ y) ~~ (f x ∧ f y)

morphism_meet_on' :: (Meet-Monoid) r => (Meet-Monoid) s => Rel s b -> (r -> s) -> b
morphism_meet_on' (~~) f = (f top) ~~ top

------------------------------------------------------------------------------------
-- Required properties of lattices

-- This is a required property for semilattices and lattices.
--
commutative_join :: Eq r => Lattice r => r -> r -> Bool
commutative_join = commutative_join_on $ \a b -> joinLeq a b && meetGeq a b 

-- This is a required property for semilattices and lattices.
--
commutative_meet :: Eq r => Lattice r => r -> r -> Bool
commutative_meet = commutative_meet_on $ \a b -> joinLeq a b && meetGeq a b

{-
-- If /R/ and /S/ both include extremal elements, then /f/ should also be a monoid homomorphism, 
-- i.e. we joinally require that
--
-- @ 
-- f 'top' '=~' 'top'
-- f 'bottom' '=~' 'bottom'
-- @
--
morphism_bounded :: Prd r => Prd s => BoundedLattice r => BoundedLattice s => (r -> s) -> r -> r -> r -> Bool
morphism_bounded f x y z =
  morphism_lattice f x y z &&
  morphism_join_on' (=~) f &&
  morphism_meet_on' (=~) f
-}
-- | Distributive lattice morphisms are compatible with 'glb'.
--
morphism_lattice :: Prd r => Prd s => Distributive r => Distributive s => (r -> s) -> r -> r -> r -> Bool
morphism_lattice f x y z =
  morphism_joinsemilattice f x y &&
  morphism_meetsemilattice f x y &&
  Prop.morphism_distribitive_on (=~) f x y z

------------------------------------------------------------------------------------
-- Properties of distributive semilattices and lattices

-- |  \( \forall a, b, c: c \leq a ∨ b \Rightarrow \exists a',b': c = a' ∨ b' \)
--
-- See < https://en.wikipedia.org/wiki/Distributivity_(order_theory) >
--
distributive_join :: Prd r => (Join-Semigroup) r => r -> r -> r -> r -> r -> Bool
distributive_join c a b a' b' = c <= a ∨ b ==> a' <= a && b' <= b && c <= a' ∨ b'

-- |  \( \forall a, b, c: c \leq a ∨ b \Rightarrow \exists a',b': c = a' ∨ b' \)
--
-- See < https://en.wikipedia.org/wiki/Distributivity_(order_theory) >
--
distributive_meet :: Prd r => (Meet-Semigroup) r => r -> r -> r -> r -> r -> Bool
distributive_meet c a b a' b' = c >= a ∧ b ==> a' >= a && b' >= b && c >= a' ∧ b'

-- @ glb x x y '==' x @
--
majority_median :: Eq r => Distributive r => r -> r -> Bool
majority_median x y = glb x y y == y

-- @ median x y z '==' glb z x y @
--
commutative_median :: Eq r => Distributive r => r -> r -> r -> Bool
commutative_median x y z = glb x y z == glb z x y

-- @ median x y z '==' median x z y @
--
commutative_median' :: Eq r => Distributive r => r -> r -> r -> Bool
commutative_median' x y z = glb x y z == glb x z y

-- @ median (median x w y) w z '==' median x w (median y w z) @
--
associative_median :: Eq r => Distributive r => r -> r -> r -> r -> Bool
associative_median x y z w = glb (glb x w y) w z == glb x w (glb y w z)

-- | Distributive lattice morphisms are compatible with 'median'.
--
morphism_distributive :: Prd r => Prd s => Distributive r => Distributive s => (r -> s) -> r -> r -> r -> Bool
morphism_distributive f x y z = f (glb x y z) =~ glb (f x) (f y) (f z)
