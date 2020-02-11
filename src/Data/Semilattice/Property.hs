{-# Language AllowAmbiguousTypes #-}

module Data.Semilattice.Property (
  -- * Properties of join lattices
    monotone_join
  , idempotent_join
  , idempotent_join_on
  , associative_join
  , associative_join_on
  , commutative_join
  , commutative_join_on
  , neutral_join
  , neutral_join_on
  , distributive_join
  -- * Properties of meet semilattices
  , monotone_meet
  , idempotent_meet
  , idempotent_meet_on
  , associative_meet
  , associative_meet_on
  , commutative_meet
  , commutative_meet_on
  , neutral_meet
  , neutral_meet_on
  , distributive_meet
  -- * Properties of lattices
  , absorbative
  , absorbative'
  , annihilative_join
  , annihilative_meet
  , distributive
  , codistributive
  , majority_glb
  , commutative_glb
  , commutative_glb'
  , associative_glb
  --, distributive_finite_on
  --, distributive_finite1_on
  --, distributive_cross_on
  --, distributive_cross1_on
  -- * Properties of semilattice & lattice morphisms
  , morphism_join
  , morphism_join_on
  , morphism_join'
  , morphism_join_on'
  , morphism_meet
  , morphism_meet_on
  , morphism_meet'
  , morphism_meet_on'
  , morphism_distributive
) where

--import Data.Semigroup.Property as Prop
import Data.Dioid
import Data.List (unfoldr)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Prd
import Data.Semigroup
import Data.Semigroup.Join
import Data.Semigroup.Meet
import Data.Semilattice
import Data.Semiring hiding (nonunital)
import Data.Semiring.Property as Prop hiding (distributive_on)
import Numeric.Natural
import Test.Function  as Prop
import Test.Logic (Rel, (<==>),(==>))
import qualified Test.Operation as Prop

import Prelude hiding (Ord(..), Num(..), sum)

------------------------------------------------------------------------------------
-- Properties of join semilattices

-- | \( \forall a, b, c: b \leq c \Rightarrow b ∨ a \leq c ∨ a \)
--
-- This is a required property.
--
monotone_join :: JoinSemilattice r => r -> r -> r -> Bool
monotone_join x = Prop.monotone_on (<=) (<=) (∨ x)

-- | \( \forall a \in R: a ∨ a = a \)
--
-- @ 'idempotent_join' = 'absorbative' 'top' @
-- 
-- See < https://en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a required property.
--
idempotent_join :: JoinSemilattice r => r -> Bool
idempotent_join = idempotent_join_on (=~)

idempotent_join_on :: (Join-Semigroup) r => Rel r b -> r -> b
idempotent_join_on (~~) r = (∨) r r ~~ r

-- | \( \forall a, b, c \in R: (a ∨ b) ∨ c = a ∨ (b ∨ c) \)
--
-- This is a required property.
--
associative_join :: JoinSemilattice r => r -> r -> r -> Bool
associative_join = Prop.associative_on (=~) (∨) 

associative_join_on :: (Join-Semigroup) r => Rel r b -> r -> r -> r -> b
associative_join_on (~~) = Prop.associative_on (~~) (∨) 

-- | \( \forall a, b \in R: a ∨ b = b ∨ a \)
--
-- This is a required property.
--
commutative_join :: JoinSemilattice r => r -> r -> Bool
commutative_join = commutative_join_on (=~)

commutative_join_on :: (Join-Semigroup) r => Rel r b -> r -> r -> b
commutative_join_on (~~) = Prop.commutative_on (~~) (∨) 

-- | \( \forall a \in R: (bottom ∨ a) = a \)
--
-- This is a required property for bounded join semilattices.
--
neutral_join :: BoundedJoinSemilattice r => r -> Bool
neutral_join = neutral_join_on (=~)

neutral_join_on :: (Join-Monoid) r => Rel r b -> r -> b
neutral_join_on (~~) = Prop.neutral_on (~~) (∨) bottom

-- |  \( \forall a, b, c: c \leq a ∨ b \Rightarrow \exists a',b': c = a' ∨ b' \)
--
-- See < https://en.wikipedia.org/wiki/Distributivity_(order_theory)#Distributivity_for_semilattices >
--
-- This is a required property for distributive join semilattices.
--
distributive_join :: JoinSemilattice r => r -> r -> r -> r -> r -> Bool
distributive_join c a b a' b' = c <= a ∨ b ==> a' <= a && b' <= b && c <= a' ∨ b'

------------------------------------------------------------------------------------
-- Properties of meet semilattices

-- | \( \forall a, b, c: b \leq c \Rightarrow b ∧ a \leq c ∧ a \)
--
-- This is a required property.
--
monotone_meet :: MeetSemilattice r => r -> r -> r -> Bool
monotone_meet x = Prop.monotone_on (<=) (<=) (∧ x)

-- | \( \forall a, b, c \in R: (a * b) * c = a * (b * c) \)
--
-- This is a required property.
--
associative_meet :: MeetSemilattice r => r -> r -> r -> Bool
associative_meet = associative_meet_on (=~)

associative_meet_on :: (Meet-Semigroup) r => Rel r b -> r -> r -> r -> b
associative_meet_on (~~) = Prop.associative_on (~~) (∧) 

-- | \( \forall a, b \in R: a ∧ b = b ∧ a \)
--
-- This is a required property.
--
commutative_meet :: MeetSemilattice r => r -> r -> Bool
commutative_meet = commutative_meet_on (=~)

commutative_meet_on :: (Meet-Semigroup) r => Rel r b -> r -> r -> b
commutative_meet_on (~~) = Prop.commutative_on (~~) (∧) 

-- | \( \forall a \in R: a ∧ a = a \)
--
-- @ 'idempotent_meet' = 'absorbative' 'bottom' @
-- 
-- See < https://en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a required property.
--
idempotent_meet :: MeetSemilattice r => r -> Bool
idempotent_meet = idempotent_meet_on (=~)

idempotent_meet_on :: (Meet-Semigroup) r => Rel r b -> r -> b
idempotent_meet_on (~~) r = (∧) r r ~~ r

-- | \( \forall a \in R: (bottom ∧ a) = a \)
--
-- This is a required property for bounded meet semilattices.
--
neutral_meet :: BoundedMeetSemilattice r => r -> Bool
neutral_meet = neutral_meet_on (=~)

neutral_meet_on :: (Meet-Monoid) r => Rel r b -> r -> b
neutral_meet_on (~~) = Prop.neutral_on (~~) (∧) top

-- |  \( \forall a, b, c: c \leq a ∨ b \Rightarrow \exists a',b': c = a' ∧ b' \)
--
-- See < https://en.wikipedia.org/wiki/Distributivity_(order_theory)#Distributivity_for_semilattices >
--
-- This is a required property for distributive meet semilattices.
--
distributive_meet :: MeetSemilattice r => r -> r -> r -> r -> r -> Bool
distributive_meet c a b a' b' = c >= a ∧ b ==> a' >= a && b' >= b && c >= a' ∧ b'

------------------------------------------------------------------------------------
-- Properties of lattices

-- | \( \forall a, b \in R: a ∧ b ∨ b = b \)
--
-- Absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative' 'top' a = a ∨ a = a
-- @
--
-- This is a required property.
--
absorbative :: Lattice r => r -> r -> Bool
absorbative x y = (x ∧ y ∨ y) =~ y

-- | \( \forall a, b \in R: a ∨ b ∧ b = b \)
--
-- Absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative'' 'bottom' a = a ∨ a = a
-- @
--
-- This is a required property.
--
absorbative' :: Lattice r => r -> r -> Bool
absorbative' x y = (x ∨ y ∧ y) =~ y

-- | \( \forall a \in R: (top ∨ a) = top \)
--
-- If /R/ is a lattice then its top element must be annihilative.
--
-- This is a required property.
--
annihilative_join :: UpperBoundedLattice r => r -> Bool
annihilative_join r = Prop.annihilative_on (=~) (∨) top r

-- | \( \forall a \in R: (bottom ∧ a) = bottom \)
--
-- If /R/ is a lattice then its bottom element must be annihilative.
--
-- For 'Semiring' instances this property translates to:
--
-- @
-- 'zero' '*' a = 'zero'
-- @
--
-- For 'Alternative' instances this property translates to:
--
-- @
-- 'empty' '*>' a = 'empty'
-- @
--
-- This is a required property.
--
annihilative_meet :: LowerBoundedLattice r => r -> Bool
annihilative_meet r = Prop.annihilative_on (=~) (∧) bottom r

------------------------------------------------------------------------------------
-- Properties of distributive lattices

distributive :: Lattice r => r -> r -> r -> Bool
distributive = Prop.distributive_on (=~) (∧) (∨)

-- | \( \forall a, b, c \in R: c ∨ (a ∧ b) \equiv (c ∨ a) ∧ (c ∨ b) \)
--
-- A right-codistributive semiring has a right-annihilative meet:
--
-- @ 'codistributive' 'top' a 'bottom' = 'top' '=~' 'top' '∨' a @
--
-- idempotent mulitiplication:
--
-- @ 'codistributive' 'bottom' 'bottom' a = a '=~' a '∧' a @
--
-- and idempotent addition:
--
-- @ 'codistributive' a 'bottom' a = a '=~' a '∨' a @
--
-- Furthermore if /R/ is commutative then it is a right-distributive lattice.
--
codistributive :: Lattice r => r -> r -> r -> Bool
codistributive = Prop.distributive_on' (=~) (∧) (∨)

-- | @ 'glb' x x y = x @
--
majority_glb :: Lattice r => r -> r -> Bool
majority_glb x y = glb x y y =~ y

-- | @ 'glb' x y z = 'glb' z x y @
--
commutative_glb :: Lattice r => r -> r -> r -> Bool
commutative_glb x y z = glb x y z =~ glb z x y

-- | @ 'glb' x y z = 'glb' x z y @
--
commutative_glb' :: Lattice r => r -> r -> r -> Bool
commutative_glb' x y z = glb x y z =~ glb x z y

-- | @ 'glb' ('glb' x w y) w z = 'glb' x w ('glb' y w z) @
--
associative_glb :: Lattice r => r -> r -> r -> r -> Bool
associative_glb x y z w = glb (glb x w y) w z =~ glb x w (glb y w z)

------------------------------------------------------------------------------------
-- Properties of semilattice & lattice morphisms

-- | \( \forall a, b: f(a ∨ b) = f(a) ∨ f(b) \)
--
-- Given two join-semilattices (S, ∨) and (T, ∨), a homomorphism is a monotone function /f: S → T/ such that 
--
-- @ f (x '∨' y) '=~' f x '∨' f y @
--
-- This is a required property for join semilattice morphisms.
--
morphism_join :: JoinSemilattice r => JoinSemilattice s => (r -> s) -> r -> r -> Bool
morphism_join = morphism_join_on (=~)

morphism_join_on :: (Join-Semigroup) r => (Join-Semigroup) s => Rel s b -> (r -> s) -> r -> r -> b
morphism_join_on (~~) f x y = (f $ x ∨ y) ~~ (f x ∨ f y)

-- | \( \forall a, b: f(bottom) = bottom \)
--
-- This is a required property for bounded join semilattice morphisms.
--
morphism_join' :: BoundedJoinSemilattice r => BoundedJoinSemilattice s => (r -> s) -> Bool
morphism_join' = morphism_join_on' (=~)

morphism_join_on' :: (Join-Monoid) r => (Join-Monoid) s => Rel s b -> (r -> s) -> b
morphism_join_on' (~~) f = (f bottom) ~~ bottom

-- | \( \forall a, b: f(a ∧ b) = f(a) ∧ f(b) \)
--
-- The obvious dual replacing '∧' with '∨' and 'bottom' with 'top' transforms this
-- definition of a join-semilattice homomorphism into its meet-semilattice equivalent.
--
-- This is a required property for meet semilattice morphisms.
--
morphism_meet :: MeetSemilattice r => MeetSemilattice s => (r -> s) -> r -> r -> Bool
morphism_meet = morphism_meet_on (=~)

morphism_meet_on :: (Meet-Semigroup) r => (Meet-Semigroup) s => Rel s b -> (r -> s) -> r -> r -> b
morphism_meet_on (~~) f x y = (f $ x ∧ y) ~~ (f x ∧ f y)

-- | \( \forall a, b: f(top) = top \)
--
-- This is a required property for bounded meet semilattice morphisms.
--
morphism_meet' :: BoundedMeetSemilattice r => BoundedMeetSemilattice s => (r -> s) -> Bool
morphism_meet' = morphism_meet_on' (=~)

morphism_meet_on' :: (Meet-Monoid) r => (Meet-Monoid) s => Rel s b -> (r -> s) -> b
morphism_meet_on' (~~) f = (f top) ~~ top

-- | Distributive lattice morphisms are compatible with 'glb'.
--
morphism_distributive :: Prd r => Prd s => Lattice r => Lattice s => (r -> s) -> r -> r -> r -> Bool
morphism_distributive f x y z = f (glb x y z) =~ glb (f x) (f y) (f z)
