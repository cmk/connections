{-# Language AllowAmbiguousTypes #-}
{-# LANGUAGE Safe #-}

module Data.Dioid.Property (
  -- * Required properties of pre-dioids
    nonunital_on
  , associative_addition_on
  , associative_multiplication_on
  , distributive_on
  , distributive_finite1_on 
  , commutative_addition_on
  , preordered
  , morphism_predioid
  , monotone_addition
  , monotone_multiplication
  -- * Required properties of dioids
  , neutral_addition_on
  , neutral_multiplication_on
  , annihilative_multiplication_on
  , distributive_finite_on
  , monotone_zero
  , morphism_dioid
  , annihilative_unit
  , pos_addition
  , pos_multiplication
  -- * Left distributive pre-dioids & dioids 
  , distributive_cross_on
  , distributive_cross1_on
  -- * Commutative pre-dioids & dioids 
  , commutative_multiplication_on
  -- * Absorbative pre-dioids & dioids 
  , absorbative_addition_on
  , absorbative_addition_on'
  , absorbative_multiplication_on
  , absorbative_multiplication_on' 
  -- * Annihilative pre-dioids & dioids 
  , annihilative_addition 
  , annihilative_addition' 
  , codistributive
  -- * Idempotent pre-dioids & dioids
  , monotone_addition'
  , idempotent_addition
 -- , idempotent_addition_on
  , idempotent_multiplication
 -- , idempotent_multiplication_on
{-
  -- * Properties of kleene dioids
  , kleene_pstable
  , kleene_paffine 
  , kleene_stable 
  , kleene_affine 
  , idempotent_star
-}
) where

import Data.Prd
import Data.Dioid
import Data.List (unfoldr)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semiring hiding (nonunital)
import Numeric.Natural
import Test.Logic (Rel, (<==>),(==>))
import Data.Semigroup.Additive
import Data.Semigroup.Multiplicative
import Test.Function  as Prop
import Test.Operation as Prop hiding (distributive_on)
import Data.Semiring.Property as Prop
import Data.Semigroup.Property as Prop

import Prelude hiding (Ord(..), Num(..), sum)

------------------------------------------------------------------------------------
-- Required properties of predioids.

-- | '<=' is a preordered relation relative to '+'.
--
-- This is a required property.
--
preordered :: Prd r => (Additive-Semigroup) r => r -> r -> Bool
preordered a b = a <= a + b

-- | Predioid morphisms are monotone, distributive semigroup morphisms.
--
-- This is a required property for predioid morphisms.
--
morphism_predioid :: Prd r => Prd s => Predioid r => Predioid s => (r -> s) -> r -> r -> r -> Bool
morphism_predioid f x y z = 
  Prop.monotone_on (<=) (<=) f x y &&
  Prop.morphism_distribitive_on (=~) f x y z &&
  f (x + y) =~ f x + f y && (f $ x * y) =~ (f x * f y)

-- | \( \forall a, b, c: b \leq c \Rightarrow b + a \leq c + a \)
--
-- In an ordered semiring this follows directly from the definition of '<='.
--
-- Compare 'cancellative_addition_on'.
-- 
-- @
-- 'monotone_addition' x y z '<==>' 'morphism_predioid' ('add' x) y z 
-- @
--
-- This is a required property.
--
monotone_addition :: Prd r => (Additive-Semigroup) r => r -> r -> r -> Bool
monotone_addition a = Prop.monotone_on (<=) (<=) (+ a)

-- | \( \forall a, b, c: b \leq c \Rightarrow b * a \leq c * a \)
--
-- In an ordered semiring this follows directly from 'distributive' and the definition of '<='.
--
-- Compare 'cancellative_multiplication_on'.
--
-- @
-- 'monotone_multiplication' x y z '<==>' 'morphism_predioid' ('mul' x) y z
-- @
--
-- This is a required property.
--
monotone_multiplication :: Prd r => (Multiplicative-Semigroup) r => r -> r -> r -> Bool
monotone_multiplication a = Prop.monotone_on (<=) (<=) (* a)

{-
-- | A variant of 'monotone_addition'.
--
monotone_addition' :: Prd r => Predioid r => r -> r -> r -> Bool
monotone_addition' x y z = morphism_predioid (+ z) x y 

monotone_multiplication' :: Prd r => Predioid r => r -> r -> r -> Bool
monotone_multiplication' x y z = morphism_predioid (* z) x y 
-}

------------------------------------------------------------------------------------
-- Required properties of dioids.

-- | 'zero' is a minimal or least element of /r/.
--
-- This is a required property.
--
monotone_zero :: Prd r => (Additive-Monoid) r => r -> Bool
monotone_zero a = zero ?~ a ==> zero <= a 

-- | Dioid morphisms are monoidal predioid morphisms.
--
-- This is a required property for dioid morphisms.
--
morphism_dioid :: Prd r => Prd s => Dioid r => Dioid s => (r -> s) -> r -> r -> r -> Bool
morphism_dioid f x y z = 
  morphism_predioid f x y z &&
  f zero =~ zero && f one =~ one


-- | '<=' is consistent with annihilativity.
--
-- This means that a dioid with an annihilative multiplicative one must satisfy:
--
-- @
-- ('one' <=) = ('one' '==')
-- @
--
-- This is a required property.
--
annihilative_unit :: Prd r => (Multiplicative-Monoid) r => r -> Bool
annihilative_unit a = one <= a <==> one =~ a

-- |  \( \forall a, b: a + b = 0 \Rightarrow a = 0 \wedge b = 0 \)
--
-- This is a required property.
--
pos_addition :: Prd r => (Additive-Monoid) r => r -> r -> Bool
pos_addition a b = a + b =~ zero ==> a =~ zero && b =~ zero

-- |  \( \forall a, b: a * b = 0 \Rightarrow a = 0 \vee b = 0 \)
--
-- Dioids which are groups wrt multiplication are often referred to as pos dioids or semi-fields
--
pos_multiplication :: Dioid r => r -> r -> Bool
pos_multiplication a b = a * b =~ zero ==> a =~ zero || b =~ zero

------------------------------------------------------------------------------------
-- Properties of absorbative predioids & dioids.

-- | \( \forall a, b \in R: a * b + b = b \)
--
-- Right-additive absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_addition' 'one' a '~~' a + a '~~' a
-- @
--
-- This is a required property for semilattices and lattices.
--
absorbative_addition_on :: Presemiring r => Rel r b -> r -> r -> b
absorbative_addition_on (~~) a b = (a * b + b) ~~ b

-- | \( \forall a, b \in R: b + b * a = b \)
--
-- Left-additive absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_addition' 'one' a '~~' a + a '~~' a
-- @
--
absorbative_addition_on' :: Presemiring r => Rel r b -> r -> r -> b
absorbative_addition_on' (~~) a b = (b + b * a) ~~ b

-- | \( \forall a, b \in R: (a + b) * b = b \)
--
-- Right-mulitplicative absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_multiplication' 'zero' a '~~' a '*' a '~~' a
-- @
--
-- See < https://en.wikipedia.org/wiki/Absorption_law >.
--
-- This is a required property for semilattices and lattices.
--
absorbative_multiplication_on :: Presemiring r => Rel r b -> r -> r -> b
absorbative_multiplication_on (~~) a b = ((a + b) * b) ~~ b

--absorbative_multiplication a b c = (a + b) * c '~~' c
--kleene a = 
--  absorbative_multiplication (star a) one a && absorbative_multiplication one (star a) a 

-- | \( \forall a, b \in R: b * (b + a) = b \)
--
-- Left-mulitplicative absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_multiplication'' 'zero' a '~~' a '*' a '~~' a
-- @
--
-- See < https://en.wikipedia.org/wiki/Absorption_law >.
--
absorbative_multiplication_on' :: Presemiring r => Rel r b -> r -> r -> b
absorbative_multiplication_on' (~~) a b = (b * (b + a)) ~~ b

------------------------------------------------------------------------------------
-- Properties of annihilative predioids & dioids.

-- | \( \forall a, b, c \in R: c + (a * b) \equiv (c + a) * (c + b) \)
--
-- A right-codistributive semiring has a right-annihilative muliplicative one:
--
-- @ 'codistributive' 'one' a 'zero' = 'one' '~~' 'one' '+' a @
--
-- idempotent mulitiplication:
--
-- @ 'codistributive' 'zero' 'zero' a = a '~~' a '*' a @
--
-- and idempotent addition:
--
-- @ 'codistributive' a 'zero' a = a '~~' a '+' a @
--
-- Furthermore if /R/ is commutative then it is a right-distributive lattice.
--
codistributive :: Eq r => Predioid r => r -> r -> r -> Bool
codistributive = Prop.distributive_on' (~~) (*) (+)

-- | \( \forall a \in R: o + a = o \)
--
-- A unital semiring with a right-annihilative muliplicative one must satisfy:
--
-- @
-- 'one' + a '~~' 'one'
-- @
--
-- For a dioid this is equivalent to:
-- 
-- @
-- ('one' '<=') = ('one' '~~')
-- @
--
-- For 'Alternative' instances this is known as the left-catch law:
--
-- @
-- 'pure' a '<|>' _ '~~' 'pure' a
-- @
--
-- This is a required property for bounded lattices.
--
annihilative_addition :: Eq r => Dioid r => r -> Bool
annihilative_addition r = Prop.annihilative_on (~~) (+) one r

-- | \( \forall a \in R: a + o = o \)
--
-- A unital semiring with a left-annihilative muliplicative one must satisfy:
--
-- @
-- a '+' 'one' '~~' 'one'
-- @
--
-- Note that the left-annihilative property is too strong for many instances. 
-- This is because it requires that any effects that /r/ generates be undone.
--
-- See < https://winterkoninkje.dreamwidth.org/90905.html >.
--
-- This is a required property for bounded lattices.
--
annihilative_addition' :: Eq r => Dioid r => r -> Bool
annihilative_addition' r = Prop.annihilative_on' (~~) (+) one r

------------------------------------------------------------------------------------
-- Properties of idempotent predioids & dioids

-- | \( \forall a, b: a \leq b \Rightarrow a + b = b \)
--
-- This is a required property for semilattices and lattices.
--
monotone_addition' :: Prd r => (Additive-Semigroup) r => r -> r -> Bool
monotone_addition' a b = (a <= b) <==> (a + b =~ b)

-- | \( \forall a : a + a = a \)
--
-- See < https://en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a required property for semilattices and lattices.
--
idempotent_addition :: Eq r => Dioid r => r -> Bool
idempotent_addition = absorbative_addition_on (~~) one

-- | \( \forall a : a * a = a \)
--
-- This is a required property for semilattices and lattices.
--
idempotent_multiplication :: Eq r => Dioid r => r -> Bool
idempotent_multiplication = absorbative_multiplication_on (~~) zero

------------------------------------------------------------------------------------
-- Properties of kleene dioids

{-
-- | \( 1 + \sum_{i=1}^{P+1} a^i = 1 + \sum_{i=1}^{P} a^i \)
--
-- If /a/ is p-stable for some /p/, then we have:
--
-- @
-- 'powers' p a ~~ a '*' 'powers' p a '+' 'one'  ~~ 'powers' p a '*' a '+' 'one' 
-- @
--
-- If '+' and '*' are idempotent then every element is 1-stable:
--
-- @ a '*' a '+' a '+' 'one' = a '+' a '+' 'one' = a '+' 'one' @
--
kleene_pstable :: (Eq r, Dioid r) => Natural -> r -> Bool
kleene_pstable p a = powers p a ~~ powers (p + 1) a

-- | \( x = a * x + b \Rightarrow x = (1 + \sum_{i=1}^{P} a^i) * b \)
--
-- If /a/ is p-stable for some /p/, then we have:
--
kleene_paffine :: (Eq r, Dioid r) => Natural -> r -> r -> Bool
kleene_paffine p a b = kleene_pstable p a ==> x ~~ a * x + b 
  where x = powers p a * b

-- | \( \forall a \in R : a^* = a^* * a + 1 \)
--
-- Closure is /p/-stability for all /a/ in the limit as \( p \to \infinity \).
--
-- One way to think of this property is that all geometric series
-- "converge":
--
-- \( \forall a \in R : 1 + \sum_{i \geq 1} a^i \in R \)
--
kleene_stable :: (Eq r, Dioid r, Kleene r) => r -> Bool
kleene_stable a = star a ~~ star a * a + one

kleene_stable' :: (Eq r, Dioid r, Kleene r) => r -> Bool
kleene_stable' a = star a ~~ one + a * star a

kleene_affine :: (Eq r, Dioid r, Kleene r) => r -> r -> Bool
kleene_affine a b = x ~~ a * x + b where x = star a * b

-- If /R/ is kleene then 'star' must be idempotent:
--
-- @'star' ('star' a) ~~ 'star' a@
--
idempotent_star :: (Eq r, Dioid r, Kleene r) => r -> Bool
idempotent_star = Prop.idempotent star

-- If @r@ is a kleene dioid then 'star' must be monotone:
--
-- @x '<=' y ==> 'star' x '<=' 'star' y@
--
monotone_star :: (Dioid r, Kleene r) => r -> r -> Bool
monotone_star = Prop.monotone_on (<=) (<=) star
-}
