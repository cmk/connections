{-# Language AllowAmbiguousTypes #-}
{-# LANGUAGE Safe #-}

module Data.Dioid.Property (
  -- * Properties of dioids
    ordered_preordered
  , ordered_monotone_zero
  , ordered_monotone_addition
  , ordered_positive_addition
  , ordered_monotone_multiplication
  , ordered_annihilative_unit 
  , ordered_idempotent_addition
  , ordered_positive_multiplication
  -- * Properties of absorbative dioids 
  , absorbative_addition
  , absorbative_addition'
  , idempotent_addition
  , absorbative_multiplication
  , absorbative_multiplication' 
  -- * Properties of annihilative dioids 
  , annihilative_addition 
  , annihilative_addition' 
  , codistributive
  -- * Properties of general pre-dioids & dioids
{-
    neutral_addition_on
  , neutral_multiplication_on
  , associative_addition_on 
  , associative_multiplication_on
  , commutative_addition_on 
  , commutative_multiplication_on
  , distributive_on 
  , nonunital_on
  , annihilative_multiplication_on 
-}
  -- * Properties of idempotent pre-dioids & dioids 
  -- * Properties of selective pre-dioids & dioids 
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
import Test.Util ((<==>),(==>))
import Data.Semigroup.Additive
import Data.Semigroup.Multiplicative
import qualified Test.Function  as Prop
import qualified Test.Operation as Prop hiding (distributive_on)
import qualified Data.Semiring.Property as Prop

import Prelude hiding (Num(..), sum)

------------------------------------------------------------------------------------
-- Properties of ordered semirings (aka dioids).

-- | '<~' is a preordered relation relative to '+'.
--
-- This is a required property.
--
ordered_preordered :: Prd r => (Additive-Semigroup) r => r -> r -> Bool
ordered_preordered a b = a <~ add a b

-- | 'zero' is a minimal or least element of @r@.
--
-- This is a required property.
--
ordered_monotone_zero :: Prd r => (Additive-Monoid) r => r -> Bool
ordered_monotone_zero a = zero ?~ a ==> zero <~ a 

-- | \( \forall a, b, c: b \leq c \Rightarrow b + a \leq c + a
--
-- In an ordered semiring this follows directly from the definition of '<~'.
--
-- Compare 'cancellative_addition'.
-- 
-- This is a required property.
--
ordered_monotone_addition :: Prd r => (Additive-Semigroup) r => r -> r -> r -> Bool
ordered_monotone_addition a = Prop.monotone_on (<~) (<~) (add a)

-- |  \( \forall a, b: a + b = 0 \Rightarrow a = 0 \wedge b = 0 \)
--
-- This is a required property.
--
ordered_positive_addition :: Prd r => (Additive-Monoid) r => r -> r -> Bool
ordered_positive_addition a b = add a b =~ zero ==> a =~ zero && b =~ zero

-- | \( \forall a, b, c: b \leq c \Rightarrow b * a \leq c * a
--
-- In an ordered semiring this follows directly from 'distributive' and the definition of '<~'.
--
-- Compare 'cancellative_multiplication'.
--
-- This is a required property.
--
ordered_monotone_multiplication :: Prd r => (Multiplicative-Semigroup) r => r -> r -> r -> Bool
ordered_monotone_multiplication a = Prop.monotone_on (<~) (<~) (mul a)

-- | '<~' is consistent with annihilativity.
--
-- This means that a dioid with an annihilative multiplicative one must satisfy:
--
-- @
-- ('one' <~) ≡ ('one' ==)
-- @
--
ordered_annihilative_unit :: Prd r => (Multiplicative-Monoid) r => r -> Bool
ordered_annihilative_unit a = one <~ a <==> one =~ a

-- | \( \forall a, b: a \leq b \Rightarrow a + b = b
--
ordered_idempotent_addition :: Prd r => (Additive-Semigroup) r => r -> r -> Bool
ordered_idempotent_addition a b = (a <~ b) <==> (add a b =~ b)

-- |  \( \forall a, b: a * b = 0 \Rightarrow a = 0 \vee b = 0 \)
--
-- Dioids which are groups wrt multiplication are often referred to as positive dioids or semi-fields
--
ordered_positive_multiplication :: Dioid r => r -> r -> Bool
ordered_positive_multiplication a b = a * b =~ zero ==> a =~ zero || b =~ zero

------------------------------------------------------------------------------------
-- Properties of idempotent & absorbative semirings

-- | \( \forall a, b \in R: a * b + b = b \)
--
-- Right-additive absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_addition' 'one' a ~~ a + a ~~ a
-- @
--
absorbative_addition :: Eq r => Predioid r => r -> r -> Bool
absorbative_addition a b = a * b + b ~~ b

idempotent_addition :: Eq r => Dioid r => r -> Bool
idempotent_addition = absorbative_addition one
 
-- | \( \forall a, b \in R: b + b * a = b \)
--
-- Left-additive absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_addition' 'one' a ~~ a + a ~~ a
-- @
--
absorbative_addition' :: Eq r => Predioid r => r -> r -> Bool
absorbative_addition' a b = b + b * a ~~ b

-- | \( \forall a, b \in R: (a + b) * b = b \)
--
-- Right-mulitplicative absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_multiplication' 'zero' a ~~ a '*' a ~~ a
-- @
--
-- See < https://en.wikipedia.org/wiki/Absorption_law >.
--
absorbative_multiplication :: Eq r => Predioid r => r -> r -> Bool
absorbative_multiplication a b = (a + b) * b ~~ b

--absorbative_multiplication a b c = (a + b) * c ~~ c
--kleene a = 
--  absorbative_multiplication (star a) one a && absorbative_multiplication one (star a) a 

-- | \( \forall a, b \in R: b * (b + a) = b \)
--
-- Left-mulitplicative absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_multiplication'' 'zero' a ~~ a '*' a ~~ a
-- @
--
-- See < https://en.wikipedia.org/wiki/Absorption_law >.
--
absorbative_multiplication' :: Eq r => Predioid r => r -> r -> Bool
absorbative_multiplication' a b = b * (b + a) ~~ b

------------------------------------------------------------------------------------
-- Properties of idempotent and annihilative dioids.

-- | \( \forall a \in R: o + a = o \)
--
-- A unital semiring with a right-annihilative muliplicative one must satisfy:
--
-- @
-- 'one' + a ~~ 'one'
-- @
--
-- For a dioid this is equivalent to:
-- 
-- @
-- ('one' '<~') ~~ ('one' '~~')
-- @
--
-- For 'Alternative' instances this is known as the left-catch law:
--
-- @
-- 'pure' a '<|>' _ ~~ 'pure' a
-- @
--
annihilative_addition :: Eq r => Dioid r => r -> Bool
annihilative_addition r = Prop.annihilative_on (~~) (+) one r

-- | \( \forall a \in R: a + o = o \)
--
-- A unital semiring with a left-annihilative muliplicative one must satisfy:
--
-- @
-- a '+' 'one' ~~ 'one'
-- @
--
-- Note that the left-annihilative property is too strong for many instances. 
-- This is because it requires that any effects that /r/ generates be undone.
--
-- See < https://winterkoninkje.dreamwidth.org/90905.html >.
--
annihilative_addition' :: Eq r => Dioid r => r -> Bool
annihilative_addition' r = Prop.annihilative_on' (~~) (+) one r

-- | \( \forall a, b, c \in R: c + (a * b) \equiv (c + a) * (c + b) \)
--
-- A right-codistributive semiring has a right-annihilative muliplicative one:
--
-- @ 'codistributive' 'one' a 'zero' ~~ 'one' ~~ 'one' '+' a @
--
-- idempotent mulitiplication:
--
-- @ 'codistributive' 'zero' 'zero' a ~~ a ~~ a '*' a @
--
-- and idempotent addition:
--
-- @ 'codistributive' a 'zero' a ~~ a ~~ a '+' a @
--
-- Furthermore if /R/ is commutative then it is a right-distributive lattice.
--
codistributive :: Eq r => Dioid r => r -> r -> r -> Bool
codistributive = Prop.distributive_on' (~~) (*) (+)

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
-- @x '<~' y ==> 'star' x '<~' 'star' y@
--
monotone_star :: (Dioid r, Kleene r) => r -> r -> Bool
monotone_star = Prop.monotone_on (<~) (<~) star
-}
