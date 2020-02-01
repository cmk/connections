-- | See <https://en.wikipedia.org/wiki/Binary_relation#Properties>.
module Data.Prd.Property (
  -- * Typeclass consistency
    consistent
  -- * Equivalence relations
  , symmetric
  , reflexive_eq
  , transitive_eq
  -- * Partial orders
  -- ** Non-strict partial orders
  , antisymmetric
  , reflexive_le
  , transitive_le
  -- ** Connex non-strict partial orders
  , connex
  -- ** Strict partial orders
  , asymmetric
  , transitive_lt
  , irreflexive_lt
  -- ** Semiconnex strict partial orders
  , semiconnex
  , trichotomous
  -- ** Semiorders
  , chain_22
  , chain_31
) where

import Data.Prd
import Test.Logic
import Prelude hiding (Ord(..))

import qualified Prelude as P
import qualified Test.Relation as R

-- | Check that 'Prd' methods are internally consistent.
--
-- This is a required property.
--
consistent :: Prd r => r -> r -> Bool
consistent x y = 
  ((x <= y) == le x y) &&
  ((x >= y) == ge x y) &&
  ((x <  y) == lt x y) &&
  ((x >  y) == gt x y) &&
  ((x ?~ y) == cp x y) &&
  ((x =~ y) == eq x y) &&
  ((x /~ y) == ne x y) &&
  ((x ~~ y) == sm x y) &&
  ((x !~ y) == ns x y) &&
  (pcompare x y == pcmp x y)

  where
    le x y = maybe False (P.<= EQ) $ pcompare x y

    ge x y = maybe False (P.>= EQ) $ pcompare x y

    lt x y = maybe False (P.< EQ) $ pcompare x y

    gt x y = maybe False (P.> EQ) $ pcompare x y

    cp x y = maybe False (const True) $ pcompare x y

    eq x y = maybe False (== EQ) $ pcompare x y

    ne x y = not $ x =~ y

    sm x y = not (x < y) && not (x > y)

    ns x y = not $ x ~~ y

    pcmp x y 
      | x <= y = Just $ if y <= x then EQ else LT
      | y <= x = Just GT
      | otherwise = Nothing


-- | \( \forall a, b: (a = b) \Leftrightarrow (b = a) \)
--
-- '=~' is a symmetric relation.
--
-- This is a required property.
--
symmetric :: Prd r => r -> r -> Bool
symmetric = R.symmetric (=~)

-- | \( \forall a: (a = a) \)
--
-- '=~' is a reflexive relation.
--
-- This is a required property.
--
reflexive_eq :: Prd r => r ->  Bool
reflexive_eq = R.reflexive (=~) 

-- | \( \forall a, b, c: ((a = b) \wedge (b = c)) \Rightarrow (a = c) \)
--
-- '=~' is a transitive relation.
--
-- This is a required property.
--
transitive_eq :: Prd r => r -> r -> r -> Bool
transitive_eq = R.transitive (=~)

-- | \( \forall a, b: (a \leq b) \wedge (b \leq a) \Rightarrow a = b \)
--
-- '<=' is an antisymmetric relation.
--
-- This is a required property.
--
antisymmetric :: Prd r => r -> r -> Bool
antisymmetric = R.antisymmetric_on (=~) (<=)

-- | \( \forall a: (a \leq a) \)
--
-- '<=' is a reflexive relation.
--
-- This is a required property.
--
reflexive_le :: Prd r => r ->  Bool
reflexive_le = R.reflexive (<=) 

-- | \( \forall a, b, c: ((a \leq b) \wedge (b \leq c)) \Rightarrow (a \leq c) \)
--
-- '<=' is an transitive relation.
--
-- This is a required property.
--
transitive_le :: Prd r => r -> r -> r -> Bool
transitive_le = R.transitive (<=)

-- | \( \forall a, b: ((a \leq b) \vee (b \leq a)) \)
--
-- '<=' is a connex relation.
-- 
connex :: Prd r => r -> r -> Bool
connex = R.connex (<=)

-- | \( \forall a, b: (a \lt b) \Rightarrow \neg (b \lt a) \)
--
-- 'lt' is an asymmetric relation.
--
-- This is a required property.
--
asymmetric :: Eq r => Prd r => r -> r -> Bool
asymmetric = R.asymmetric (<)

-- | \( \forall a: \neg (a \lt a) \)
--
-- 'lt' is an irreflexive relation.
--
-- This is a required property.
--
irreflexive_lt :: Eq r => Prd r => r ->  Bool
irreflexive_lt = R.irreflexive (<) 

-- | \( \forall a, b, c: ((a \lt b) \wedge (b \lt c)) \Rightarrow (a \lt c) \)
--
-- 'lt' is a transitive relation.
--
-- This is a required property.
--
transitive_lt :: Eq r => Prd r => r -> r -> r -> Bool
transitive_lt = R.transitive (<)

-- | \( \forall a, b: \neg (a = b) \Rightarrow ((a \lt b) \vee (b \lt a)) \)
--
-- 'lt' is a semiconnex relation.
--
semiconnex :: Eq r => Prd r => r -> r -> Bool
semiconnex = R.semiconnex_on (=~) (<)

-- | \( \forall a, b, c: ((a \lt b) \vee (a = b) \vee (b \lt a)) \wedge \neg ((a \lt b) \wedge (a = b) \wedge (b \lt a)) \)
--
-- In other words, exactly one of \(a \lt b\), \(a = b\), or \(b \lt a\) holds.
--
-- If 'lt' is a trichotomous relation then the set is totally ordered.
--
trichotomous :: Eq r => Prd r => r -> r -> Bool
trichotomous = R.trichotomous_on (=~) (<)

-- | \( \forall x, y, z, w: x \lt y \wedge y \sim z \wedge z \lt w \Rightarrow x \lt w \) 
--
-- A semiorder does not allow 2-2 chains.
--
chain_22 :: Eq r => Prd r => r -> r -> r -> r -> Bool
chain_22 x y z w = x < y && y ~~ z && z < w ==> x < w

-- \( \forall x, y, z, w: x \lt y \wedge y \lt z \wedge y \sim w \Rightarrow \neg (x \sim w \wedge z \sim w) \) (3-1 chain)
--
-- A semiorder does not allow 3-1 chains.
--
chain_31 :: Eq r => Prd r => r -> r -> r -> r -> Bool
chain_31 x y z w = x < y && y < z && y ~~ w ==> not (x ~~ w && z ~~ w)
