-- | See <https://en.wikipedia.org/wiki/Binary_relation#Properties>.
module Data.Prd.Property (
  -- * Typeclass consistency
    consistent
  -- * Equivalence relations
  , symmetric_eq
  , reflexive_eq
  , transitive_eq
  -- * Partial orders
  -- ** Non-strict partial orders
  , antisymmetric_le
  , reflexive_le
  , transitive_le
  -- ** Connex non-strict partial orders
  , connex_le
  -- ** Strict partial orders
  , asymmetric_lt
  , transitive_lt
  , irreflexive_lt
  -- ** Semiconnex strict partial orders
  , semiconnex_lt
  , trichotomous_lt
  -- ** Semiorders
  , chain_22
  , chain_31
  -- * Properties of generic relations
  , reflexive
  , irreflexive
  , coreflexive
  , quasireflexive
  , transitive
  , euclidean
  , euclidean'
  , connex
  , semiconnex
  , trichotomous
  , symmetric
  , asymmetric
  , antisymmetric
  -- * Extras
  , type Rel
  , xor
  , xor3
  , (==>)
  , iff
  , (<==>)
) where

import Data.Prd
import Prelude hiding (Ord(..))

import qualified Prelude as P

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
    le x1 y1 = maybe False (P.<= EQ) $ pcompare x1 y1

    ge x1 y1 = maybe False (P.>= EQ) $ pcompare x1 y1

    lt x1 y1 = maybe False (P.< EQ) $ pcompare x1 y1

    gt x1 y1 = maybe False (P.> EQ) $ pcompare x1 y1

    cp x1 y1 = maybe False (const True) $ pcompare x1 y1

    eq x1 y1 = maybe False (== EQ) $ pcompare x1 y1

    ne x1 y1 = not $ x1 =~ y1

    sm x1 y1 = not (x1 < y1) && not (x1 > y1)

    ns x1 y1 = not $ x1 ~~ y1

    pcmp x1 y1
      | x1 <= y1 = Just $ if y1 <= x1 then EQ else LT
      | y1 <= x1 = Just GT
      | otherwise = Nothing

-- | \( \forall a, b: (a = b) \Leftrightarrow (b = a) \)
--
-- '=~' is a symmetric relation.
--
-- This is a required property.
--
symmetric_eq :: Prd r => r -> r -> Bool
symmetric_eq = symmetric (=~)

-- | \( \forall a: (a = a) \)
--
-- '=~' is a reflexive relation.
--
-- This is a required property.
--
reflexive_eq :: Prd r => r ->  Bool
reflexive_eq = reflexive (=~) 

-- | \( \forall a, b, c: ((a = b) \wedge (b = c)) \Rightarrow (a = c) \)
--
-- '=~' is a transitive relation.
--
-- This is a required property.
--
transitive_eq :: Prd r => r -> r -> r -> Bool
transitive_eq = transitive (=~)

-- | \( \forall a, b: (a \leq b) \wedge (b \leq a) \Rightarrow a = b \)
--
-- '<=' is an antisymmetric relation.
--
-- This is a required property.
--
antisymmetric_le :: Prd r => r -> r -> Bool
antisymmetric_le = antisymmetric (=~) (<=)

-- | \( \forall a: (a \leq a) \)
--
-- '<=' is a reflexive relation.
--
-- This is a required property.
--
reflexive_le :: Prd r => r ->  Bool
reflexive_le = reflexive (<=) 

-- | \( \forall a, b, c: ((a \leq b) \wedge (b \leq c)) \Rightarrow (a \leq c) \)
--
-- '<=' is an transitive relation.
--
-- This is a required property.
--
transitive_le :: Prd r => r -> r -> r -> Bool
transitive_le = transitive (<=)

-- | \( \forall a, b: ((a \leq b) \vee (b \leq a)) \)
--
-- '<=' is a connex relation.
-- 
connex_le :: Prd r => r -> r -> Bool
connex_le = connex (<=)

-- | \( \forall a, b: (a \lt b) \Rightarrow \neg (b \lt a) \)
--
-- 'lt' is an asymmetric relation.
--
-- This is a required property.
--
asymmetric_lt :: Eq r => Prd r => r -> r -> Bool
asymmetric_lt = asymmetric (<)

-- | \( \forall a: \neg (a \lt a) \)
--
-- 'lt' is an irreflexive relation.
--
-- This is a required property.
--
irreflexive_lt :: Eq r => Prd r => r ->  Bool
irreflexive_lt = irreflexive (<) 

-- | \( \forall a, b, c: ((a \lt b) \wedge (b \lt c)) \Rightarrow (a \lt c) \)
--
-- 'lt' is a transitive relation.
--
-- This is a required property.
--
transitive_lt :: Eq r => Prd r => r -> r -> r -> Bool
transitive_lt = transitive (<)

-- | \( \forall a, b: \neg (a = b) \Rightarrow ((a \lt b) \vee (b \lt a)) \)
--
-- 'lt' is a semiconnex relation.
--
semiconnex_lt :: Eq r => Prd r => r -> r -> Bool
semiconnex_lt = semiconnex (=~) (<)

-- | \( \forall a, b, c: ((a \lt b) \vee (a = b) \vee (b \lt a)) \wedge \neg ((a \lt b) \wedge (a = b) \wedge (b \lt a)) \)
--
-- In other words, exactly one of \(a \lt b\), \(a = b\), or \(b \lt a\) holds.
--
-- If 'lt' is a trichotomous relation then the set is totally ordered.
--
trichotomous_lt :: Eq r => Prd r => r -> r -> Bool
trichotomous_lt = trichotomous (=~) (<)

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

---------------------------------------------------------------------
-- Properties of general relations
---------------------------------------------------------------------

-- | See <https://en.wikipedia.org/wiki/Binary_relation#Properties>.
--
-- Note that these properties do not exhaust all of the possibilities.
--
-- As an example over the natural numbers, the relation \(a \# b \) defined by 
-- \( a > 2 \) is neither symmetric nor antisymmetric, let alone asymmetric.
type Rel r b = r -> r -> b

xor :: Bool -> Bool -> Bool
xor a b = (a || b) && not (a && b)

xor3 :: Bool -> Bool -> Bool -> Bool
xor3 a b c = (a `xor` (b `xor` c)) && not (a && b && c)

infixr 0 ==>

(==>) :: Bool -> Bool -> Bool
(==>) a b = not a || b

iff :: Bool -> Bool -> Bool
iff a b = a ==> b && b ==> a

infixr 1 <==>

(<==>) :: Bool -> Bool -> Bool
(<==>) = iff

-- | \( \forall a: (a \# a) \)
--
-- For example, ≥ is a reflexive relation but > is not.
--
reflexive :: Rel r b -> r -> b
reflexive (#) a = a # a 

-- | \( \forall a: \neg (a \# a) \)
--
-- For example, > is an irreflexive relation, but ≥ is not.
--
irreflexive :: Rel r Bool -> r -> Bool
irreflexive (#) a = not $ a # a

-- | \( \forall a, b: ((a \# b) \wedge (b \# a)) \Rightarrow (a \equiv b) \)
--
-- For example, the relation over the integers in which each odd number is 
-- related to itself is a coreflexive relation. The equality relation is the 
-- only example of a relation that is both reflexive and coreflexive, and any 
-- coreflexive relation is a subset of the equality relation.
--
coreflexive :: Rel r Bool -> Rel r Bool -> Rel r Bool
coreflexive (~~) (#) a b = (a # b) && (b # a) ==> (a ~~ b)

-- | \( \forall a, b: (a \# b) \Rightarrow ((a \# a) \wedge (b \# b)) \)
--
quasireflexive :: Rel r Bool -> Rel r Bool
quasireflexive (#) a b = (a # b) ==> (a # a) && (b # b)

-- | \( \forall a, b, c: ((a \# b) \wedge (b \# c)) \Rightarrow (a \# c) \)
--
-- For example, "is ancestor of" is a transitive relation, while "is parent of" is not.
--
transitive :: Rel r Bool -> r -> Rel r Bool
transitive (#) a b c = (a # b) && (b # c) ==> a # c

-- | \( \forall a, b, c: ((a \# b) \wedge (a \# c)) \Rightarrow (b \# c) \)
--
-- For example, /=/ is an right Euclidean relation because if /x = y/ and /x = z/ then /y = z/.
--
euclidean :: Rel r Bool -> r -> Rel r Bool
euclidean (#) a b c = (a # b) && (a # c) ==> b # c

-- |  \( \forall a, b, c: ((b \# a) \wedge (c \# a)) \Rightarrow (b \# c) \)
--
-- For example, /=/ is a left Euclidean relation because if /x = y/ and /x = z/ then /y = z/.
--
euclidean' :: Rel r Bool -> r -> Rel r Bool
euclidean' (#) a b c = (b # a) && (c # a) ==> b # c

-- | \( \forall a, b: ((a \# b) \vee (b \# a)) \)
--
-- For example, ≥ is a connex relation, while 'divides evenly' is not.
-- 
-- A connex relation cannot be symmetric, except for the universal relation.
--
connex :: Rel r Bool -> Rel r Bool
connex (#) a b = (a # b) || (b # a)

-- | \( \forall a, b: \neg (a \equiv b) \Rightarrow ((a \# b) \vee (b \# a)) \)
--
-- A binary relation is semiconnex if it relates all pairs of _distinct_ elements in some way.
--
-- A relation is connex if and only if it is semiconnex and reflexive.
--
semiconnex :: Rel r Bool -> Rel r Bool -> Rel r Bool
semiconnex (~~) (#) a b = not (a ~~ b) ==> connex (#) a b

-- | \( \forall a, b, c: ((a \# b) \vee (a \doteq b) \vee (b \# a)) \wedge \neg ((a \# b) \wedge (a \doteq b) \wedge (b \# a)) \)
--
-- In other words, exactly one of \(a \# b\), \(a \doteq b\), or \(b \# a\) holds.
-- 	
-- For example, > is a trichotomous relation, while ≥ is not.
--
-- Note that @ trichotomous (>) @ should hold for any 'Ord' instance.
--
trichotomous :: Rel r Bool -> Rel r Bool -> Rel r Bool
trichotomous (~~) (#) a b = xor3 (a # b) (a ~~ b) (b # a)

-- | \( \forall a, b: (a \# b) \Leftrightarrow (b \# a) \)
--
-- For example, "is a blood relative of" is a symmetric relation, because 
-- A is a blood relative of B if and only if B is a blood relative of A.
--
symmetric :: Rel r Bool -> Rel r Bool
symmetric (#) a b = (a # b) <==> (b # a)

-- | \( \forall a, b: (a \# b) \Rightarrow \neg (b \# a) \)
--
-- For example, > is an asymmetric relation, but ≥ is not.
--
-- A relation is asymmetric if and only if it is both antisymmetric and irreflexive.
-- 
asymmetric :: Rel r Bool -> Rel r Bool
asymmetric (#) a b = (a # b) ==> not (b # a)

-- | \( \forall a, b: (a \# b) \wedge (b \# a) \Rightarrow a \equiv b \)
--
-- For example, ≥ is an antisymmetric relation; so is >, but vacuously 
-- (the condition in the definition is always false).
--
antisymmetric :: Rel r Bool -> Rel r Bool -> Rel r Bool
antisymmetric (~~) (#) a b = (a # b) && (b # a) ==> (a ~~ b)
