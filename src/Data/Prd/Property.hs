-- | See <https://en.wikipedia.org/wiki/Binary_relation#Properties>.
module Data.Prd.Property (
  -- * Equivalence relations
    symmetric
  , coreflexive
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
import Data.Prd.Lattice
import Test.Util
import Prelude hiding (Ord(..))

import qualified Prelude as P
import qualified Test.Relation as R

-- | \( \forall a, b: (a \eq b) \Leftrightarrow (b \eq a) \)
--
-- '=~' is a symmetric relation.
--
-- This is a required property.
--
symmetric :: Prd r => r -> r -> Bool
symmetric = R.symmetric (=~)

-- | \( \forall x, y: x \eq y \Leftrightarrow x == y \)
--
-- '=~' is a coreflexive relation.
--
-- See <https://en.wikipedia.org/wiki/Reflexive_relation#Related_terms>.
--
-- This is a required property.
--
coreflexive :: (Eq r, Prd r) => r -> r -> Bool
coreflexive x y = x =~ y ==> x == y

-- | \( \forall a: (a \eq a) \)
--
-- '=~' is a reflexive relation.
--
-- This is a required property.
--
reflexive_eq :: Prd r => r ->  Bool
reflexive_eq = R.reflexive (=~) 

-- | \( \forall a, b, c: ((a \eq b) \wedge (b \eq c)) \Rightarrow (a \eq c) \)
--
-- '=~' is a transitive relation.
--
-- This is a required property.
--
transitive_eq :: Prd r => r -> r -> r -> Bool
transitive_eq = R.transitive (=~)

-- | \( \forall a, b: (a \leq b) \wedge (b \leq a) \Rightarrow a \eq b \)
--
-- '<~' is an antisymmetric relation.
--
-- This is a required property.
--
antisymmetric :: Prd r => r -> r -> Bool
antisymmetric = R.antisymmetric_on (=~) (<~)

-- | \( \forall a: (a \leq a) \)
--
-- '<~' is a reflexive relation.
--
-- This is a required property.
--
reflexive_le :: Prd r => r ->  Bool
reflexive_le = R.reflexive (<~) 

-- | \( \forall a, b, c: ((a \leq b) \wedge (b \leq c)) \Rightarrow (a \leq c) \)
--
-- '<~' is an transitive relation.
--
-- This is a required property.
--
transitive_le :: Prd r => r -> r -> r -> Bool
transitive_le = R.transitive (<~)

-- | \( \forall a, b: ((a \leq b) \vee (b \leq a)) \)
--
-- '<~' is a connex relation.
-- 
connex :: Prd r => r -> r -> Bool
connex = R.connex (<~)

-- | \( \forall a, b: (a \lt b) \Rightarrow \neg (b \lt a) \)
--
-- 'lt' is an asymmetric relation.
--
-- This is a required property.
--
asymmetric :: Eq r => Prd r => r -> r -> Bool
asymmetric = R.asymmetric lt

-- | \( \forall a: \neg (a \lt a) \)
--
-- 'lt' is an irreflexive relation.
--
-- This is a required property.
--
irreflexive_lt :: Eq r => Prd r => r ->  Bool
irreflexive_lt = R.irreflexive lt 

-- | \( \forall a, b, c: ((a \lt b) \wedge (b \lt c)) \Rightarrow (a \lt c) \)
--
-- 'lt' is a transitive relation.
--
-- This is a required property.
--
transitive_lt :: Eq r => Prd r => r -> r -> r -> Bool
transitive_lt = R.transitive lt

-- | \( \forall a, b: \neg (a \eq b) \Rightarrow ((a \lt b) \vee (b \lt a)) \)
--
-- 'lt' is a semiconnex relation.
--
semiconnex :: Eq r => Prd r => r -> r -> Bool
semiconnex = R.semiconnex_on (=~) lt

-- | \( \forall a, b, c: ((a \lt b) \vee (a \eq b) \vee (b \lt a)) \wedge \neg ((a \lt b) \wedge (a \eq b) \wedge (b \lt a)) \)
--
-- In other words, exactly one of \(a \lt b\), \(a \eq b\), or \(b \lt a\) holds.
--
-- If 'lt' is a trichotomous relation then the set is totally ordered.
--
trichotomous :: Eq r => Prd r => r -> r -> Bool
trichotomous = R.trichotomous_on (=~) lt

-- | \( \forall x, y, z, w: x \lt y \wedge y \sim z \wedge z \lt w \Rightarrow x \lt w \) 
--
-- A semiorder does not allow 2-2 chains.
--
chain_22 :: Eq r => Prd r => r -> r -> r -> r -> Bool
chain_22 x y z w = x `lt` y && y ~~ z && z `lt` w ==> x `lt` w

-- \( \forall x, y, z, w: x \lt y \wedge y \lt z \wedge y \sim w \Rightarrow \neg (x \sim w \wedge z \sim w) \) (3-1 chain)
--
-- A semiorder does not allow 3-1 chains.
--
chain_31 :: Eq r => Prd r => r -> r -> r -> r -> Bool
chain_31 x y z w = x `lt` y && y `lt` z && y ~~ w ==> not (x ~~ w && z ~~ w)
