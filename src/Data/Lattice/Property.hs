{-# LANGUAGE DataKinds                  #-}
module Data.Lattice.Property where

import Data.Order.Property
import Data.Order.Syntax
import Data.Lattice
import Prelude hiding (Eq(..), Ord(..), Bounded, not)


coheyting0 :: Coheyting a => a -> a -> a -> Bool
coheyting0 x y z = x \\ y <= z <=> x <= y \/ z

coheyting1 :: Coheyting a => a -> a -> a -> Bool
coheyting1 x y z = x \\ y >= (x /\ z) \\ y

coheyting2 :: Coheyting a => a -> a -> a -> Bool
coheyting2 x y z = x \\ (y /\ z) >= x \\ y

coheyting3 :: Coheyting a => a -> a -> a -> Bool
coheyting3 x y z = x >= y ==> x \\ z >= y \\ z

coheyting4 :: Coheyting a => a -> a -> a -> Bool
coheyting4 x y z = z \\ (x \/ y) == z \\ x \\ y

coheyting5 :: Coheyting a => a -> a -> a -> Bool
coheyting5 x y z = (y \/ z) \\ x == y \\ x \/ z \\ x

coheyting6 :: Coheyting a => a -> a -> Bool
coheyting6 x y = x >= x \\ y

coheyting7 :: Coheyting a => a -> a -> Bool
coheyting7 x y = x \/ y \\ x == x \/ y

coheyting8 :: forall a. Coheyting a => a -> Bool
coheyting8 _ = non bottom == top @a && non top == bottom @a

-- Double co-negation is a co-monad.
coheyting9 :: Coheyting a => a -> a -> Bool
coheyting9 x y = x /\ non y >= x \\ y

coheyting10 :: Coheyting a => a -> a -> Bool
coheyting10 x y = x >= y <=> y \\ x == bottom

coheyting11 :: Coheyting a => a -> a -> Bool
coheyting11 x y = non (x /\ y) >= non x

coheyting12 :: Coheyting a => a -> a -> Bool
coheyting12 x y = non (y \\ x) == non (non x) \/ non y

coheyting13 :: Coheyting a => a -> a -> Bool
coheyting13 x y = non (x /\ y) == non x \/ non y

coheyting14 :: Coheyting a => a -> Bool
coheyting14 x = x \/ non x == top

coheyting15 :: Coheyting a => a -> Bool
coheyting15 x = non (non (non x)) == non x

coheyting16 :: Coheyting a => a -> Bool
coheyting16 x = non (non (x /\ non x)) == bottom

coheyting17 :: Coheyting a => a -> Bool
coheyting17 x = x >= non (non x)

coheyting18 :: Coheyting c => c -> Bool
coheyting18 x = x == boundary x \/ (non . non) x

coheyting19 :: Coheyting a => a -> a -> Bool
coheyting19 x y = boundary (x /\ y) == (boundary x /\ y) \/ (x /\ boundary y)  -- (Leibniz rule)

coheyting20 :: Coheyting a => a -> a -> Bool
coheyting20 x y = boundary (x \/ y) \/ boundary (x /\ y) == boundary x \/ boundary y


heyting0 :: Heyting a => a -> a -> a -> Bool
heyting0 x y z = x /\ y <= z <=> x <= y // z

heyting1 :: Heyting a => a -> a -> a -> Bool
heyting1 x y z = x // y <= x // (y \/ z)

heyting2 :: Heyting a => a -> a -> a -> Bool
heyting2 x y z = (x \/ z) // y <= x // y

heyting3 :: Heyting a => a -> a -> a -> Bool
heyting3 x y z = x <= y ==> z // x <= z // y

heyting4 :: Heyting a => a -> a -> a -> Bool
heyting4 x y z = (x /\ y) // z == x // y // z

heyting5 :: Heyting a => a -> a -> a -> Bool
heyting5 x y z = x // (y /\ z) == x // y /\ x // z

heyting6 :: Heyting a => a -> a -> Bool
heyting6 x y = y <= x // (x /\ y)

heyting7 :: Heyting a => a -> a -> Bool
heyting7 x y = x /\ x // y == x /\ y

heyting8 :: forall a. Heyting a => a -> Bool
heyting8 _ = neg bottom == top @a && neg top == bottom @a

-- Double negation is a monad.
heyting9 :: Heyting a => a -> a -> Bool
heyting9 x y = neg x \/ y <= x // y

heyting10 :: Heyting a => a -> a -> Bool
heyting10 x y = x <= y <=> x // y == top

heyting11 :: Heyting a => a -> a -> Bool
heyting11 x y = neg (x \/ y) <= neg x

heyting12 :: Heyting a => a -> a -> Bool
heyting12 x y = neg (x // y) == neg (neg x) /\ neg y

heyting13 :: Heyting a => a -> a -> Bool
heyting13 x y = neg (x \/ y) == neg x /\ neg y

heyting14 :: Heyting a => a -> Bool
heyting14 x = x /\ neg x == bottom

heyting15 :: Heyting a => a -> Bool
heyting15 x = neg (neg (neg x)) == neg x

heyting16 :: Heyting a => a -> Bool
heyting16 x = neg (neg (x \/ neg x)) == top

heyting17 :: Heyting a => a -> Bool
heyting17 x = x <= neg (neg x)

-- 
-- x '\\' x           = 'top'
-- x '/\' (x '\\' y)  = x '/\' y
-- y '/\' (x '\\' y)  = y
-- x '\\' (y '\\' z) = (x '/\' y) '\\' z
-- x '\\' (y '/\' z)  = (x '\\' y) '/\' (x '\\' z)
-- 'neg' (x '/\' y)    = 'neg' (x '\/' y)
-- 'neg' (x '\/' y)    = 'neg' x '/\' 'neg' y
-- (x '\\' y) '\/' x '<=' y
-- y '<=' (x '\\' x '/\' y)
-- x '<=' y => (z '\\' x) '<=' (z '\\' y)
-- x '<=' y => (x '\\' z) '<=' (y '\\' z)
-- x '<=' y <=> x '\\' y '==' 'top'
-- x '/\' y '<=' z <=> x '<=' (y '\\' z) <=> y '<=' (x '\\' z)
-- 
--


-- adjointL $ ConnL (\x -> y \\ not x) (\z -> not z // not y)
symmetric1 :: Biheyting a => a -> Bool
symmetric1 x = neg x <= non x

symmetric2 :: Symmetric a => a -> Bool
symmetric2 x = (neg . neg) x == (converseR . converseL) x

symmetric3 :: Symmetric a => a -> Bool
symmetric3 x = (non . non) x == (converseL . converseR) x

symmetric4 :: Symmetric a => a -> Bool
symmetric4 x = non x == (converseL . not) x && neg x == (not . converseL) x

symmetric5 :: Symmetric a => a -> Bool
symmetric5 x = non x == (not . converseR) x && neg x == (converseR . not) x

symmetric6 :: Heyting a => a -> Bool
symmetric6 x = neg x \/ neg (neg x) == top

symmetric7 :: Symmetric a => a -> a -> Bool
symmetric7 x y = not (x /\ y) == not x \/ not y

symmetric8 :: Symmetric a => a -> a -> Bool
symmetric8 x y = (not . not) (x \/ y) == not (not x) \/ not (not y)

symmetric9 :: Symmetric a => a -> a -> Bool
symmetric9 x y = not (x \/ y) == not x /\ not y

symmetric10 :: Symmetric a => a -> a -> Bool
symmetric10 x y = converseL (x \/ y) == converseL x \/ converseL y

symmetric11 :: Symmetric a => a -> a -> Bool
symmetric11 x y = converseR (x /\ y) == converseR x /\ converseR y

symmetric12 :: Symmetric a => a -> a -> Bool
symmetric12 x y = converseL (x /\ y) == (non . non) (converseL x /\ converseL y)

symmetric13 :: Symmetric a => a -> a -> Bool
symmetric13 x y = converseR (x \/ y) == (neg . neg) (converseR x \/ converseR y)


boolean0 :: Biheyting a => a -> Bool
boolean0 x = neg x == non x

boolean1 :: Heyting a => a -> Bool
boolean1 x = neg (neg x) == x

boolean2 :: Heyting a => a -> Bool
boolean2 x = x \/ neg x == top

boolean3 :: Coheyting a => a -> Bool
boolean3 x = x /\ non x == bottom 

boolean4 :: Heyting a => a -> a -> Bool
boolean4 x y = (x <= y) // (neg y <= neg x)

boolean5 :: Biheyting a => a -> a -> Bool
boolean5 x y = x \\ y == neg (neg y // neg x)

boolean6 :: Biheyting a => a -> a -> Bool
boolean6 x y = x // y == non (non y \\ non x)

{-
infix 4 `joinLe`
-- | The partial ordering induced by the join-semilattice structure.
--
--
-- Normally when /a/ implements 'Ord' we should have:
-- @ 'joinLe' x y = x '<=' y @
--
joinLe :: Lattice a => a -> a -> Bool
joinLe x y = y == x \/ y

infix 4 `joinGe`
-- | The partial ordering induced by the join-semilattice structure.
--
-- Normally when /a/ implements 'Ord' we should have:
-- @ 'joinGe' x y = x '>=' y @
--
joinGe :: Lattice a => a -> a -> Bool
joinGe x y = x == x \/ y

-- | Partial version of 'Data.Ord.compare'.
--
-- Normally when /a/ implements 'Preorder' we should have:
-- @ 'pcompareJoin' x y = 'pcompare' x y @
--
pcompareJoin :: Lattice a => a -> a -> Maybe Ordering
pcompareJoin x y
  | x == y = Just EQ
  | joinLe x y && x /= y = Just LT
  | joinGe x y && x /= y = Just GT
  | otherwise = Nothing

infix 4 `meetLe`
-- | The partial ordering induced by the meet-semilattice structure.
--
-- Normally when /a/ implements 'Preorder' we should have:
-- @ 'meetLe' x y = x '<~' y @
--
meetLe :: Lattice a => a -> a -> Bool
meetLe x y = x == x /\ y

infix 4 `meetGe`
-- | The partial ordering induced by the meet-semilattice structure.
--
-- Normally when /a/ implements 'Preorder' we should have:
-- @ 'meetGe' x y = x '>~' y @
--
meetGe :: Lattice a => a -> a -> Bool
meetGe x y = y == x /\ y

-- | Partial version of 'Data.Ord.compare'.
--
-- Normally when /a/ implements 'Preorder' we should have:
-- @ 'pcompareJoin' x y = 'pcompare' x y @
--
pcompareMeet :: Lattice a => a -> a -> Maybe Ordering
pcompareMeet x y
  | x == y = Just EQ
  | meetLe x y && x /= y = Just LT
  | meetGe x y && x /= y = Just GT
  | otherwise = Nothing

-- | \( \forall a \in R: a \/ a = a \)
--
-- @ 'idempotent_join' = 'absorbative' 'top' @
-- 
-- See < https:\\en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a required property.
--
idempotent_join :: Lattice r => r -> Bool
idempotent_join = idempotent_join_on (~~)

idempotent_join_on :: Semilattice 'L r => Rel r b -> r -> b
idempotent_join_on (~~) r = (\/) r r ~~ r

-- | \( \forall a, b, c \in R: (a \/ b) \/ c = a \/ (b \/ c) \)
--
-- This is a required property.
--
associative_join :: Lattice r => r -> r -> r -> Bool
associative_join = associative_on (~~) (\/) 

associative_join_on :: Semilattice 'L r => Rel r b -> r -> r -> r -> b
associative_join_on (=~) = associative_on (=~) (\/) 

-- | \( \forall a, b, c: (a \# b) \# c \doteq a \# (b \# c) \)
--
associative_on :: Rel r b -> (r -> r -> r) -> (r -> r -> r -> b)
associative_on (~~) (#) a b c = ((a # b) # c) ~~ (a # (b # c))

-- | \( \forall a, b \in R: a \/ b = b \/ a \)
--
-- This is a required property.
--
commutative_join :: Lattice r => r -> r -> Bool
commutative_join = commutative_join_on (~~)

commutative_join_on :: Semilattice 'L r => Rel r b -> r -> r -> b
commutative_join_on (=~) = commutative_on (=~) (\/) 


-- | \( \forall a, b: a \# b \doteq b \# a \)
--
commutative_on :: Rel r b -> (r -> r -> r) -> r -> r -> b
commutative_on (=~) (#) a b = (a # b) =~ (b # a)

-- | \( \forall a, b \in R: a /\ b \/ b = b \)
--
-- Absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative' 'top' a = a \/ a = a
-- @
--
-- This is a required property.
--
absorbative_on :: Lattice r => Rel r Bool -> r -> r -> Bool
absorbative_on (=~) x y = (x /\ y \/ y) =~ y

-- | \( \forall a, b \in R: a \/ b /\ b = b \)
--
-- Absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative'' 'bottom' a = a \/ a = a
-- @
--
-- This is a required property.
--
absorbative_on' :: Lattice r => Rel r Bool -> r -> r -> Bool
absorbative_on' (=~) x y = ((x \/ y) /\ y) =~ y

distributive :: Lattice r => r -> r -> r -> Bool
distributive = distributive_on (~~) (/\) (\/)

codistributive :: Lattice r => r -> r -> r -> Bool
codistributive = distributive_on (~~) (\/) (/\)

distributive_on :: Rel r b -> (r -> r -> r) -> (r -> r -> r) -> (r -> r -> r -> b)
distributive_on (=~) (#) (%) a b c = ((a # b) % c) =~ ((a % c) # (b % c))

distributive_on' :: Rel r b -> (r -> r -> r) -> (r -> r -> r) -> (r -> r -> r -> b)
distributive_on' (=~) (#) (%) a b c = (c % (a # b)) =~ ((c % a) # (c % b))

-- | @ 'glb' x x y = x @
--
-- See < https:\\en.wikipedia.org/wiki/Median_algebra >.
majority_glb :: Lattice r => r -> r -> Bool
majority_glb x y = glb x y y ~~ y

-- | @ 'glb' x y z = 'glb' z x y @
--
commutative_glb :: Lattice r => r -> r -> r -> Bool
commutative_glb x y z = glb x y z ~~ glb z x y

-- | @ 'glb' x y z = 'glb' x z y @
--
commutative_glb' :: Lattice r => r -> r -> r -> Bool
commutative_glb' x y z = glb x y z ~~ glb x z y

-- | @ 'glb' ('glb' x w y) w z = 'glb' x w ('glb' y w z) @
--
associative_glb :: Lattice r => r -> r -> r -> r -> Bool
associative_glb x y z w = glb (glb x w y) w z ~~ glb x w (glb y w z)

distributive_glb :: (Bounded r, Lattice r) => r -> r -> r -> Bool
distributive_glb x y z = glb x y z ~~ lub x y z

interval_glb :: Lattice r => r -> r -> r -> Bool
interval_glb x y z = glb x y z ~~ y ==> (x <~ y && y <~ z) || (z <~ y && y <~ x)

-- |  \( \forall a, b, c: a \leq b \Rightarrow a \/ (c /\ b) \eq (a \/ c) /\ b \)
--
-- See < https:\\en.wikipedia.org/wiki/Distributivity_(order_theory)#Distributivity_for_semilattices >
--
modular :: Lattice r => r -> r -> r -> Bool
modular a b c = a \/ (c /\ b) ~~ (a \/ c) /\ b 


-}
