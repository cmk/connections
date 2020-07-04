{-# LANGUAGE DataKinds                  #-}
module Data.Lattice.Property where

import Data.Connection.Conn
import Data.Connection.Property
import Data.Order
import Data.Order.Property
import Data.Order.Syntax
import Data.Lattice
import Prelude hiding (Eq(..), Ord(..), Bounded)

--foo x y z = x // y <= x // y /\ z
--foo x z y = x /\ z // y <= x // y
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

heytingL0 :: Heyting 'L a => a -> a -> a -> Bool
heytingL0 x y z = x \\ y <= z <=> x <= y \/ z

heytingL1 :: Heyting 'L a => a -> a -> a -> Bool
heytingL1 x y z = x \\ y >= (x /\ z) \\ y

heytingL2 :: Heyting 'L a => a -> a -> a -> Bool
heytingL2 x y z = x \\ (y /\ z) >= x \\ y

heytingL3 :: Heyting 'L a => a -> a -> a -> Bool
heytingL3 x y z = x >= y ==> x \\ z >= y \\ z

heytingL4 :: Heyting 'L a => a -> a -> a -> Bool
heytingL4 x y z = z \\ (x \/ y) == z \\ x \\ y

heytingL5 :: Heyting 'L a => a -> a -> a -> Bool
heytingL5 x y z = (y \/ z) \\ x == y \\ x \/ z \\ x

heytingL6 :: Heyting 'L a => a -> a -> Bool
heytingL6 x y = x >= x \\ y

heytingL7 :: Heyting 'L a => a -> a -> Bool
heytingL7 x y = x \/ y \\ x == x \/ y

heytingL8 :: forall a. Heyting 'L a => a -> Bool
heytingL8 _ = non bottom == top @a && non top == bottom @a

-- Double co-negation is a co-monad.
heytingL9 :: Heyting 'L a => a -> a -> Bool
heytingL9 x y = x /\ non y >= x \\ y

heytingL10 :: Heyting 'L a => a -> a -> Bool
heytingL10 x y = x >= y <=> y \\ x == bottom

heytingL11 :: Heyting 'L a => a -> a -> Bool
heytingL11 x y = non (x /\ y) >= non x

heytingL12 :: Heyting 'L a => a -> a -> Bool
heytingL12 x y = non (y \\ x) == non (non x) \/ non y

heytingL13 :: Heyting 'L a => a -> a -> Bool
heytingL13 x y = non (x /\ y) == non x \/ non y

heytingL14 :: Heyting 'L a => a -> Bool
heytingL14 x = x \/ non x == top

heytingL15 :: Heyting 'L a => a -> Bool
heytingL15 x = non (non (non x)) == non x

heytingL16 :: Heyting 'L a => a -> Bool
heytingL16 x = non (non (x /\ non x)) == bottom

heytingL17 :: Heyting 'L a => a -> Bool
heytingL17 x = x >= non (non x)

heytingL18 :: Heyting 'L c => c -> Bool
heytingL18 x = x == boundary x \/ (non . non) x

heytingL19 :: Heyting 'L a => a -> a -> Bool
heytingL19 x y = boundary (x /\ y) == (boundary x /\ y) \/ (x /\ boundary y)  -- (Leibniz rule)

heytingL20 :: Heyting 'L a => a -> a -> Bool
heytingL20 x y = boundary (x \/ y) \/ boundary (x /\ y) == boundary x \/ boundary y


heytingR0 :: Heyting 'R a => a -> a -> a -> Bool
heytingR0 x y z = x /\ y <= z <=> x <= y // z

heytingR1 :: Heyting 'R a => a -> a -> a -> Bool
heytingR1 x y z = x // y <= x // (y \/ z)

heytingR2 :: Heyting 'R a => a -> a -> a -> Bool
heytingR2 x y z = (x \/ z) // y <= x // y

heytingR3 :: Heyting 'R a => a -> a -> a -> Bool
heytingR3 x y z = x <= y ==> z // x <= z // y

heytingR4 :: Heyting 'R a => a -> a -> a -> Bool
heytingR4 x y z = (x /\ y) // z == x // y // z

heytingR5 :: Heyting 'R a => a -> a -> a -> Bool
heytingR5 x y z = x // (y /\ z) == x // y /\ x // z

heytingR6 :: Heyting 'R a => a -> a -> Bool
heytingR6 x y = y <= x // (x /\ y)

heytingR7 :: Heyting 'R a => a -> a -> Bool
heytingR7 x y = x /\ x // y == x /\ y

heytingR8 :: forall a. Heyting 'R a => a -> Bool
heytingR8 _ = neg bottom == top @a && neg top == bottom @a

-- Double negation is a monad.
heytingR9 :: Heyting 'R a => a -> a -> Bool
heytingR9 x y = neg x \/ y <= x // y

heytingR10 :: Heyting 'R a => a -> a -> Bool
heytingR10 x y = x <= y <=> x // y == top

heytingR11 :: Heyting 'R a => a -> a -> Bool
heytingR11 x y = neg (x \/ y) <= neg x

heytingR12 :: Heyting 'R a => a -> a -> Bool
heytingR12 x y = neg (x // y) == neg (neg x) /\ neg y

heytingR13 :: Heyting 'R a => a -> a -> Bool
heytingR13 x y = neg (x \/ y) == neg x /\ neg y

heytingR14 :: Heyting 'R a => a -> Bool
heytingR14 x = x /\ neg x == bottom

heytingR15 :: Heyting 'R a => a -> Bool
heytingR15 x = neg (neg (neg x)) == neg x

heytingR16 :: Heyting 'R a => a -> Bool
heytingR16 x = neg (neg (x \/ neg x)) == top

heytingR17 :: Heyting 'R a => a -> Bool
heytingR17 x = x <= neg (neg x)

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
