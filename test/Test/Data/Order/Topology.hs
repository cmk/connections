{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module Test.Data.Order.Topology where

import Control.Applicative hiding (empty)
import Data.Connection.Type
import Data.Connection.Double
import Data.Lattice
import Data.Lattice.Heyting
import Test.Data.Connection
import Data.Word
import Data.Order
import Data.Order.Topology
import Prelude hiding (Bounded, Eq(..), Ord(..))
import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

ordbin :: Conn Ordering Bool
ordbin = Conn f g where
  f GT = True
  f _  = False

  g True = GT
  g _    = EQ

binord :: Conn Bool Ordering
binord = Conn f g where
  f False = LT
  f _     = EQ

  g LT = False
  g _  = True

type Rel r b = r -> r -> b


-- | \( \forall a \in R: a \/ a = a \)
--
-- @ 'idempotent_join' = 'absorbative' 'top' @
-- 
-- See < https://en.wikipedia.org/wiki/Band_(mathematics) >.
--
-- This is a required property.
--
idempotent_join :: Lattice r => r -> Bool
idempotent_join = idempotent_join_on (~~)

idempotent_join_on :: (Join-Semigroup) r => Rel r b -> r -> b
idempotent_join_on (~~) r = (\/) r r ~~ r

-- | \( \forall a, b, c \in R: (a \/ b) \/ c = a \/ (b \/ c) \)
--
-- This is a required property.
--
associative_join :: Lattice r => r -> r -> r -> Bool
associative_join = associative_on (~~) (\/) 

associative_join_on :: (Join-Semigroup) r => Rel r b -> r -> r -> r -> b
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

commutative_join_on :: (Join-Semigroup) r => Rel r b -> r -> r -> b
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
-- See < https://en.wikipedia.org/wiki/Median_algebra >.
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
-- See < https://en.wikipedia.org/wiki/Distributivity_(order_theory)#Distributivity_for_semilattices >
--
modular :: Lattice r => r -> r -> r -> Bool
modular a b c = a \/ (c /\ b) ~~ (a \/ c) /\ b 

eq :: Eq a => [a] -> Open t a -> Open t a -> Bool
eq as p q = base p == base q && and (fmap chk as)
  where chk x = member x p <=> member x q


prop_alexandrov_bool :: Property
prop_alexandrov_bool = withTests 1000 . property $ do
  x1 <- forAll $ gen_inf G.bool
  y1 <- forAll $ gen_sup ord

  x2 <- forAll $ fmap (upper' binord) $ gen_ivl G.bool G.bool
  y2 <- forAll $ fmap (lower' binord) $ gen_ivl ord ord
  
  x3 <- forAll $ fmap (upper' ordbin) $ gen_ivl ord ord
  y3 <- forAll $ fmap (lower' ordbin) $ gen_ivl G.bool G.bool
  
  assert $ valid x1 && base x1 <~ bound x1
  assert $ valid x2 && base x2 <~ bound x2
  assert $ valid x3 && base x3 <~ bound x3
  
  assert $ valid y1 && base y1 >~ bound y1
  assert $ valid y2 && base y2 >~ bound y2
  assert $ valid y3 && base y3 >~ bound y3


prop_alexandrov_float :: Property
prop_alexandrov_float = withTests 1000 . property $ do
  x0 <- forAll $ fmap inf f32
  y0 <- forAll $ fmap sup f32

  x1 <- forAll $ gen_inf f32
  y1 <- forAll $ gen_sup f32

  x2 <- forAll $ fmap (upper' $ tripl f64f32) $ gen_ivl f64 f64
  y2 <- forAll $ fmap (lower' $ tripr f64f32) $ gen_ivl f64 f64
  
  as <- forAll $ G.list (R.constant 0 20) f32

  assert $ valid x0 && base x0 <~ bound x0
  assert $ valid x1 && base x1 <~ bound x1
  assert $ valid x2 && base x2 <~ bound x2
  
  assert $ valid y0 && base y0 >~ bound y0
  assert $ valid y1 && base y1 >~ bound y1
  assert $ valid y2 && base y2 >~ bound y2

  assert $ absorbative_on (eq as) x1 x2
  assert $ absorbative_on (eq as) y1 y2
  assert $ absorbative_on' (eq as) x1 x2
  assert $ absorbative_on' (eq as) y1 y2
  assert $ commutative_join_on (eq as) x1 x2
  assert $ commutative_join_on (eq as) y1 y2
  assert $ associative_join_on (eq as) x0 x1 x2
  assert $ associative_join_on (eq as) y0 y1 y2


prop_alexandrov_word8 :: Property
prop_alexandrov_word8 = withTests 100 . property $ do
  --let g = gen_inf $ G.set (R.constant 0 20) $ G.integral (ri @Word8)
  let l = gen_inf $ G.integral (ri @Word8)
      u = gen_sup $ G.integral (ri @Word8)
      
  (a,b,c,d) <- forAll $ (,,,) <$> l <*> l <*> l <*> l
  (x,y,z,w) <- forAll $ (,,,) <$> u <*> u <*> u <*> u
  
  assert $ valid a && base a <~ bound a
  assert $ valid x && base x >~ bound x
  
  --assert $ distributive_on (eq as) (/\) (\/) x0 x1 x2
  --assert $ distributive_on (eq as) (/\) (\/) y0 y1 y2
  assert $ majority_glb a b
  assert $ commutative_glb a b c
  assert $ commutative_glb' a b c
  assert $ associative_glb a b c d
  --assert $ validl x1 s1
  --assert $ modular x y z -- 0 ... 1 , 0 ... 0 , 0 ... 0 
  assert $ majority_glb a b
  assert $ commutative_glb x y z
  assert $ commutative_glb' x y z
  assert $ associative_glb x y z w

  assert $ absorbative_on (~~) a b
  assert $ absorbative_on (~~) x y
  assert $ absorbative_on' (~~) a b
  assert $ absorbative_on' (~~) x y
  assert $ commutative_join_on (~~) a b
  assert $ commutative_join_on (~~) x y
  assert $ associative_join_on (~~) a b c
  assert $ associative_join_on (~~) x y z
{-
-- (-Infinity) ... 0.0 , 0.0
validl :: Lattice a => Inf a -> a -> Bool
validl o x = member x o || x ~~ bound o <=> glb (base o) x (bound o) ~~ x

{-
λ> x = lfilter (0/0) $ inf (-1/0) :: Inf Float
λ> x
-Infinity ... NaN
λ> validl' x 0
False
λ> x ? 0
True
-}
validl' :: Lattice a => Inf a -> a -> Bool
validl' o x = member x o || x ~~ bound o <=> base o <~ x && x <~ bound o

validr :: Lattice a => Sup a -> a -> Bool
validr o x = member x o <=> lub (bound o) x (base o) ~~ x
-}

prop_lattice :: Property
prop_lattice = withTests 10 . property $ do
  --let g = G.bool
  --let g = gen_inf ord
  --let g = G.integral (ri @Word8)
  --let g = f32
  let g = gen_inf $ G.integral (ri @Word8)
  --let g = gen_inf $ G.set (R.constant 0 20) $ G.integral (ri @Word8)
  (a,b,c,d) <- forAll $ (,,,) <$> g <*> g <*> g <*> g

  assert $ distributive_glb a b c
  assert $ majority_glb a b
  assert $ commutative_glb a b c
  assert $ commutative_glb' a b c
  assert $ associative_glb a b c d

-- false for floats
--interval_glb 0 0 (0/0 :: Float)
--modular 0 (-1) (0 :: Float)
--distributive 0 (0/0) (-1)
--codistributive (-1) (0/0) 0
prop_distributive :: Property
prop_distributive = withTests 100 . property $ do

  let g = G.bool
  --let g = gen_inf $ G.integral (ri @Word8)
  --let g = gen_inf $ G.set (R.constant 0 20) $ G.integral (ri @Word8)
  (a,b,c) <- forAll $ (,,) <$> g <*> g <*> g

  assert $ distributive_glb a b c
  assert $ interval_glb a b c
  assert $ modular a b c
  assert $ distributive a b c
  assert $ codistributive a b c
  --assert . valid $ pull (tripr f64f32) x2
