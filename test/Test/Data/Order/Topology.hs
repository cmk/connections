{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Test.Data.Order.Topology where

import Control.Applicative hiding (empty)
import Data.Connection
import Data.Connection.Conn
import Data.Connection.Double
import Data.Lattice
import Data.Lattice.Heyting
import Test.Data.Connection
import Data.Int
import Data.Word
import Data.Order
import Data.Order.Syntax
import Data.Order.Interval
import Data.Order.Extended
import Data.Order.Topology

import Prelude hiding (Bounded, round, floor, ceiling, Eq(..), Ord(..))
import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

import Hedgehog.Range hiding (exponential)
import Hedgehog.Internal.Range hiding (exponential)
import Hedgehog.Internal.Shrink
import qualified Prelude as P
import qualified Data.Order.Float as F32


{-
r = exponential 0 (-10) (0/0) :: Range Float
>>> bounds 5 r
(-0.12874436,-10.0)

take 5 $ towardsFloat 0 F32.maximal
λ> take 5 $ towardsFloat 0 F32.maximal
[0.0,1.7014117e38,2.5521175e38,2.9774705e38,3.190147e38]

λ> take 5 $ towards32 0 F32.maximal

λ> take 5 $ descend32 1 $ 0 ... F32.maximal
[0.0,2.028241e31,4.056482e31,6.084723e31,8.112964e31]
λ> take 5 $ descend32 100 $ 0 ... F32.maximal
[0.0,2.028241e33,4.056482e33,6.084723e33,8.112964e33]
λ> take 5 $ descend32 1000 $ 0 ... F32.maximal
[0.0,2.028241e34,4.056482e34,6.084723e34,8.112964e34]
λ> take 5 $ descend32 10000 $ 0 ... F32.maximal
[0.0,2.028241e35,4.056482e35,6.084723e35,8.112964e35]

descend32 :: Int32 -> Interval Float -> [Float]
descend32 i0 = maybe [] (f i) . endpts where

  i = - min 1 (abs i0)

  f step (dest, orig) =
    if dest == orig then
      []
    else
      let
	diff =
	  orig - dest

	ok y =
	  y /= orig && not (isNaN y) -- && not (isInfinite y)
      in
	takeWhile ok .
	fmap (orig -) $
	iterate (F32.shift step) diff

-}


-- TODO vary 'step' param intelligently
towards32 :: Float -> Float -> [Float]
towards32 x y = case F32.ulp x y of
  Just (LT, width) -> f (width `quot` 25) x y
  Just (GT, width) -> f (width `quot` 25) y x
  _ -> []
  where
    ok y = not (isNaN y) && not (isInfinite y)
    f step dest orig = 
	takeWhile (>~ dest) .
	fmap (orig -) $
	iterate (F32.shift . negate $ fromIntegral step) (orig - dest)


--take 25 . takeWhile (<~ orig) . iterate (F32.shift . fromIntegral $ step) $ dest

{-
scaleDisc :: (Num a, ConnInteger a) => Integer -> a -> a -> a
scaleDisc sz0 z0 n0 =
    let
      sz =
        max 0 (min 99 sz0)
      diff z n = (n - z) * (sz `quot` 99)
    in
      z0 + floor2 (liftA2 diff) z0 n0
-}

range :: Preorder a => Size -> Range a -> Interval a
range sz (Range _ f) = uncurry (...) $ f sz

--rescale :: Trip a b -> Range a -> Range b
-- f bottom = fst
-- f top = snd
type Interpolation a b = a -> (b, b) -> b

diffRing sz z n = (n - z) * (fromIntegral sz `quot` 99)

--integral :: (Lattice a, Num a, Triple Rational a) => a -> a -> a -> Range a
--integral = rangeWith diffRing

diffField sz z n = (n - z) * (toRational sz / 99.0)

linear :: (Lattice a, Fractional a, Triple Rational a) => a -> a -> a -> Range a
linear = rangeWith diffField

exponential :: (Lattice a, Num a, Triple Double a) => a -> a -> a -> Range a
exponential = rangeWith diffFloat

rangeWith :: (Lattice a, Num a, Triple r a) => (Size -> r -> r -> r) -> a -> a -> a -> Range a
rangeWith diff z x y =
  Range z $ \sz0 ->
    let
      sz = clamp 0 99 sz0
     
      clampedX =
        glb x (z + ceiling2 (diff sz) z x) y

      clampedY =
        lub x (z + floor2 (diff sz) z y) y
    in
      (clampedX, clampedY)


diffFloat sz0 z n =
  let
    sz = clamp 0 99 sz0

    m = (((abs (n - z) + 1) ** (realToFrac sz / 99)) - 1) * signum (n - z)

   in m -- glb z m n

{-
scaleWith :: (Connection 'R a b, Num b) => (Size -> a -> a -> a) -> Size -> b -> b -> b
scaleWith diff sz0 z0 n0 =
    let
      sz = clamp 0 99 sz0
      
    in
      z0 + floor2 (diff sz) z0 n0
-}

ordbin :: ConnL Ordering Bool
ordbin = ConnL f g where
  f GT = True
  f _  = False

  g True = GT
  g _    = EQ

binord :: ConnR Bool Ordering
binord = ConnR g f where
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


eql :: PartialOrder a => [a] -> Inf a -> Inf a -> Bool
eql as p q = lower p == lower q && and (fmap chk as)
  where chk x = p .? x <=> q .? x

eqr :: PartialOrder a => [a] -> Sup a -> Sup a -> Bool
eqr as p q = upper p == upper q && and (fmap chk as)
  where chk x = x ?. p <=> x ?. q

validL :: Preorder a => Inf a -> Bool
validL i = i .? lower i && lower i <~ upper i

validR :: Preorder a => Sup a -> Bool
validR s = upper s ?. s && lower s <~ upper s

prop_alexandrov_float :: Property
prop_alexandrov_float = withTests 20000 . property $ do
  x0 <- forAll $ gen_inf f64
  y0 <- forAll $ gen_sup f64
  
  xs <- forAll $ G.list (R.constant 0 20) f32
  as <- forAll $ G.list (R.constant 0 20) f32

  let x1 = omap f64f32 x0
      y1 = omap f64f32 y0

      x2 = foldr filterL x1 xs
      y2 = foldr filterR y1 xs

  assert $ validL x0
  assert $ validR y0
  assert $ validL x1
  assert $ validR y1
  assert $ validL x2
  assert $ validR y2

  assert $ absorbative_on (eql as) x1 x2
  assert $ absorbative_on (eqr as) y1 y2
  assert $ absorbative_on' (eql as) x1 x2
  assert $ absorbative_on' (eqr as) y1 y2
  assert $ commutative_join_on (eql as) x1 x2
  assert $ commutative_join_on (eqr as) y1 y2
  assert $ associative_join_on (eql as) x2 x1 x2
  assert $ associative_join_on (eqr as) y2 y1 y2


{-
  z0 <- forAll $ fmap inf f64
  z1 <- forAll $ gen_inf f64
  let 
      lfilt = (foldl $ flip filterL)

      baz0 = upper3 f64f32 z0
      baz1 = upper3 f64f32 z1
      baz2 = lfilt baz1 as

      bar0 = upper2 f64f32 z0
      bar1 = upper2 f64f32 z1
      bar2 = lfilt bar1 as
-}


{-
  assert $ absorbative_on (eql as) baz0 baz2
  assert $ absorbative_on' (eql as) baz0 baz2
  assert $ commutative_join_on (eql as) baz1 baz2
  assert $ associative_join_on (eql as) baz0 baz1 baz2
-}

{-
  assert $ valid z0 && base z0 <~ bound z0
  assert $ valid z1 && base z1 <~ bound z1
  --assert $ valid baz0 && base baz0 <~ bound baz0
  --assert $ valid baz1 && base baz1 <~ bound baz1
  --assert $ valid baz2 && base baz2 <~ bound baz2

  -- recheck (Size 13) (Seed 10897869244381744101 12878561573241830103) prop_alexandrov_float 
  assert $ valid bar0 && base bar0 <~ bound bar0
  annotateShow $ bar1
  annotateShow $ baz1
  assert $ valid bar1 -- && base bar1 <~ bound bar1
  assert $ valid bar2 && base bar2 <~ bound bar2

  assert $ valid x0 && base x0 <~ bound x0
  assert $ valid x1 && base x1 <~ bound x1
  assert $ valid x2 && base x2 <~ bound x2
  
  assert $ valid y0 && base y0 >~ bound y0
  assert $ valid y1 && base y1 >~ bound y1
  --assert $ valid y2 && base y2 >~ bound y2

-}

{-
upper2 :: ConnL a b -> Inf a -> Inf b
upper2 (ConnL f g) (Open p x y) = Open (p . g) (f x) (f y)

upper3 :: Trip a b -> Inf a -> Inf b
upper3 (Conn f g h) (Open p x y) = Open (p . g) (h x) (f y)
-}

prop_alexandrov_word8 :: Property
prop_alexandrov_word8 = withTests 100 . property $ do
  --let g = gen_inf $ G.set (R.constant 0 20) $ G.integral (ri @Word8)
  let l = gen_inf $ G.integral (ri @Word8)
      u = gen_sup $ G.integral (ri @Word8)
      
  (a,b,c,d) <- forAll $ (,,,) <$> l <*> l <*> l <*> l
  (x,y,z,w) <- forAll $ (,,,) <$> u <*> u <*> u <*> u
  
  assert $ validL a
  assert $ validR x
  
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
λ> x = filterL (0/0) $ inf (-1/0) :: Inf Float
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
