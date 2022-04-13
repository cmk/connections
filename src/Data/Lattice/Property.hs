{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Lattice.Property where

import Data.Lattice
import Data.Order.Property
import Data.Order.Syntax
import Prelude hiding (Bounded, Eq (..), Ord (..), not)


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

-- Double negation is a monad.
heyting17 :: Heyting a => a -> Bool
heyting17 x = x <= neg (neg x)

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

-- Double co-negation is a co-monad.
coheyting17 :: Coheyting a => a -> Bool
coheyting17 x = x >= non (non x)

coheyting18 :: Coheyting c => c -> Bool
coheyting18 x = x == boundary x \/ (non . non) x

-- Leibniz rule
coheyting19 :: Coheyting a => a -> a -> Bool
coheyting19 x y = boundary (x /\ y) == (boundary x /\ y) \/ (x /\ boundary y)

coheyting20 :: Coheyting a => a -> a -> Bool
coheyting20 x y = boundary (x \/ y) \/ boundary (x /\ y) == boundary x \/ boundary y

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

-- adjointL $ CastL (\x -> y \\ not x) (\z -> not z // not y)
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
