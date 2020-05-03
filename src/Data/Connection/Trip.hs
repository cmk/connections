{-# Language AllowAmbiguousTypes #-}

module Data.Connection.Trip (
  -- * Triple
    Trip(..)
  , tripl
  , tripr
  , unitl
  , unitr
  , counitl
  , counitr
  , strong'
  , choice'
  -- * Rounding
  , Mode(..)
  , half
  , tied
  , above
  , below
  , roundOn
  , floorOn
  , ceilingOn
  , truncateOn
) where

import Control.Category (Category)
import Data.Bifunctor (bimap)
import Data.Bool
import Data.Connection.Conn
import Data.Prd
import Prelude hiding (until, Ord(..), Bounded)
import qualified Control.Category as C

---------------------------------------------------------------------
-- Adjoint triples
---------------------------------------------------------------------

-- | An adjoint triple.
--
-- @'Trip' f g h@ satisfies:
--
-- @
-- f ⊣ g
-- ⊥   ⊥
-- g ⊣ h
-- @
--
-- See <https://ncatlab.org/nlab/show/adjoint+triple>
--
data Trip a b = Trip (a -> b) (b -> a) (a -> b)

instance Category Trip where
  id = Trip id id id
  Trip f' g' h' . Trip f g h = Trip (f' . f) (g . g') (h' . h)

tripl :: Trip a b -> Conn a b
tripl (Trip f g _) = Conn f g

tripr :: Trip a b -> Conn b a
tripr (Trip _ g h) = Conn g h

unitl :: Trip a b -> a -> a
unitl = unit . tripl

unitr :: Trip a b -> b -> b
unitr = unit . tripr

counitl :: Trip a b -> b -> b
counitl = counit . tripl

counitr :: Trip a b -> a -> a
counitr = counit . tripr

strong' :: Trip a b -> Trip c d -> Trip (a, c) (b, d)
strong' (Trip ab ba ab') (Trip cd dc cd') = Trip f g h where
  f = bimap ab cd 
  g = bimap ba dc
  h = bimap ab' cd'

choice' :: Trip a b -> Trip c d -> Trip (Either a c) (Either b d)
choice' (Trip ab ba ab') (Trip cd dc cd') = Trip f g h where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)
  h = either (Left . ab') (Right . cd')

---------------------------------------------------------------------
-- Rounding
---------------------------------------------------------------------

-- | The four primary IEEE rounding modes.
--
-- See <https://en.wikipedia.org/wiki/Rounding>.
--
data Mode = 
    RNZ -- ^ round to nearest with ties towards 0
  | RTP -- ^ round towards pos infinity
  | RTN -- ^ round towards neg infinity
  | RTZ -- ^ round towards 0
  deriving (Eq, Show)

-- | Determine which half of the interval between two representations of /a/ a particular value lies.
-- 
half :: (Num a, Prd a) => Trip a b -> a -> Maybe Ordering
half t x = pcompare (x - unitl t x) (counitr t x - x) 

-- | Determine whether /x/ lies above the halfway point between two representations.
-- 
-- @ 'above' t x '==' (x '-' 'unitl' t x) '`gt`' ('counitr' t x '-' x) @
--
above :: (Num a, Prd a) => Trip a b -> a -> Bool
above t = maybe False (== GT) . half t

-- | Determine whether /x/ lies below the halfway point between two representations.
-- 
-- @ 'below' t x '==' (x '-' 'unitl' t x) '`lt`' ('counitr' t x '-' x) @
--
below :: (Num a, Prd a) => Trip a b -> a -> Bool
below t = maybe False (== LT) . half t

-- | Determine whether /x/ lies exactly halfway between two representations.
-- 
-- @ 'tied' t x '==' (x '-' 'unitl' t x) '=~' ('counitr' t x '-' x) @
--
tied :: (Num a, Prd a) => Trip a b -> a -> Bool
tied t = maybe False (== EQ) . half t

-- @ roundOn C.id == id @
roundOn :: (Prd a, Num a) => Trip a b -> a -> b
roundOn t x | above t x = ceilingOn t x -- upper half interval
            | below t x = floorOn t x -- lower half interval
            | otherwise = truncateOn t x

-- @ floorOn C.id == id @
floorOn :: Trip a b -> a -> b
floorOn = connr . tripr

-- @ ceilingOn C.id == id @
ceilingOn :: Trip a b -> a -> b
ceilingOn = connl . tripl

-- @ truncateOn C.id == id @
truncateOn :: (Num a, Prd a) => Trip a b -> a -> b
truncateOn t x = bool (ceilingOn t x) (floorOn t x) $ x >= 0

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

{-
-- >>> addOn ratf32 RTN 1 2
-- 3.0
-- minSubf
addOn :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> b -> b 
addOn t@(Trip _ f _) rm x y = rnd t rm (addSgn t rm x y) (f x + f y)

negOn :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> b 
negOn t@(Trip _ f _) rm x = rnd t rm (neg' t rm x) (0 - f x)

subOn :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> b -> b 
subOn t@(Trip _ f _) rm x y = rnd t rm (subSgn t rm x y) (f x - f y)

mulOn :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> b -> b 
mulOn t@(Trip _ f _) rm x y = rnd t rm (xorSgn t rm x y) (f x * f y)

{-
big = shiftf (-1) maximal
λ> fmaOn ratf32 RTN big 2 (-big)
3.4028235e38
λ> big * 2 - big
Infinity
-}
fmaOn :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> b -> b -> b
fmaOn t@(Trip _ f _) rm x y z = rnd t rm (fmaSgn t rm x y z) $ f x * f y + f z

{-
λ> remOn @Int RTP 17 5
-3
λ> remOn @Int RNZ 17 5
2
-}
remOn :: (Prd a, Prd b, Fractional a) => Trip a b -> Mode -> b -> b -> b
remOn t rm x y = fmaOn t rm (negOn t rm $ divOn t rm x y) y x

{-
λ> divOn @Int RNZ 17 5
3
λ> divOn @Int RTP 17 5
4
-}
-- when pos numbers are divided by −0 we return minus infinity rather than pos:
-- >>> divOn C.id RNZ 1 (shiftf (-1) 0)
-- -Infinity
divOn :: (Prd a, Prd b, Fractional a) => Trip a b -> Mode -> b -> b -> b 
divOn t@(Trip _ f _) rm x y = rnd t rm (xorSgn t rm x y) (f x / f y)

-- requires that sign be flipped back in /a/.
divOn' :: (Prd a, Prd b, Fractional a) => Trip a b -> Mode -> b -> b -> b 
divOn' t@(Trip _ f _) rm x y | xorSgn t rm x y = rnd t rm True (negate $ f x / f y)
                             | otherwise  = rnd t rm False (f x / f y)



{-

rndOn :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> b 
rndOn t@(Trip f g h) rm x = rnd t rm (neg' t rm x) (g x)

-}

-- Determine the sign of 0 when /a/ contains signed 0s
rsz :: (Prd a, Prd b) => Trip a b -> Bool -> a -> b
rsz t = bool (floorOn t) (ceilingOn t)

rnd :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> Bool -> a -> b
rnd t RNZ s x = bool (roundOn t x) (rsz t s x) $ x =~ 0
rnd t RTP s x = bool (ceilingOn t x) (rsz t s x) $ x =~ 0
rnd t RTN s x = bool (floorOn t x) (rsz t s x) $ x =~ 0
rnd t RTZ s x = bool (truncateOn t x) (rsz t s x) $ x =~ 0

neg' :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> Bool
neg' t rm x = x < rnd t rm False 0

--pos'  :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> Bool 
--pos' t rm x = x > rnd t rm False 0

-- | Determine signed-0 behavior under addition.
addSgn :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> b -> Bool
addSgn t rm x y | rm == RTN = neg' t rm x || neg' t rm y
                | otherwise = neg' t rm x && neg' t rm y

subSgn :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> b -> Bool
subSgn t rm x y = not (addSgn t rm x y)

-- | Determine signed-0 behavior under multiplication and division.
xorSgn :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> b -> Bool
xorSgn t rm x y = neg' t rm x `xor` neg' t rm y

fmaSgn :: (Prd a, Prd b, Num a) => Trip a b -> Mode -> b -> b -> b -> Bool
fmaSgn t rm x y z = addSgn t rm (mulOn t rm x y) z

-}
