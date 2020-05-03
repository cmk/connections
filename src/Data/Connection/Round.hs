{-# Language AllowAmbiguousTypes #-}

module Data.Connection.Round (
    Mode(..)
  , half
  , tied
  , above
  , below
  , ceilingOn
  , floorOn
  , roundOn
  , truncOn
  , addOn
  , negOn
  , subOn
  , mulOn
  , fmaOn
  , remOn
  , divOn
  , divOn'
) where

import Data.Bool
import Data.Connection
import Data.Connection.Ratio
import Data.Float
import Data.Int
import Data.Prd
import Data.Prd.Property (xor)
import Data.Prd.Top
import Data.Ratio
import Prelude hiding (until, Ord(..), Bounded)

{-
  -- * Rounding Classes
    TripInt64(..) 
  , ceil64
  , floor64
  , trunc64
  , round64
  , TripInt32(..)
  , ceil32
  , floor32
  , trunc32
  , round32

class Prd a => TripInt64 a where
  typi64 :: Trip a (Extended Int64)

ceil64 :: TripInt64 a => a -> a
ceil64 = ceilingOn typi64

floor64 :: TripInt64 a => a -> a
floor64 = counitr typi64

trunc64 :: Num a => TripInt64 a => a -> a
trunc64 x = bool (ceil64 x) (floor64 x) $ x >= 0

round64 :: Num a => TripInt64 a => a -> a
round64 x | above typi64 x = ceil64 x -- upper half interval
          | below typi64 x = floor64 x -- lower half interval
          | otherwise = trunc64 x

class Prd a => TripInt32 a where
  typi32 :: Trip a (Extended Int32)

ceil32 :: TripInt32 a => a -> a
ceil32 = unitl typi32

floor32 :: TripInt32 a => a -> a
floor32 = counitr typi32

trunc32 :: Num a => TripInt32 a => a -> a
trunc32 x = bool (ceil32 x) (floor32 x) $ x >= 0 

round32 :: Num a => TripInt32 a => a -> a
round32 x | above typi32 x = ceil32 x -- upper half interval
          | below typi32 x = floor32 x -- lower half interval
          | otherwise = trunc32 x


---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance TripInt16 Float where
  typi16 = f32i16

instance TripInt16 Double where
  typi16 = f64i16

instance TripInt16 (Ratio Integer) where
  typi16 = rati16 

instance TripInt32 Double where
  typi32 = f64i32

instance TripInt32 (Ratio Integer) where
  typi32 = rati32
-}

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
half :: Prd a => Prd b => Num a => Trip a b -> a -> Maybe Ordering
half t x = pcompare (x - unitl t x) (counitr t x - x) 

-- | Determine whether /x/ lies above the halfway point between two representations.
-- 
-- @ 'above' t x '==' (x '-' 'unitl' t x) '`gt`' ('counitr' t x '-' x) @
--
above :: Prd a => Prd b => Num a => Trip a b -> a -> Bool
above t = maybe False (== GT) . half t

-- | Determine whether /x/ lies below the halfway point between two representations.
-- 
-- @ 'below' t x '==' (x '-' 'unitl' t x) '`lt`' ('counitr' t x '-' x) @
--
below :: Prd a => Prd b => Num a => Trip a b -> a -> Bool
below t = maybe False (== LT) . half t

-- | Determine whether /x/ lies exactly halfway between two representations.
-- 
-- @ 'tied' t x '==' (x '-' 'unitl' t x) '=~' ('counitr' t x '-' x) @
--
tied :: Prd a => Prd b => Num a => Trip a b -> a -> Bool
tied t = maybe False (== EQ) . half t

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

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

-- @ truncOn C.id == id @
truncOn :: (Prd a, Prd b, Num a) => Trip a b -> a -> b
truncOn t x = bool (ceilingOn t x) (floorOn t x) $ x >= 0

-- @ ceilingOn C.id == id @
ceilingOn :: Prd a => Prd b => Trip a b -> a -> b
ceilingOn = connl . tripl

-- @ floorOn C.id == id @
floorOn :: Prd a => Prd b => Trip a b -> a -> b
floorOn = connr . tripr

-- @ roundOn C.id == id @
roundOn :: (Prd a, Prd b, Num a) => Trip a b -> a -> b
roundOn t x | above t x = ceilingOn t x -- upper half interval
              | below t x = floorOn t x -- lower half interval
              | otherwise = truncOn t x

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
rnd t RTZ s x = bool (truncOn t x) (rsz t s x) $ x =~ 0

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
