{-# Language AllowAmbiguousTypes #-}

module Data.Connection.Round (
  -- * Rounding Classes
    TripInt16(..) 
  , ceil16
  , floor16
  , trunc16
  , round16
  , TripInt32(..)
  , ceil32
  , floor32
  , trunc32
  , round32
  -- * Rounding Utils
  , Mode(..)
  , half
  , tied
  , above
  , below
  , addWith
  , negWith
  , subWith
  , mulWith
  , fmaWith
  , remWith
  , divWith
) where

import Data.Bool
import Data.Prd
import Data.Connection
import Data.Connection.Float
import Data.Connection.Ratio
import Data.Ratio


import Control.Category ((>>>))
import Data.Bits ((.&.))
import Data.Connection
import Data.Connection.Float
import Data.Connection.Int
import Data.Prd
import Data.Prd.Nan
import Data.Int
import Data.Word
import Data.Ratio
import Data.Float
import Data.Group
import qualified Control.Category as C
import qualified GHC.Float as F
import Data.Semilattice
import Data.Semilattice.Top
import Data.Semiring
import Data.Semifield hiding (fin)
import Prelude hiding (until, Ord(..), Num(..), Fractional(..), (^), Bounded)
import qualified Prelude as P
import GHC.Real hiding ((/), (^))
import Numeric.Natural
import Test.Logic (xor, (<==>),(==>))

class Prd a => TripInt16 a where
  xxxi16 :: Trip a (Extended Int16)

ceil16 :: TripInt16 a => a -> a
ceil16 = unitl xxxi16

floor16 :: TripInt16 a => a -> a
floor16 = counitr xxxi16

trunc16 :: (Additive-Monoid) a => TripInt16 a => a -> a
trunc16 x = bool (ceil16 x) (floor16 x) $ x >= zero

round16 :: (Additive-Group) a => TripInt16 a => a -> a
round16 x | above xxxi16 x = ceil16 x -- upper half interval
          | below xxxi16 x = floor16 x -- lower half interval
          | otherwise = trunc16 x

class Prd a => TripInt32 a where
  xxxi32 :: Trip a (Extended Int32)

ceil32 :: TripInt32 a => a -> a
ceil32 = unitl xxxi32

floor32 :: TripInt32 a => a -> a
floor32 = counitr xxxi32

trunc32 :: (Additive-Monoid) a => TripInt32 a => a -> a
trunc32 x = bool (ceil32 x) (floor32 x) $ x >= zero 

round32 :: (Additive-Group) a => TripInt32 a => a -> a
round32 x | above xxxi32 x = ceil32 x -- upper half interval
          | below xxxi32 x = floor32 x -- lower half interval
          | otherwise = trunc32 x

---------------------------------------------------------------------
-- Rounding
---------------------------------------------------------------------

-- | The four primary IEEE rounding modes.
--
-- See <https://en.wikipedia.org/wiki/Rounding>.
--
data Mode = 
    RNZ -- ^ round to nearest with ties towards zero
  | RTP -- ^ round towards pos infinity
  | RTN -- ^ round towards neg infinity
  | RTZ -- ^ round towards zero
  deriving (Eq, Show)

-- | Determine which half of the interval between two representations of /a/ a particular value lies.
-- 
half :: Prd a => Prd b => (Additive-Group) a => Trip a b -> a -> Maybe Ordering
half t x = pcompare (x - unitl t x) (counitr t x - x) 

-- | Determine whether /x/ lies above the halfway point between two representations.
-- 
-- @ 'above' t x '==' (x '-' 'unitl' t x) '`gt`' ('counitr' t x '-' x) @
--
above :: Prd a => Prd b => (Additive-Group) a => Trip a b -> a -> Bool
above t = maybe False (== GT) . half t

-- | Determine whether /x/ lies below the halfway point between two representations.
-- 
-- @ 'below' t x '==' (x '-' 'unitl' t x) '`lt`' ('counitr' t x '-' x) @
--
below :: Prd a => Prd b => (Additive-Group) a => Trip a b -> a -> Bool
below t = maybe False (== LT) . half t

-- | Determine whether /x/ lies exactly halfway between two representations.
-- 
-- @ 'tied' t x '==' (x '-' 'unitl' t x) '=~' ('counitr' t x '-' x) @
--
tied :: Prd a => Prd b => (Additive-Group) a => Trip a b -> a -> Bool
tied t = maybe False (== EQ) . half t

-- >>> addWith ratf32 RTN 1 2
-- 3.0
-- minSubf
addWith :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b -> b 
addWith t@(Trip _ f _) rm x y = rnd t rm (addSgn t rm x y) (f x + f y)

negWith :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b 
negWith t@(Trip _ f _) rm x = rnd t rm (neg' t rm x) (zero - f x)

subWith :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b -> b 
subWith t@(Trip _ f _) rm x y = rnd t rm (subSgn t rm x y) (f x - f y)

mulWith :: (Prd a, Prd b, Ring a) => Trip a b -> Mode -> b -> b -> b 
mulWith t@(Trip _ f _) rm x y = rnd t rm (xorSgn t rm x y) (f x * f y)

{-
big = shiftf (-1) maximal
λ> fmaWith ratf32 RTN big 2 (-big)
3.4028235e38
λ> big * 2 - big
Infinity
-}
fmaWith :: (Prd a, Prd b, Ring a) => Trip a b -> Mode -> b -> b -> b -> b
fmaWith t@(Trip _ f _) rm x y z = rnd t rm (fmaSgn t rm x y z) $ f x * f y + f z

{-
λ> remWith @Int RTP 17 5
-3
λ> remWith @Int RNZ 17 5
2
-}
remWith :: (Prd a, Prd b, Field a) => Trip a b -> Mode -> b -> b -> b
remWith t rm x y = fmaWith t rm (negWith t rm $ divWith t rm x y) y x

{-
λ> divWith @Int RNZ 17 5
3
λ> divWith @Int RTP 17 5
4
-}
-- when pos numbers are divided by −0 we return minus infinity rather than pos:
-- >>> divWith C.id RNZ 1 (shiftf (-1) 0)
-- -Infinity
divWith :: (Prd a, Prd b, Field a) => Trip a b -> Mode -> b -> b -> b 
divWith t@(Trip _ f _) rm x y = rnd t rm (xorSgn t rm x y) (f x / f y)


-- requires that sign be flipped back in /a/.
divWith' :: (Prd a, Prd b, Field a) => Trip a b -> Mode -> b -> b -> b 
divWith' t@(Trip _ f _) rm x y | xorSgn t rm x y = rnd t rm True (negate $ f x / f y)
                               | otherwise  = rnd t rm False (f x / f y)


---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

-- @ truncateWith C.id == id @
truncateWith :: (Prd a, Prd b, (Additive-Monoid) a) => Trip a b -> a -> b
truncateWith t x = bool (ceilingWith t x) (floorWith t x) $ x >= zero

-- @ ceilingWith C.id == id @
ceilingWith :: Prd a => Prd b => Trip a b -> a -> b
ceilingWith = connl . tripl

-- @ floorWith C.id == id @
floorWith :: Prd a => Prd b => Trip a b -> a -> b
floorWith = connr . tripr

-- @ roundWith C.id == id @
roundWith :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> a -> b
roundWith t x | above t x = ceilingWith t x -- upper half interval
              | below t x = floorWith t x -- lower half interval
              | otherwise = truncateWith t x

{-

rndWith :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b 
rndWith t@(Trip f g h) rm x = rnd t rm (neg' t rm x) (g x)

-}

-- Determine the sign of 0 when /a/ contains signed 0s
rsz :: (Prd a, Prd b) => Trip a b -> Bool -> a -> b
rsz t = bool (floorWith t) (ceilingWith t)

rnd :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> Bool -> a -> b
rnd t RNZ s x = bool (roundWith t x) (rsz t s x) $ x =~ zero
rnd t RTP s x = bool (ceilingWith t x) (rsz t s x) $ x =~ zero
rnd t RTN s x = bool (floorWith t x) (rsz t s x) $ x =~ zero
rnd t RTZ s x = bool (truncateWith t x) (rsz t s x) $ x =~ zero

neg' :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> Bool
neg' t rm x = x < rnd t rm False zero

pos'  :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> Bool 
pos' t rm x = x > rnd t rm False zero

-- | Determine signed-0 behavior under addition.
addSgn :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b -> Bool
addSgn t rm x y | rm == RTN = neg' t rm x || neg' t rm y
                | otherwise = neg' t rm x && neg' t rm y

subSgn :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b -> Bool
subSgn t rm x y = not (addSgn t rm x y)

-- | Determine signed-0 behavior under multiplication and division.
xorSgn :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b -> Bool
xorSgn t rm x y = neg' t rm x `xor` neg' t rm y

fmaSgn :: (Prd a, Prd b, Ring a) => Trip a b -> Mode -> b -> b -> b -> Bool
fmaSgn t rm x y z = addSgn t rm (mulWith t rm x y) z

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance TripInt16 Float where
  xxxi16 = f32i16

instance TripInt16 Double where
  xxxi16 = f64i16

instance TripInt16 (Ratio Integer) where
  xxxi16 = rati16 

instance TripInt32 Double where
  xxxi32 = f64i32

instance TripInt32 (Ratio Integer) where
  xxxi32 = rati32
