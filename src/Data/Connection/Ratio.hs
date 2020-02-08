{-# Language AllowAmbiguousTypes #-}
{-# Language FunctionalDependencies #-}

module Data.Connection.Ratio where

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
import Data.Semilattice.Bounded
import Data.Semiring
import Data.Semifield hiding (fin)
import Prelude hiding (until, Ord(..), Num(..), Fractional(..), (^), Bounded)
import qualified Prelude as P
import GHC.Real hiding ((/), (^))
import Numeric.Natural

reduce :: Integral a => a -> a -> Ratio a
reduce x 0 = x :% 0
reduce x y = (x `quot` d) :% (y `quot` d) where d = gcd x y

-- x % y = reduce (x * signum y) (abs y)
cancel :: Prd a => (Additive-Group) a => Ratio a -> Ratio a
cancel (x :% y) = if x < zero && y < zero then (pabs x) :% (pabs y) else x :% y

-- | Lawful replacement for the version in base.
--
-- >>> fromRational @Float 1.3
-- 1.3000001
-- >>> fromRational @Float (1/0)
-- Infinity
-- >>> fromRational @Float (0/0)
-- NaN
--
-- >>> fromRational @(Extended Int8) 4.9
-- Def (fin 5)
-- >>> fromRational @(Extended Int8) (-1.2)
-- Def (fin (-1))
-- >>> fromRational @(Extended Int8) (1/0)
-- Def Just Top
-- >>> fromRational @(Extended Int8) (0/0)
-- Nan
-- >>> fromRational @(Extended Int8) (-1/0)
-- Def Nothing
--
fromRational :: TripRatio a b => Ratio a -> b
fromRational = connl . tripl $ tripRatio

class (Prd (Ratio a), Prd b) => TripRatio a b | b -> a where
  tripRatio :: Trip (Ratio a) b

-- TODO replace w/ Yoneda / Index / Graded
-- shift by n 'units of least precision' where the ULP is
-- determined by the denominator
shiftd :: (Additive-Semigroup) a => a -> Ratio a -> Ratio a
shiftd n (x :% y) = (n + x) :% y

ratf32 :: Trip (Ratio Integer) Float
ratf32 = Trip (extend' f) (extend' g) (extend' h) where
  f x = let est = P.fromRational x in --F.fromRat'
          if extend' g est >= x
          then est
          else ascendf est (extend' g) x
    
  g = flip approxRational 0 

  h x = let est = P.fromRational x in
          if extend' g est <= x
          then est
          else descendf est (extend' g) x

  ascendf z g y = until (\x -> g x >= y) (<=) (shiftf 1) z

  descendf z f x = until (\y -> f y <= x) (>=) (shiftf (-1)) z

ratf64 :: Trip (Ratio Integer) Double
ratf64 = Trip (extend' f) (extend' g) (extend' h) where
  f x = let est = P.fromRational x in
          if extend' g est >= x
          then est
          else ascendf est (extend' g) x
    
  g = flip approxRational 0 

  h x = let est = P.fromRational x in
          if extend' g est <= x
          then est
          else descendf est (extend' g) x

  ascendf z g y = until (\x -> g x >= y) (<=) (shift 1) z

  descendf z f x = until (\y -> f y <= x) (>=) (shift (-1)) z

rati08 :: Trip (Ratio Integer) (Extended Int8) 
rati08 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin bottom
      | otherwise = fin $ P.ceiling $ cancel x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Just Top
      | x > imax = fin top
      | x < imin = Nothing
      | otherwise = fin $ P.floor $ cancel x

  imax = 127

  imin = -128

rati16 :: Trip (Ratio Integer) (Extended Int16) 
rati16 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin bottom
      | otherwise = fin $ P.ceiling $ cancel x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Just Top
      | x > imax = fin top
      | x < imin = Nothing
      | otherwise = fin $ P.floor $ cancel x

  imax = 32767

  imin = -32768

rati32 :: Trip (Ratio Integer) (Extended Int32) 
rati32 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin bottom
      | otherwise = fin $ P.ceiling $ cancel x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Just Top
      | x > imax = fin top
      | x < imin = Nothing
      | otherwise = fin $ P.floor $ cancel x

  imax = 2147483647 

  imin = -2147483648

rati64 :: Trip (Ratio Integer) (Extended Int64) 
rati64 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin bottom
      | otherwise = fin $ P.ceiling $ cancel x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Just Top
      | x > imax = fin top
      | x < imin = Nothing
      | otherwise = fin $ P.floor $ cancel x
 
  imax = 9223372036854775807

  imin = -9223372036854775808

ratint :: Trip (Ratio Integer) (Extended Integer)
ratint = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x =~ pinf = Just Top
      | x =~ ninf = Nothing
      | otherwise = fin $ P.ceiling $ cancel x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Just Top
      | x =~ ninf = Nothing
      | otherwise = fin $ P.floor $ cancel x

ratw08 :: Trip (Ratio Natural) (Lifted Word8) 
ratw08 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Top
      | otherwise = Fin $ P.ceiling x

  g = topped P.fromIntegral pinf

  h x | x =~ pinf = Top
      | x > imax = Fin top
      | otherwise = Fin $ P.floor x

  imax = 255

ratw16 :: Trip (Ratio Natural) (Lifted Word16) 
ratw16 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Top
      | otherwise = Fin $ P.ceiling x

  g = topped P.fromIntegral pinf

  h x | x =~ pinf = Top
      | x > imax = Fin top
      | otherwise = Fin $ P.floor x

  imax = 65535

ratw32 :: Trip (Ratio Natural) (Lifted Word32) 
ratw32 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Top
      | otherwise = Fin $ P.ceiling x

  g = topped P.fromIntegral pinf

  h x | x =~ pinf = Top
      | x > imax = Fin top
      | otherwise = Fin $ P.floor x

  imax = 4294967295

ratw64 :: Trip (Ratio Natural) (Lifted Word64) 
ratw64 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Top
      | otherwise = Fin $ P.ceiling x

  g = topped P.fromIntegral pinf

  h x | x =~ pinf = Top
      | x > imax = Fin top
      | otherwise = Fin $ P.floor x

  imax = 18446744073709551615

ratnat :: Trip (Ratio Natural) (Lifted Natural)
ratnat = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x =~ pinf = Top
      | otherwise = Fin $ P.ceiling x

  g = topped P.fromIntegral pinf

  h x | x =~ pinf = Top
      | otherwise = Fin $ P.floor x

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance TripRatio Integer Float where
  tripRatio = ratf32

instance TripRatio Integer Double where
  tripRatio = ratf64

instance TripRatio Integer (Ratio Integer) where
  tripRatio = C.id

instance TripRatio Integer (Nan Ordering) where
  tripRatio = fldord

instance TripRatio Integer (Extended Int8) where
  tripRatio = rati08

instance TripRatio Integer (Extended Int16) where
  tripRatio = rati16

instance TripRatio Integer (Extended Int32) where
  tripRatio = rati32

instance TripRatio Integer (Extended Int64) where
  tripRatio = rati64

instance TripRatio Integer (Extended Integer) where
  tripRatio = ratint

instance TripRatio Natural (Ratio Natural) where
  tripRatio = C.id

instance TripRatio Natural (Lifted Word8) where
  tripRatio = ratw08

instance TripRatio Natural (Lifted Word16) where
  tripRatio = ratw16

instance TripRatio Natural (Lifted Word32) where
  tripRatio = ratw32

instance TripRatio Natural (Lifted Word64) where
  tripRatio = ratw64

instance TripRatio Natural (Lifted Natural) where
  tripRatio = ratnat
