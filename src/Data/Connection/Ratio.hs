{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}
module Data.Connection.Ratio (
    Ratio(..) 
  , reduce
  , shiftd
  -- * Rational
  , Rational
  , ratf32
  , ratf64
  , rati08
  , rati16
  , rati32
  , rati64
  , ratixx
  , ratint
  -- * Positive
  , Positive
  , ratw08
  , ratw16
  , ratw32
  , ratw64
  , ratwxx
  , ratnat
) where

import safe Data.Connection.Type
import safe Data.Int
import safe Data.Lattice hiding (reduce)
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Ratio
import safe Data.Word
import safe GHC.Real (Ratio(..), Rational)
import safe Numeric.Natural
import safe Prelude hiding (Ord(..), until, Bounded)
import safe qualified Prelude as P
import safe qualified Data.Order.Float as F32
import safe qualified Data.Order.Double as F64

-- | A total version of 'GHC.Real.reduce'.
--
reduce :: Integral a => Ratio a -> Ratio a
reduce (x :% 0) = x :% 0
reduce (x :% y) = (x `quot` d) :% (y `quot` d) where d = gcd x y

-- | Shift by n 'units of least precision' where the ULP is determined by the denominator
-- 
-- This is an analog of 'Data.Connection.Float.shift' for rationals.
--
shiftd :: Num a => a -> Ratio a -> Ratio a
shiftd n (x :% y) = (n + x) :% y

---------------------------------------------------------------------
-- Rational
---------------------------------------------------------------------

rati08 :: Trip Rational (Extended Int8)
rati08 = signedTriple 127

rati16 :: Trip Rational (Extended Int16)
rati16 = signedTriple 32767

rati32 :: Trip Rational (Extended Int32)
rati32 = signedTriple 2147483647

rati64 :: Trip Rational (Extended Int64)
rati64 = signedTriple 9223372036854775807

ratixx :: Trip Rational (Extended Int)
ratixx = signedTriple 9223372036854775807

ratint :: Trip Rational (Extended Integer)
ratint = Trip f g h where
  
  f = liftExtended (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) P.ceiling

  g = extended bottom top P.fromIntegral

  h = liftExtended (\x -> x ~~ nan || x ~~ ninf) (~~ pinf) P.floor

ratf32 :: Trip Rational Float
ratf32 = Trip (toFloating f) (fromFloating g) (toFloating h) where
  f x = let est = P.fromRational x in --F.fromRat'
          if fromFloating g est >~ x
          then est
          else ascendf est (fromFloating g) x
    
  g = flip approxRational 0 

  h x = let est = P.fromRational x in
          if fromFloating g est <~ x
          then est
          else descendf est (fromFloating g) x

  ascendf z g1 y = until (\x -> g1 x >~ y) (<~) (F32.shift 1) z

  descendf z f1 x = until (\y -> f1 y <~ x) (>~) (F32.shift (-1)) z

ratf64 :: Trip Rational Double
ratf64 = Trip (toFloating f) (fromFloating g) (toFloating h) where
  f x = let est = P.fromRational x in
          if fromFloating g est >~ x
          then est
          else ascendf est (fromFloating g) x
    
  g = flip approxRational 0 

  h x = let est = P.fromRational x in
          if fromFloating g est <~ x
          then est
          else descendf est (fromFloating g) x

  ascendf z g1 y = until (\x -> g1 x >~ y) (<~) (F64.shift 1) z

  descendf z f1 x = until (\y -> f1 y <~ x) (>~) (F64.shift (-1)) z


---------------------------------------------------------------------
-- Ratio Natural
---------------------------------------------------------------------

ratw08 :: Trip Positive (Lowered Word8) 
ratw08 = unsignedTriple 255

ratw16 :: Trip Positive (Lowered Word16) 
ratw16 = unsignedTriple 65535

ratw32 :: Trip Positive (Lowered Word32) 
ratw32 = unsignedTriple 4294967295

ratw64 :: Trip Positive (Lowered Word64) 
ratw64 = unsignedTriple 18446744073709551615

ratwxx :: Trip Positive (Lowered Word) 
ratwxx = unsignedTriple 18446744073709551615

ratnat :: Trip Positive (Lowered Natural)
ratnat = Trip f g h where
  
  f = liftEitherR (\x -> x ~~ nan || x ~~ pinf) P.ceiling

  g = either P.fromIntegral (const top)

  h = liftEitherR (~~ pinf) $ \x -> if x ~~ nan then bottom else P.floor x

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

{-
pabs :: (Lattice a, Eq a, Num a) => a -> a
pabs x = if 0 <~ x then x else negate x

cancel :: (Lattice a, Eq a, Num a) => Ratio a -> Ratio a
cancel (x :% y) = if x < 0 && y < 0 then (pabs x) :% (pabs y) else x :% y

-- | An exception-safe version of 'nanf' for rationals.
--
nanr :: Integral b => (a -> Ratio b) -> Maybe a -> Ratio b
nanr f = maybe (0 :% 0) f
-}

pinf :: Num a => Ratio a
pinf = 1 :% 0

ninf :: Num a => Ratio a
ninf = (-1) :% 0

nan :: Num a => Ratio a
nan = 0 :% 0

unsignedTriple :: (Bounded a, Integral a) => Ratio Natural -> Trip Positive (Lowered a) 
unsignedTriple high = Trip f g h where
  f x | x ~~ nan = top
      | x > high = top
      | otherwise = Left $ P.ceiling x

  g = either P.fromIntegral (const pinf)

  h x | x ~~ nan = Left bottom
      | x ~~ pinf = top
      | x > high = Left top
      | otherwise = Left $ P.floor x

signedTriple :: (Bounded a, Integral a) => Rational -> Trip Rational (Extended a)
signedTriple high = Trip f g h where

  f = liftExtended (~~ ninf) (\x -> x ~~ nan || x > high) $ \x -> if x < low then bottom else P.ceiling x

  g = extended bottom top P.fromIntegral
 
  h = liftExtended (\x -> x ~~ nan || x < low) (~~ pinf) $ \x -> if x > high then top else P.floor x

  low = -1 - high


toFloating :: (Lattice (Ratio a), Eq a, Fractional b, Num a) => (Ratio a -> b) -> Ratio a -> b
toFloating f x | x ~~ nan = 0/0
         | x ~~ ninf = (-1)/0
         | x ~~ pinf = 1/0
         | otherwise = f x

fromFloating :: (Lattice a, Eq a, Fractional a, Num b) => (a -> Ratio b) -> a -> Ratio b
fromFloating f x | x ~~ 0/0 = nan
                 | x ~~ (-1)/0 = ninf
                 | x ~~ 1/0 = pinf
                 | otherwise = f x
