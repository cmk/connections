{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}
module Data.Connection.Ratio (
    Ratio(..) 
  , reduce
  , shiftd
  -- * Rational
  , ratf32
  , ratf64
  , rati08
  , rati16
  , rati32
  , rati64
  , ratixx
  , ratint
  -- * Positive
  , posw08
  , posw16
  , posw32
  , posw64
  , poswxx
  , posnat
) where

import safe Data.Connection.Conn
import safe Data.Int
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Order.Syntax
import safe Data.Ratio
import safe Data.Word
import safe GHC.Real (Ratio(..), Rational)
import safe Numeric.Natural
import safe Prelude hiding (Ord(..), until)
import safe qualified Prelude as P
import safe qualified Data.Connection.Float as Float

-- | A total version of 'GHC.Real.reduce'.
--
reduce :: Integral a => Ratio a -> Ratio a
reduce (x :% 0) = x :% 0
reduce (x :% y) = (x `quot` d) :% (y `quot` d) where d = gcd x y

-- | Shift by n 'units of least precision' where the ULP is determined by the denominator
-- 
-- This is an analog of 'Data.Connection.Float.shift32' for rationals.
--
shiftd :: Num a => a -> Ratio a -> Ratio a
shiftd n (x :% y) = (n + x) :% y

---------------------------------------------------------------------
-- Ratio Integer
---------------------------------------------------------------------

rati08 :: Conn k Rational (Extended Int8)
rati08 = signedTriple 127

rati16 :: Conn k Rational (Extended Int16)
rati16 = signedTriple 32767

rati32 :: Conn k Rational (Extended Int32)
rati32 = signedTriple 2147483647

rati64 :: Conn k Rational (Extended Int64)
rati64 = signedTriple 9223372036854775807

ratixx :: Conn k Rational (Extended Int)
ratixx = signedTriple 9223372036854775807

ratint :: Conn k Rational (Extended Integer)
ratint = Conn f g h where
  
  f = liftExtended (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) P.ceiling

  g = extended ninf pinf P.fromIntegral

  h = liftExtended (\x -> x ~~ nan || x ~~ ninf) (~~ pinf) P.floor

ratf32 :: Conn k Rational Float
ratf32 = Conn (toFloating f) (fromFloating g) (toFloating h) where
  f x = let est = P.fromRational x in
          if fromFloating g est >~ x
          then est
          else ascendf est (fromFloating g) x
    
  g = flip approxRational 0 

  h x = let est = P.fromRational x in
          if fromFloating g est <~ x
          then est
          else descendf est (fromFloating g) x

  ascendf z g1 y = Float.until (\x -> g1 x >~ y) (<~) (Float.shift32 1) z

  descendf z f1 x = Float.until (\y -> f1 y <~ x) (>~) (Float.shift32 (-1)) z

ratf64 :: Conn k Rational Double
ratf64 = Conn (toFloating f) (fromFloating g) (toFloating h) where
  f x = let est = P.fromRational x in
          if fromFloating g est >~ x
          then est
          else ascendf est (fromFloating g) x
    
  g = flip approxRational 0 

  h x = let est = P.fromRational x in
          if fromFloating g est <~ x
          then est
          else descendf est (fromFloating g) x

  ascendf z g1 y = Float.until (\x -> g1 x >~ y) (<~) (Float.shift64 1) z

  descendf z f1 x = Float.until (\y -> f1 y <~ x) (>~) (Float.shift64 (-1)) z

---------------------------------------------------------------------
-- Ratio Natural
---------------------------------------------------------------------

posw08 :: Conn k Positive (Lowered Word8) 
posw08 = unsignedTriple 255

posw16 :: Conn k Positive (Lowered Word16) 
posw16 = unsignedTriple 65535

posw32 :: Conn k Positive (Lowered Word32) 
posw32 = unsignedTriple 4294967295

posw64 :: Conn k Positive (Lowered Word64) 
posw64 = unsignedTriple 18446744073709551615

poswxx :: Conn k Positive (Lowered Word) 
poswxx = unsignedTriple 18446744073709551615

posnat :: Conn k Positive (Lowered Natural)
posnat = Conn f g h where
  
  f = liftEitherR (\x -> x ~~ nan || x ~~ pinf) P.ceiling

  g = either P.fromIntegral (const pinf)

  h = liftEitherR (~~ pinf) $ \x -> if x ~~ nan then 0 else P.floor x

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

pinf :: Num a => Ratio a
pinf = 1 :% 0

ninf :: Num a => Ratio a
ninf = (-1) :% 0

nan :: Num a => Ratio a
nan = 0 :% 0

unsignedTriple :: (Bounded a, Integral a) => Ratio Natural -> Conn k Positive (Lowered a) 
unsignedTriple high = Conn f g h where
  f x | x ~~ nan = Right maxBound
      | x > high = Right maxBound
      | otherwise = Left $ P.ceiling x

  g = either P.fromIntegral (const pinf)

  h x | x ~~ nan = Left minBound
      | x ~~ pinf = Right maxBound
      | x > high = Left maxBound
      | otherwise = Left $ P.floor x

signedTriple :: (Bounded a, Integral a) => Rational -> Conn k Rational (Extended a)
signedTriple high = Conn f g h where

  f = liftExtended (~~ ninf) (\x -> x ~~ nan || x > high) $ \x -> if x < low then minBound else P.ceiling x

  g = extended ninf pinf P.fromIntegral
 
  h = liftExtended (\x -> x ~~ nan || x < low) (~~ pinf) $ \x -> if x > high then maxBound else P.floor x

  low = -1 - high


toFloating :: (Order (Ratio a), Fractional b, Num a) => (Ratio a -> b) -> Ratio a -> b
toFloating f x | x ~~ nan = 0/0
         | x ~~ ninf = (-1)/0
         | x ~~ pinf = 1/0
         | otherwise = f x

fromFloating :: (Order a, Eq a, Fractional a, Num b) => (a -> Ratio b) -> a -> Ratio b
fromFloating f x | x ~~ 0/0 = nan
                 | x ~~ (-1)/0 = ninf
                 | x ~~ 1/0 = pinf
                 | otherwise = f x

{-
pabs :: (Lattice a, Eq a, Num a) => a -> a
pabs x = if 0 <~ x then x else negate x

cancel :: (Lattice a, Eq a, Num a) => Ratio a -> Ratio a
cancel (x :% y) = if x < 0 && y < 0 then (pabs x) :% (pabs y) else x :% y

-- | An exception-safe version of 'nanf' for rationals.
--
nanr :: Integral b => (a -> Ratio b) -> Maybe a -> Ratio b
nanr f = maybe (0 :% 0) f

ratpos :: Conn k Rational Positive
ratpos = Conn k f g h where
  
  f = liftExtended (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) P.ceiling

  g = extended minBound maxBound P.fromIntegral

  h = liftExtended (\x -> x ~~ nan || x ~~ ninf) (~~ pinf) P.floor
-}
