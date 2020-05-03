{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds #-}
{-# Language FunctionalDependencies #-}
{-# Language Safe                #-}
module Data.Connection.Ratio (
    Ratio(..) 
  , reduce
  , shiftd
  -- * Ratio Integer
  , ratord
  , ratf32
  , ratf64
  , rati08
  , rati16
  , rati32
  , rati64
  , ratint
  -- * Ratio Natural
  , ratw08
  , ratw16
  , ratw32
  , ratw64
  , ratnat
) where

import safe Data.Connection.Trip
import safe Data.Connection.Float
import safe Data.Int
import safe Data.Prd
import safe Data.Prd.Nan hiding (liftNan)
import safe Data.Ratio
import safe Data.Prd.Top
import safe Data.Word
import safe GHC.Real (Ratio(..), Rational)
import safe Numeric.Natural
import safe Prelude hiding (until, Ord(..), Bounded)
import safe qualified Prelude as P
import safe qualified Data.Prd as Prd

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
-- Ratio Integer
---------------------------------------------------------------------

ratord :: Trip (Ratio Integer) (Nan Ordering)
ratord = Trip f g h where
    g (Def GT) = pinf 
    g (Def LT) = ninf 
    g (Def EQ) = 0
    g Nan = anan 
    
    f x | x =~ anan  = Nan
        | x =~ ninf  = Def LT
        | x <= 0  = Def EQ
        | otherwise  = Def GT

    h x | x =~ anan  = Nan
        | x =~ pinf  = Def GT
        | x >= 0  = Def EQ
        | otherwise  = Def LT

ratf32 :: Trip (Ratio Integer) Float
ratf32 = Trip (extend' f) (extend g) (extend' h) where
  f x = let est = P.fromRational x in --F.fromRat'
          if extend g est >= x
          then est
          else ascendf est (extend g) x
    
  g = flip approxRational 0 

  h x = let est = P.fromRational x in
          if extend g est <= x
          then est
          else descendf est (extend g) x

  ascendf z g1 y = until (\x -> g1 x >= y) (<=) (shiftf 1) z

  descendf z f1 x = until (\y -> f1 y <= x) (>=) (shiftf (-1)) z

ratf64 :: Trip (Ratio Integer) Double
ratf64 = Trip (extend' f) (extend g) (extend' h) where
  f x = let est = P.fromRational x in
          if extend g est >= x
          then est
          else ascendf est (extend g) x
    
  g = flip approxRational 0 

  h x = let est = P.fromRational x in
          if extend g est <= x
          then est
          else descendf est (extend g) x

  ascendf z g1 y = until (\x -> g1 x >= y) (<=) (shift 1) z

  descendf z f1 x = until (\y -> f1 y <= x) (>=) (shift (-1)) z

rati08 :: Trip (Ratio Integer) (Extended Int8) 
rati08 = Trip (liftNan f) (nanr g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling $ cancel x

  g = bound ninf pinf P.fromIntegral

  h x | x =~ pinf = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor $ cancel x

  imax = 127

  imin = -128

rati16 :: Trip (Ratio Integer) (Extended Int16) 
rati16 = Trip (liftNan f) (nanr g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling $ cancel x

  g = bound ninf pinf P.fromIntegral

  h x | x =~ pinf = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor $ cancel x

  imax = 32767

  imin = -32768

rati32 :: Trip (Ratio Integer) (Extended Int32) 
rati32 = Trip (liftNan f) (nanr g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling $ cancel x

  g = bound ninf pinf P.fromIntegral

  h x | x =~ pinf = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor $ cancel x

  imax = 2147483647 

  imin = -2147483648

rati64 :: Trip (Ratio Integer) (Extended Int64) 
rati64 = Trip (liftNan f) (nanr g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling $ cancel x

  g = bound ninf pinf P.fromIntegral

  h x | x =~ pinf = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor $ cancel x
 
  imax = 9223372036854775807

  imin = -9223372036854775808

ratint :: Trip (Ratio Integer) (Extended Integer)
ratint = Trip (liftNan f) (nanr g) (liftNan h) where
  f x | x =~ pinf = Just Top
      | x =~ ninf = Nothing
      | otherwise = fin $ P.ceiling $ cancel x

  g = bound ninf pinf P.fromIntegral

  h x | x =~ pinf = Just Top
      | x =~ ninf = Nothing
      | otherwise = fin $ P.floor $ cancel x

---------------------------------------------------------------------
-- Ratio Natural
---------------------------------------------------------------------

ratw08 :: Trip (Ratio Natural) (Lifted Word8) 
ratw08 = Trip (liftNan f) (nanr g) (liftNan h) where
  f x | x > imax = Top
      | otherwise = Fin $ P.ceiling x

  g = top pinf P.fromIntegral

  h x | x =~ pinf = Top
      | x > imax = Fin maximal
      | otherwise = Fin $ P.floor x

  imax = 255

ratw16 :: Trip (Ratio Natural) (Lifted Word16) 
ratw16 = Trip (liftNan f) (nanr g) (liftNan h) where
  f x | x > imax = Top
      | otherwise = Fin $ P.ceiling x

  g = top pinf P.fromIntegral

  h x | x =~ pinf = Top
      | x > imax = Fin maximal
      | otherwise = Fin $ P.floor x

  imax = 65535

ratw32 :: Trip (Ratio Natural) (Lifted Word32) 
ratw32 = Trip (liftNan f) (nanr g) (liftNan h) where
  f x | x > imax = Top
      | otherwise = Fin $ P.ceiling x

  g = top pinf P.fromIntegral

  h x | x =~ pinf = Top
      | x > imax = Fin maximal
      | otherwise = Fin $ P.floor x

  imax = 4294967295

ratw64 :: Trip (Ratio Natural) (Lifted Word64) 
ratw64 = Trip (liftNan f) (nanr g) (liftNan h) where
  f x | x > imax = Top
      | otherwise = Fin $ P.ceiling x

  g = top pinf P.fromIntegral

  h x | x =~ pinf = Top
      | x > imax = Fin maximal
      | otherwise = Fin $ P.floor x

  imax = 18446744073709551615

ratnat :: Trip (Ratio Natural) (Lifted Natural)
ratnat = Trip (liftNan f) (nanr g) (liftNan h) where
  f x | x =~ pinf = Top
      | otherwise = Fin $ P.ceiling x

  g = top pinf P.fromIntegral

  h x | x =~ pinf = Top
      | otherwise = Fin $ P.floor x

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

cancel :: Prd a => Num a => Ratio a -> Ratio a
cancel (x :% y) = if x < 0 && y < 0 then (pabs x) :% (pabs y) else x :% y

liftNan f x | x =~ anan = Nan
            | otherwise = Def (f x)

extend :: (Prd a, Fractional a, Num b) => (a -> Ratio b) -> a -> Ratio b
extend f x  | x =~ 0/0 = anan
            | x =~ (-1)/0 = ninf
            | x =~ 1/0 = pinf
            | otherwise = f x

extend' :: (Prd (Ratio a), Num a, Fractional b) => (Ratio a -> b) -> Ratio a -> b
extend' f x | x =~ anan = 0/0
            | x =~ ninf = (-1)/0
            | x =~ pinf = 1/0
            | otherwise = f x

pinf :: Num a => Ratio a
pinf = 1 :% 0

ninf :: Num a => Ratio a
ninf = (-1) :% 0

anan :: Num a => Ratio a
anan = 0 :% 0

--showr :: Integral a => Show a => Ratio a -> String
--showr r = show x ++ " % " ++ show y where (x :% y) = reduce r
