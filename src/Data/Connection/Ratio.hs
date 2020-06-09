{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds #-}
{-# Language FunctionalDependencies #-}
{-# Language Safe                #-}
module Data.Connection.Ratio (
    Ratio(..) 
  , reduce
  , shiftd
  -- * Ratio Integer
  , ordrat
  , ratord
  , ratf32
  , ratf64
{-
  , rati08
  , rati16
  , rati32
  , rati64
  , ratixx
  , ratint
-}
  -- * Ratio Natural
{-
  , ordpos
  , posord
  , ratw08
  , ratw16
  , ratw32
  , ratw64
  , ratwxx
  , ratnat
-}
) where

import safe Data.Connection.Type
import safe Data.Connection.Float
import safe Data.Int
import safe Data.Lattice hiding (reduce)
import safe Data.Order
import safe Data.Ratio
import safe Data.Word
import safe GHC.Real (Ratio(..), Rational)
import safe Numeric.Natural
import safe Prelude hiding (Ord(..), until, Bounded)
import safe qualified Prelude as P

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

{-
ratord :: (BoundedEq a, Fractional a) => Trip a (Extended Ordering)
ratord = Trip (liftExtended (~~ 0/0) (const False) f)
              (extends g)
              (liftExtended (const False) (~~ 0/0) h)
  where
    g GT = 1/0
    g LT = -1/0 
    g EQ = 0

    f x | x ~~ (-1/0) = LT
        | x <~ 0  = EQ
  | otherwise = GT

    h x | x ~~ (1/0) = GT
        | x >~ 0  = EQ
  | otherwise = LT
-}


---------------------------------------------------------------------
-- Ratio Integer
---------------------------------------------------------------------

ratord :: Conn (Ratio Integer) (Lowered Ordering)
ratord = Conn (Left . f) (lowered g) where
  g GT = top
  g EQ = zero
  g LT = bottom
  
  f x | x ~~ bottom = LT
      | x <~ zero   = EQ
      | otherwise   = GT

ordrat :: Conn (Lifted Ordering) (Ratio Integer)
ordrat = Conn (lifted g) (Right . h) where
  g GT = top
  g EQ = zero
  g LT = bottom

  h x | x ~~ top  = GT
      | x >~ zero = EQ
      | otherwise = LT

rati08 :: Trip (Ratio Integer) (Extended Int8)
rati08 = ratixx 127

rati16 :: Trip (Ratio Integer) (Extended Int16)
rati16 = ratixx 32767

rati32 :: Trip (Ratio Integer) (Extended Int32)
rati32 = ratixx 2147483647

rati64 :: Trip (Ratio Integer) (Extended Int64)
rati64 = ratixx 9223372036854775807

ratint :: Trip (Ratio Integer) (Extended Integer)
ratint = Trip f g h where
  f x | x ~~ pinf = Top
      | x ~~ ninf = Bottom
      | otherwise = Extended $ P.ceiling $ cancel x

  g = extends P.fromIntegral

  h x | x ~~ pinf = Top
      | x ~~ ninf = Bottom
      | otherwise = Extended $ P.floor $ cancel x

ratixx :: (Bounded i, Integral i) => Ratio Integer -> Trip (Ratio Integer) (Extended i) 
ratixx i = Trip f g h where
  f x | x > imax = Top
      | x ~~ ninf = Bottom
      | x < imin = Extended bottom
      | otherwise = Extended $ P.ceiling $ cancel x

  g = extends P.fromIntegral

  h x | x ~~ pinf = Top
      | x > imax = Extended top
      | x < imin = Bottom
      | otherwise = Extended $ P.floor $ cancel x

  imax = i 

  imin = -1 - i

ratf32 :: Trip (Ratio Integer) Float
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

  ascendf z g1 y = until (\x -> g1 x >~ y) (<~) (shift32 1) z

  descendf z f1 x = until (\y -> f1 y <~ x) (>~) (shift32 (-1)) z

ratf64 :: Trip (Ratio Integer) Double
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

  ascendf z g1 y = until (\x -> g1 x >~ y) (<~) (shift64 1) z

  descendf z f1 x = until (\y -> f1 y <~ x) (>~) (shift64 (-1)) z


---------------------------------------------------------------------
-- Ratio Natural
---------------------------------------------------------------------

ratw08 :: Trip (Ratio Natural) (Lowered Word8) 
ratw08 = ratwxx 255

ratw16 :: Trip (Ratio Natural) (Lowered Word16) 
ratw16 = ratwxx 65535

ratw32 :: Trip (Ratio Natural) (Lowered Word32) 
ratw32 = ratwxx 4294967295

ratw64 :: Trip (Ratio Natural) (Lowered Word64) 
ratw64 = ratwxx 18446744073709551615

ratwxx :: (Bounded i, Integral i) => Ratio Natural -> Trip (Ratio Natural) (Lowered i) 
ratwxx i = Trip f g h where
  f x | x ~~ anan = top
      | x > i = top
      | otherwise = Left $ P.ceiling x

  g = either P.fromIntegral (const pinf)

  h x | x ~~ anan = Left bottom
      | x ~~ pinf = top
      | x > i = Left top
      | otherwise = Left $ P.floor x

ratnat :: Trip (Ratio Natural) (Lowered Natural)
ratnat = Trip f g h where
  f x | x ~~ pinf = top
      | otherwise = Left $ P.ceiling x

  g = either P.fromIntegral (const pinf) 

  h x | x ~~ pinf = top
      | otherwise = Left $ P.floor x

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

pabs :: (Lattice a, Eq a, Num a) => a -> a
pabs x = if 0 <~ x then x else negate x

cancel :: (Lattice a, Eq a, Num a) => Ratio a -> Ratio a
cancel (x :% y) = if x < 0 && y < 0 then (pabs x) :% (pabs y) else x :% y

-- | An exception-safe version of 'nanf' for rationals.
--
nanr :: Integral b => (a -> Ratio b) -> Maybe a -> Ratio b
nanr f = maybe (0 :% 0) f

toFloating :: (Lattice (Ratio a), Eq a, Fractional b, Num a) => (Ratio a -> b) -> Ratio a -> b
toFloating f x | x ~~ anan = 0/0
         | x ~~ ninf = (-1)/0
         | x ~~ pinf = 1/0
         | otherwise = f x

fromFloating :: (Lattice a, Eq a, Fractional a, Num b) => (a -> Ratio b) -> a -> Ratio b
fromFloating f x | x ~~ 0/0 = anan
                 | x ~~ (-1)/0 = ninf
                 | x ~~ 1/0 = pinf
                 | otherwise = f x

zero :: Num a => Ratio a
zero = 0 :% 1

pinf :: Num a => Ratio a
pinf = 1 :% 0

ninf :: Num a => Ratio a
ninf = (-1) :% 0

anan :: Num a => Ratio a
anan = 0 :% 0




{-
ratord :: (Eq a, Lattice a, Fractional a) => Trip a (Maybe Ordering)
ratord = Trip f g h where
  g (Just GT) = (1/0) 
  g (Just LT) = (-1/0) 
  g (Just EQ) = 0
  g Nothing = 0/0 
  
  f x | x ~~ 0/0  = Nothing
      | x ~~ (-1/0)  = Just LT
      | x <~ 0  = Just EQ
      | otherwise  = Just GT

  h x | x ~~ 0/0  = Nothing
      | x ~~ (1/0)  = Just GT
      | x >~ 0  = Just EQ
      | otherwise  = Just LT
-}


