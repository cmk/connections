{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Connection.Float (
    -- * Float
    min32,
    max32,
    eps32,
    ulp32,
    near32,
    shift32,
    f32i08,
    f32i16,
    f32i32,
    f32i64,
    f32ixx,
    f32int,

    -- * Double
    min64,
    max64,
    eps64,
    ulp64,
    near64,
    shift64,
    f64i08,
    f64i16,
    f64i32,
    f64i64,
    f64ixx,
    f64int,
    f64f32,
    until,
) where

import safe Data.Bool
import safe Data.Connection.Conn hiding (ceiling, floor)
import safe Data.Int
import safe Data.Order
import safe Data.Order.Syntax hiding (max, min)
import safe Data.Word
import safe GHC.Float as F
import safe Prelude hiding (Eq (..), Ord (..), until)
import safe qualified Prelude as P

---------------------------------------------------------------------
-- Float
---------------------------------------------------------------------

-- | A /NaN/-handling min32 function.
--
-- > min32 x NaN = x
-- > min32 NaN y = y
min32 :: Float -> Float -> Float
min32 x y = case (isNaN x, isNaN y) of
    (False, False) -> if x <= y then x else y
    (False, True) -> x
    (True, False) -> y
    (True, True) -> x

-- | A /NaN/-handling max32 function.
--
-- > max32 x NaN = x
-- > max32 NaN y = y
max32 :: Float -> Float -> Float
max32 x y = case (isNaN x, isNaN y) of
    (False, False) -> if x >= y then x else y
    (False, True) -> x
    (True, False) -> y
    (True, True) -> x

-- | Compute the difference between a float and its next largest neighbor.
--
-- See < https://en.wikipedia.org/wiki/Machine_epsilon >.
eps32 :: Float -> Float
eps32 x = shift32 1 x - x

-- | Compute the signed distance between two floats in units of least precision.
--
-- >>> ulp32 1.0 (shift32 1 1.0)
-- Just (LT,1)
-- >>> ulp32 (0.0/0.0) 1.0
-- Nothing
ulp32 :: Float -> Float -> Maybe (Ordering, Word32)
ulp32 x y = fmap f $ pcompare x y
  where
    x' = floatInt32 x
    y' = floatInt32 y
    f LT = (LT, fromIntegral . abs $ y' - x')
    f EQ = (EQ, 0)
    f GT = (GT, fromIntegral . abs $ x' - y')

-- | Compare two floats for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
near32 :: Word32 -> Float -> Float -> Bool
near32 tol x y = maybe False ((<= tol) . snd) $ ulp32 x y

-- | Shift a float by /n/ units of least precision.
--
-- >>> shift32 1 0
-- 1.0e-45
-- >>> shift32 1 1 - 1
-- 1.1920929e-7
-- >>> shift32 1 $ 0/0
-- Infinity
-- >>> shift32 (-1) $ 0/0
-- -Infinity
-- >>> shift32 1 $ 1/0
-- Infinity
shift32 :: Int32 -> Float -> Float
shift32 n x =
    if isNaN x == True
        then case signum n of
            -1 -> -1 / 0
            1 -> 1 / 0
            _ -> 0 / 0
        else int32Float . clamp32 . (+ n) . floatInt32 $ x

-- | All 'Data.Int.Int08' values are exactly representable in a 'Float'.
f32i08 :: Conn k Float (Extended Int8)
f32i08 = fxxext

-- | All 'Data.Int.Int16' values are exactly representable in a 'Float'.
--
-- >>> Data.Connection.Conn.ceiling f32i16 32767.0
-- Finite 32767
-- >>> Data.Connection.Conn.ceiling f32i16 32767.1
-- PosInf
f32i16 :: Conn k Float (Extended Int16)
f32i16 = fxxext

f32i32 :: Conn 'L Float (Extended Int32)
f32i32 = f32ext

f32i64 :: Conn 'L Float (Extended Int64)
f32i64 = f32ext

f32ixx :: Conn 'L Float (Extended Int)
f32ixx = f32ext

f32int :: Conn 'L Float (Extended Integer)
f32int = f32ext

---------------------------------------------------------------------
-- Double
---------------------------------------------------------------------

-- | A /NaN/-handling min function.
--
-- > min64 x NaN = x
-- > min64 NaN y = y
min64 :: Double -> Double -> Double
min64 x y = case (isNaN x, isNaN y) of
    (False, False) -> if x <= y then x else y
    (False, True) -> x
    (True, False) -> y
    (True, True) -> x

-- | A /NaN/-handling max function.
--
-- > max64 x NaN = x
-- > max64 NaN y = y
max64 :: Double -> Double -> Double
max64 x y = case (isNaN x, isNaN y) of
    (False, False) -> if x >= y then x else y
    (False, True) -> x
    (True, False) -> y
    (True, True) -> x

-- | Compute the difference between a double and its next largest neighbor.
--
-- See < https://en.wikipedia.org/wiki/Machine_epsilon >.
eps64 :: Double -> Double
eps64 x = shift64 1 x - x

-- | Compute the signed distance between two doubles in units of least precision.
--
-- >>> ulp64 1.0 (shift64 1 1.0)
-- Just (LT,1)
-- >>> ulp64 (0.0/0.0) 1.0
-- Nothing
ulp64 :: Double -> Double -> Maybe (Ordering, Word64)
ulp64 x y = fmap f $ pcompare x y
  where
    x' = doubleInt64 x
    y' = doubleInt64 y
    f LT = (LT, fromIntegral . abs $ y' - x')
    f EQ = (EQ, 0)
    f GT = (GT, fromIntegral . abs $ x' - y')

-- | Compare two double-precision floats for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
near64 :: Word64 -> Double -> Double -> Bool
near64 tol x y = maybe False ((<= tol) . snd) $ ulp64 x y

-- | Shift by /n/ units of least precision.
--
-- >>> shift64 1 0
-- 5.0e-324
-- >>> shift64 1 1 - 1
-- 2.220446049250313e-16
-- >>> shift64 1 $ 0/0
-- Infinity
-- >>> shift64 (-1) $ 0/0
-- -Infinity
-- >>> shift64 1 $ 1/0
-- Infinity
shift64 :: Int64 -> Double -> Double
shift64 n x =
    if isNaN x == True
        then case signum n of
            -1 -> -1 / 0
            1 -> 1 / 0
            _ -> 0 / 0
        else int64Double . clamp64 . (+ n) . doubleInt64 $ x

-- | All 'Data.Int.Int08' values are exactly representable in a 'Double'.
f64i08 :: Conn k Double (Extended Int8)
f64i08 = fxxext

-- | All 'Data.Int.Int16' values are exactly representable in a 'Double'.
f64i16 :: Conn k Double (Extended Int16)
f64i16 = fxxext

-- | All 'Data.Int.Int32' values are exactly representable in a 'Double'.
f64i32 :: Conn k Double (Extended Int32)
f64i32 = fxxext

f64i64 :: Conn 'L Double (Extended Int64)
f64i64 = f64ext

f64ixx :: Conn 'L Double (Extended Int)
f64ixx = f64ext

f64int :: Conn 'L Double (Extended Integer)
f64int = f64ext

f64f32 :: Conn k Double Float
f64f32 = Conn f g h
  where
    f x =
        let est = double2Float x
         in if g est >~ x
                then est
                else ascend32 est g x

    g = float2Double

    h x =
        let est = double2Float x
         in if g est <~ x
                then est
                else descend32 est g x

    ascend32 z g1 y = until (\x -> g1 x >~ y) (<~) (shift32 1) z

    descend32 z h1 x = until (\y -> h1 y <~ x) (>~) (shift32 (-1)) z
{-# INLINE f64f32 #-}

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

{-# INLINE until #-}
until :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
until pre rel f seed = go seed
  where
    go x
        | x' `rel` x = x
        | pre x = x
        | otherwise = go x'
      where
        x' = f x

-- Non-monotonic function
signed32 :: Word32 -> Int32
signed32 x
    | x < 0x80000000 = fromIntegral x
    | otherwise = fromIntegral (maxBound - (x - 0x80000000))

-- Non-monotonic function
signed64 :: Word64 -> Int64
signed64 x
    | x < 0x8000000000000000 = fromIntegral x
    | otherwise = fromIntegral (maxBound - (x - 0x8000000000000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned32 :: Int32 -> Word32
unsigned32 x
    | x >= 0 = fromIntegral x
    | otherwise = 0x80000000 + (maxBound - (fromIntegral x))

-- Non-monotonic function converting from 2s-complement format.
unsigned64 :: Int64 -> Word64
unsigned64 x
    | x >= 0 = fromIntegral x
    | otherwise = 0x8000000000000000 + (maxBound - (fromIntegral x))

int32Float :: Int32 -> Float
int32Float = castWord32ToFloat . unsigned32

-- NB: I needed these zeros to avoid some error
floatInt32 :: Float -> Int32
floatInt32 = signed32 . (+ 0) . castFloatToWord32

int64Double :: Int64 -> Double
int64Double = castWord64ToDouble . unsigned64

doubleInt64 :: Double -> Int64
doubleInt64 = signed64 . (+ 0) . castDoubleToWord64

-- Clamp between the int representations of -1/0 and 1/0
clamp32 :: Int32 -> Int32
clamp32 = P.max (-2139095041) . P.min 2139095040

-- Clamp between the int representations of -1/0 and 1/0
clamp64 :: Int64 -> Int64
clamp64 = P.max (-9218868437227405313) . P.min 9218868437227405312

f32ext :: Integral a => Conn 'L Float (Extended a)
f32ext = ConnL f g
  where
    prec = 24 :: Int -- Float loses integer precision beyond 2^prec
    f x
        | abs x <= 2 ** 24 -1 = Finite (ceiling x)
        | otherwise = case pcompare x 0 of
            Just LT -> NegInf
            _ -> Finite (2 ^ prec)

    g NegInf = -2 ** 24
    g PosInf = 1 / 0
    g (Finite i)
        | abs i P.<= 2 ^ prec -1 = fromIntegral i
        | otherwise = if i P.>= 0 then 1 / 0 else -2 ** 24
{-# INLINE f32ext #-}

f64ext :: Integral a => Conn 'L Double (Extended a)
f64ext = ConnL f g
  where
    prec = 53 :: Int -- Double loses integer precision beyond 2^prec
    f x
        | abs x <= 2 ** 53 -1 = Finite (ceiling x)
        | otherwise = case pcompare x 0 of
            Just LT -> NegInf
            _ -> Finite (2 ^ prec)

    g NegInf = -2 ** 53
    g PosInf = 1 / 0
    g (Finite i)
        | abs i P.<= 2 ^ prec -1 = fromIntegral i
        | otherwise = if i P.>= 0 then 1 / 0 else -2 ** 53
{-# INLINE f64ext #-}

fxxext :: forall a b k. (RealFrac a, Preorder a, Bounded b, Integral b) => Conn k a (Extended b)
fxxext = Conn f g h
  where
    f = liftExtended (~~ -1 / 0) (\x -> x ~~ 0 / 0 || x > high) $ \x -> if x < low then minBound else ceiling x

    g = extended (-1 / 0) (1 / 0) fromIntegral

    h = liftExtended (\x -> x ~~ 0 / 0 || x < low) (~~ 1 / 0) $ \x -> if x > high then maxBound else floor x

    low = fromIntegral $ minBound @b

    high = fromIntegral $ maxBound @b
{-# INLINE fxxext #-}

{-

frac2fixed :: (RealFrac a, HasResolution b) => a -> Fixed b
frac2fixed (flip approxRational 0 -> (n :% d)) = fromInteger n / fromInteger d

--fixed2Float :: forall a . HasResolution a => Fixed a -> Float
--fixed2Float (MkFixed i) = rationalToFloat i $ resolution (Proxy :: Proxy a)
-}
