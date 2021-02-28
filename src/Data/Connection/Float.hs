{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Safe #-}

module Data.Connection.Float (
    -- * Connections
    f32i08,
    f32i16,
    f64i08,
    f64i16,
    f64i32,
    f64f32,

    -- * Float
    min32,
    max32,
    eps32,
    ulp32,
    near32,
    shift32,

    -- * Double
    min64,
    max64,
    eps64,
    ulp64,
    near64,
    shift64,
    until,
) where

import safe Data.Bool
import safe Data.Connection.Conn
import safe Data.Int
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Order.Syntax hiding (max, min)
import safe Data.Word
import safe GHC.Float as F
import safe Prelude hiding (Eq (..), Ord (..), until)
import safe qualified Prelude as P

---------------------------------------------------------------------
-- Connections
---------------------------------------------------------------------

-- | All 'Data.Int.Int08' values are exactly representable in a 'Float'.
f32i08 :: Conn k Float (Extended Int8)
f32i08 = triple

-- | All 'Data.Int.Int16' values are exactly representable in a 'Float'.
--
--  > ceilingWith f32i16 32767.0
--  Extended 32767
--  > ceilingWith f32i16 32767.1
--  Top
f32i16 :: Conn k Float (Extended Int16)
f32i16 = triple

-- | All 'Data.Int.Int08' values are exactly representable in a 'Double'.
f64i08 :: Conn k Double (Extended Int8)
f64i08 = triple

-- | All 'Data.Int.Int16' values are exactly representable in a 'Double'.
f64i16 :: Conn k Double (Extended Int16)
f64i16 = triple

-- | All 'Data.Int.Int32' values are exactly representable in a 'Double'.
f64i32 :: Conn k Double (Extended Int32)
f64i32 = triple

f64f32 :: Conn k Double Float
f64f32 = Conn f1 g f2
  where
    f1 x =
        let est = F.double2Float x
         in if g est >~ x
                then est
                else ascend32 est g x

    f2 x =
        let est = F.double2Float x
         in if g est <~ x
                then est
                else descend32 est g x

    g = F.float2Double

    ascend32 z g1 y = until (\x -> g1 x >~ y) (<~) (shift32 1) z

    descend32 z h1 x = until (\y -> h1 y <~ x) (>~) (shift32 (-1)) z

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
-- NaN
-- >>> shift32 (-1) $ 0/0
-- NaN
-- >>> shift32 1 $ 1/0
-- Infinity
shift32 :: Int32 -> Float -> Float
shift32 n x
    | x ~~ 0 / 0 = x
    | otherwise = int32Float . clamp32 . (+ n) . floatInt32 $ x

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
-- NaN
-- >>> shift64 (-1) $ 0/0
-- NaN
-- >>> shift64 1 $ 1/0
-- Infinity
shift64 :: Int64 -> Double -> Double
shift64 n x
    | x ~~ 0 / 0 = x
    | otherwise = int64Double . clamp64 . (+ n) . doubleInt64 $ x

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
    | otherwise = fromIntegral (maxBound P.- (x P.- 0x8000000000000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned32 :: Int32 -> Word32
unsigned32 x
    | x >= 0 = fromIntegral x
    | otherwise = 0x80000000 + (maxBound - (fromIntegral x))

-- Non-monotonic function converting from 2s-complement format.
unsigned64 :: Int64 -> Word64
unsigned64 x
    | x >~ 0 = fromIntegral x
    | otherwise = 0x8000000000000000 + (maxBound P.- (fromIntegral x))

int32Float :: Int32 -> Float
int32Float = F.castWord32ToFloat . unsigned32

floatInt32 :: Float -> Int32
floatInt32 = signed32 . (+ 0) . F.castFloatToWord32

int64Double :: Int64 -> Double
int64Double = F.castWord64ToDouble . unsigned64

doubleInt64 :: Double -> Int64
doubleInt64 = signed64 . (+ 0) . F.castDoubleToWord64

-- Clamp between the int representations of -1/0 and 1/0
clamp32 :: Int32 -> Int32
clamp32 = P.max (-2139095041) . P.min 2139095040

-- Clamp between the int representations of -1/0 and 1/0
clamp64 :: Int64 -> Int64
clamp64 = P.max (-9218868437227405313) . P.min 9218868437227405312

triple :: forall a b k. (RealFrac a, Preorder a, Bounded b, Integral b) => Conn k a (Extended b)
triple = Conn f g h
  where
    f = liftExtended (~~ -1 / 0) (\x -> x ~~ 0 / 0 || x > high) $ \x -> if x < low then minBound else ceiling x

    g = extended (-1 / 0) (1 / 0) fromIntegral

    h = liftExtended (\x -> x ~~ 0 / 0 || x < low) (~~ 1 / 0) $ \x -> if x > high then maxBound else floor x

    low = fromIntegral $ minBound @b

    high = fromIntegral $ maxBound @b

{-
rt :: RealFloat a => a -> a
rt = uncurry encodeFloat . decodeFloat 

-- | Exact embedding up to the largest representable 'Int32'.
f32i32 :: ConnL Float (Maybe Int32)
f32i32 = Conn (nanf f) (nan g) where
  f x | abs x <~ 2**24-1 = P.ceiling x
      | otherwise = if x >~ 0 then 2^24 else minBound

  g i | abs' i <~ 2^24-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**24

-- | Exact embedding up to the largest representable 'Int32'.
i32f32 :: ConnL (Maybe Int32) Float
i32f32 = Conn (nan g) (nanf f) where
  f x | abs x <~ 2**24-1 = P.floor x
      | otherwise = if x >~ 0 then maxBound else -2^24

  g i | abs i <~ 2^24-1 = fromIntegral i
      | otherwise = if i >~ 0 then 2**24 else -1/0

-- | Exact embedding up to the largest representable 'Int64'.
f64i64 :: Conn Double (Maybe Int64)
f64i64 = Conn (nanf f) (nan g) where
  f x | abs x <~ 2**53-1 = P.ceiling x
      | otherwise = if x >~ 0 then 2^53 else minBound

  g i | abs' i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**53

-- | Exact embedding up to the largest representable 'Int64'.
f64ixx :: Conn Double (Maybe Int)
f64ixx = Conn (nanf f) (nan g) where
  f x | abs x <~ 2**53-1 = P.ceiling x
      | otherwise = if x >~ 0 then 2^53 else minBound

  g i | abs' i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**53
-}
