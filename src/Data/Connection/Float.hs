{-# Language ConstraintKinds #-}
{-# Language Safe            #-}
module Data.Connection.Float (
    fltord
  -- * Float
  , eqf
  , minSubf
  , minNormf
  , maxOddf
  , maxNormf
  , epsilonf
  , ulpf
  , shiftf 
  , withinf
  , f32c32
  , f32i08
  , f32i16
  , f32i32
  , i32f32
  -- * Double
  , eq
  , minSub
  , minNorm
  , maxOdd
  , maxNorm
  , epsilon
  , ulp
  , shift 
  , within
  , f64c64
  , f64f32
  , f64i08
  , f64i16
  , f64i32
  , f64i64
  , i64f64
  , f64ixx
  , ixxf64
) where

import safe Data.Bool
import safe Data.Connection.Conn
import safe Data.Connection.Trip
import safe Data.Function (on)
import safe Data.Int
import safe Data.Prd
import safe Data.Prd.Nan
import safe Data.Prd.Top
import safe Data.Word
import safe Foreign.C.Types
import safe GHC.Float (float2Double,double2Float)
import safe GHC.Float as F
import safe Prelude as P hiding (Ord(..), Bounded, until)

fltord :: Prd a => Floating a => Trip a (Nan Ordering)
fltord = Trip f g h where
  g (Def GT) = (1/0) 
  g (Def LT) = (-1/0) 
  g (Def EQ) = 0
  g Nan = 0/0 
  
  f x | x =~ 0/0  = Nan
      | x =~ (-1/0)  = Def LT
      | x <= 0  = Def EQ
      | otherwise  = Def GT

  h x | x =~ 0/0  = Nan
      | x =~ (1/0)  = Def GT
      | x >= 0  = Def EQ
      | otherwise  = Def LT


---------------------------------------------------------------------
-- Float
---------------------------------------------------------------------

-- | Determine bitwise equality.
--
eqf :: Float -> Float -> Bool
eqf = (==) `on` floatWord32

-- | Minimum positive float value.
--
-- >>> minSubf
-- 1.0e-45
-- >>> shiftf (-1) minSubf
-- 0
--
minSubf :: Float
minSubf = shiftf 1 0

-- | Minimum normalized value.
--
-- >>> shiftf (-1) minNormf
-- 0
-- 
minNormf :: Float
minNormf = word32Float 0x00800000

-- | Maximum representable odd integer. 
--
-- > maxOddf = 2**24 - 1
--
maxOddf :: Float
maxOddf = 1.6777215e7

-- | Maximum finite value.
--
-- > maxNormf = shiftf (-1) maximal
--
-- >>> shiftf 1 maxNormf
-- Infinity
-- 
maxNormf :: Float
maxNormf = shiftf (-1) maximal 

-- | Difference between 1 and the smallest representable value greater than 1.
--
-- > epsilonf = shiftf 1 1 - 1
--
epsilonf :: Float
epsilonf = shiftf 1 1 - 1

-- | Compute the distance between two floats in units of least precision.
--
-- @ 'ulpf' x ('shiftf' ('abs' n) x) '==' ('EQ', 'abs' n) @
--
ulpf :: Float -> Float -> (Ordering, Word32)
ulpf x y = o
  where  x' = floatInt32 x
         y' = floatInt32 y
         o  | x' > y' = (GT, fromIntegral . abs $ x' - y')
            | x' == y' = (EQ, 0)
            | otherwise = (LT, fromIntegral . abs $ y' - x')

-- | Shift a float by n units of least precision.
--
shiftf :: Int32 -> Float -> Float
shiftf n = int32Float . (+ n) . floatInt32

-- | Compare two floats for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
-- 
withinf :: Word32 -> Float -> Float -> Bool
withinf tol a b = snd (ulpf a b) <= tol

f32c32 :: Conn Float CFloat
f32c32 = Conn CFloat $ \(CFloat f) -> f

-- | All 'Int08' values are exactly representable in a 'Float'.
f32i08 :: Trip Float (Extended Int8)
f32i08 = Trip (nanf' f) (nanf g) (nanf' h) where
  f x | x > imax = Just Top
      | x =~ (-1/0) = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling x

  g = bound (-1/0) (1/0) P.fromIntegral

  h x | x =~ (1/0) = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 127 

  imin = -128

-- | All 'Int16' values are exactly representable in a 'Float'.
f32i16 :: Trip Float (Extended Int16)
f32i16 = Trip (nanf' f) (nanf g) (nanf' h) where
  f x | x > imax = Just Top
      | x =~ (-1/0) = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling x

  g = bound (-1/0) (1/0) P.fromIntegral

  h x | x =~ (1/0) = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 32767 

  imin = -32768

-- | Exact embedding up to the largest representable 'Int32'.
f32i32 :: Conn Float (Nan Int32)
f32i32 = Conn (nanf' f) (nanf g) where
  f x | abs x <= 2**24-1 = P.ceiling x
      | otherwise = if x >= 0 then 2^24 else minimal

  g i | abs' i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 1/0 else -2**24

-- | Exact embedding up to the largest representable 'Int32'.
i32f32 :: Conn (Nan Int32) Float
i32f32 = Conn (nanf g) (nanf' f) where
  f x | abs x <= 2**24-1 = P.floor x
      | otherwise = if x >= 0 then maximal else -2^24

  g i | abs i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**24 else -1/0

---------------------------------------------------------------------
-- Double
---------------------------------------------------------------------

-- | Determine bitwise equality.
--
eq :: Double -> Double -> Bool
eq = (==) `on` doubleWord64

-- | Minimum positive value.
--
-- >>> shift (-1) minSub
-- 0.0
-- 
minSub :: Double
minSub = shift 1 0

-- | Minimum normalized value.
--
-- >>> shift (-1) minNorm
-- 2.8480945388892175e-306
-- 
minNorm :: Double
minNorm = word64Double 0x0080000000000000

-- | Maximum representable odd integer. 
--
-- > maxOdd = 2**53 - 1
--
maxOdd :: Double
maxOdd = 9.007199254740991e15

-- | Maximum finite value.
--
-- > maxNorm = shift (-1) maximal
--
-- >>> shift 1 maxNorm
-- Infinity
-- 
maxNorm :: Double
maxNorm = shift (-1) maximal 

-- | Difference between 1 and the smallest representable value greater than 1.
--
-- > epsilon = shift 1 1 - 1
--
epsilon :: Double
epsilon = shift 1 1 - 1

-- | Compute signed distance in units of least precision.
--
-- @ 'ulp' x ('shift' ('abs' n) x) '==' ('EQ', 'abs' n) @
--
ulp :: Double -> Double -> (Ordering, Word64)
ulp x y = o
  where  x' = doubleInt64 x
         y' = doubleInt64 y
         o  | x' > y' = (GT, fromIntegral . abs $ x' - y')
            | x' == y' = (EQ, 0)
            | otherwise = (LT, fromIntegral . abs $ y' - x')

-- | Shift by /Int64/ units of least precision.
--
shift :: Int64 -> Double -> Double
shift n = int64Double . (+ n) . doubleInt64

-- | Compare two double-precision floats for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
-- 
within :: Word64 -> Double -> Double -> Bool
within tol a b = snd (ulp a b) <= tol

f64c64 :: Conn Double CDouble
f64c64 = Conn CDouble $ \(CDouble f) -> f

f64f32 :: Trip Double Float
f64f32 = Trip f g h where
  f x = let est = double2Float x in
          if g est >= x
          then est
          else ascendf est g x

  g = float2Double

  h x = let est = double2Float x in
          if g est <= x
          then est
          else descendf est g x

  ascendf z g1 y = until (\x -> g1 x >= y) (<=) (shiftf 1) z

  descendf z f1 x = until (\y -> f1 y <= x) (>=) (shiftf (-1)) z

-- | All 'Int8' values are exactly representable in a 'Double'.
f64i08 :: Trip Double (Extended Int8)
f64i08 = Trip (nanf' f) (nanf g) (nanf' h) where
  f x | x > imax = Just Top
      | x =~ (-1/0) = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling x

  g = bound (-1/0) (1/0) P.fromIntegral

  h x | x =~ (1/0) = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 127 

  imin = -128

-- | All 'Int16' values are exactly representable in a 'Double'.
f64i16 :: Trip Double (Extended Int16)
f64i16 = Trip (nanf' f) (nanf g) (nanf' h) where
  f x | x > imax = Just Top
      | x =~ (-1/0) = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling x

  g = bound (-1/0) (1/0) P.fromIntegral

  h x | x =~ (1/0) = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 32767 

  imin = -32768

-- | All 'Int32' values are exactly representable in a 'Double'.
f64i32 :: Trip Double (Extended Int32)
f64i32 = Trip (nanf' f) (nanf g) (nanf' h) where
  f x | x > imax = Just Top
      | x =~ (-1/0) = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling x

  g = bound (-1/0) (1/0) P.fromIntegral

  h x | x =~ (1/0) = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 2147483647 

  imin = -2147483648

-- | Exact embedding up to the largest representable 'Int64'.
f64i64 :: Conn Double (Nan Int64)
f64i64 = Conn (nanf' f) (nanf g) where
  f x | abs x <= 2**53-1 = P.ceiling x
      | otherwise = if x >= 0 then 2^53 else minimal

  g i | abs' i <= 2^53-1 = fromIntegral i
      | otherwise = if i >= 0 then 1/0 else -2**53
  
-- | Exact embedding up to the largest representable 'Int64'.
i64f64 :: Conn (Nan Int64) Double
i64f64 = Conn (nanf g) (nanf' f) where
  f x | abs x <= 2**53-1 = P.floor x
      | otherwise = if x >= 0 then maximal else -2^53

  g i | abs i <= 2^53-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**53 else -1/0

-- | Exact embedding up to the largest representable 'Int64'.
f64ixx :: Conn Double (Nan Int)
f64ixx = Conn (nanf' f) (nanf g) where
  f x | abs x <= 2**53-1 = P.ceiling x
      | otherwise = if x >= 0 then 2^53 else minimal

  g i | abs' i <= 2^53-1 = fromIntegral i
      | otherwise = if i >= 0 then 1/0 else -2**53
  
-- | Exact embedding up to the largest representable 'Int64'.
ixxf64 :: Conn (Nan Int) Double
ixxf64 = Conn (nanf g) (nanf' f) where
  f x | abs x <= 2**53-1 = P.floor x
      | otherwise = if x >= 0 then maximal else -2^53

  g i | abs i <= 2^53-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**53 else -1/0

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

{- 
f32u32 :: Conn Float Ulp32
f32u32 = Conn (Ulpf . floatInt32) (int32Float . unUlp32)

u32f32 :: Conn Ulpf Float
u32f32 = Conn (int32Float . unUlp32) (Ulpf . floatInt32)

-- correct but maybe replace w/ Graded / Yoneda / Indexed etc
u32w64 :: Conn Ulpf (Nan Word64)
u32w64 = Conn f g where
  conn = i32wf >>> w32w64

  of32set  = 2139095041 :: Word64
  of32set' = 2139095041 :: Int32

  f x@(Ulpf y) | ulp32Nan x = Nan
                | neg y = Def $ fromIntegral (y + of32set')
                | otherwise = Def $ (fromIntegral y) + of32set
               where fromIntegral = connl conn

  g x = case x of
          Nan -> Ulpf of32set'
          Def y | y < of32set -> Ulpf $ (fromIntegral y) P.- of32set'
                | otherwise  -> Ulpf $ fromIntegral ((min 4278190081 y) P.- of32set)
               where fromIntegral = connr conn
-}

{- 
f32w08 :: Trip Float (Nan Word8)
f32w08 = Trip (nanf' f) (nan (0/0) g) (nanf' h) where
  h x = if x > 0 then 0 else connr w08wf $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min 254 (h x)

-- Lift all exceptional values
extended' :: Bounded a => Floating a => (a -> b) -> a -> Extended b
extended' f = nanf' (liftBound f)

f64e32 :: Trip Double (Extended Float)
f64e32 = Trip (extended' f) (extended (0/0) g) (extended' h) where Trip f g h = f64f32

-}

abs' :: Ord a => Minimal a => Num a => a -> a
abs' x = if x =~ minimal then abs (x+1) else abs x

nanf' :: Prd a => Floating a => (a -> b) -> a -> Nan b
nanf' f x | x =~ 0/0 = Nan
          | otherwise = Def (f x)



-- Non-monotonic function 
signed64 :: Word64 -> Int64
signed64 x | x < 0x8000000000000000 = fromIntegral x
           | otherwise      = fromIntegral (maximal P.- (x P.- 0x8000000000000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned64 :: Int64 -> Word64
unsigned64 x | x >= 0  = fromIntegral x
             | otherwise = 0x8000000000000000 + (maximal P.- (fromIntegral x))

int64Double :: Int64 -> Double
int64Double = word64Double . unsigned64

doubleInt64 :: Double -> Int64
doubleInt64 = signed64 . doubleWord64 

-- Bit-for-bit conversion.
word64Double :: Word64 -> Double
word64Double = F.castWord64ToDouble

-- TODO force to pos representation?
-- Bit-for-bit conversion.
doubleWord64 :: Double -> Word64
doubleWord64 = (+0) . F.castDoubleToWord64

-- Non-monotonic function 
signed32 :: Word32 -> Int32
signed32 x | x < 0x80000000 = fromIntegral x
           | otherwise      = fromIntegral (maximal P.- (x P.- 0x80000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned32 :: Int32 -> Word32
unsigned32 x | x >= 0  = fromIntegral x
             | otherwise = 0x80000000 + (maximal P.- (fromIntegral x))

int32Float :: Int32 -> Float
int32Float = word32Float . unsigned32

floatInt32 :: Float -> Int32
floatInt32 = signed32 . floatWord32 

-- Bit-for-bit conversion.
word32Float :: Word32 -> Float
word32Float = F.castWord32ToFloat

-- TODO force to pos representation?
-- Bit-for-bit conversion.
floatWord32 :: Float -> Word32
floatWord32 = (+0) .  F.castFloatToWord32
