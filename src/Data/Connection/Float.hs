{-# Language ConstraintKinds #-}
{-# Language Safe            #-}
module Data.Connection.Float (
  -- * Float
    ordf32
  , f32ord
  , minSub32
  , minNorm32
  , maxOdd32
  , maxNorm32
  , epsilon32
  , ulp32
  , shift32 
  , within32
  --, f32i08
  --, f32i16
  --, f32i32
  --, i32f32
  -- * Double
  , f64f32
  , ordf64
  , f64ord
  , minSub64
  , minNorm64
  , maxOdd64
  , maxNorm64
  , epsilon64
  , ulp64
  , shift64 
  , within64
  --, f64i08
  --, f64i16
  --, f64i32
  --, f64i64
  --, i64f64
  --, f64ixx
  --, ixxf64
) where

import safe Data.Bool
import safe Data.Connection.Type
import safe Data.Lattice
import safe Data.Int
import safe Data.Order
import safe Data.Word
import safe GHC.Float (float2Double,double2Float)
import safe GHC.Float as F
import safe Prelude as P hiding (Ord(..), Bounded, until)

---------------------------------------------------------------------
-- Float
---------------------------------------------------------------------

-- | Minimum positive float value.
--
-- >>> minSub32
-- 1.0e-45
-- >>> shift32 (-1) minSub32
-- 0
--
minSub32 :: Float
minSub32 = shift32 1 0

-- | Minimum normalized value.
--
-- >>> shift32 (-1) minNorm32
-- 0
-- 
minNorm32 :: Float
minNorm32 = word32Float 0x00800000

-- | Maximum representable odd integer. 
--
-- > maxOdd32 = 2**24 - 1
--
maxOdd32 :: Float
maxOdd32 = 1.6777215e7

-- | Maximum finite value.
--
-- > maxNorm32 = shift32 (-1) top
--
-- >>> shift32 1 maxNorm32
-- Infinity
-- 
maxNorm32 :: Float
maxNorm32 = shift32 (-1) top 

-- | Difference between 1 and the smallest representable value greater than 1.
--
-- > epsilon32 = shift32 1 1 - 1
--
epsilon32 :: Float
epsilon32 = shift32 1 1 - 1

-- | Compute the distance between two floats in units of least precision.
--
-- @ 'ulp32' x ('shift32' ('abs' n) x) '==' ('EQ', 'abs' n) @
--
ulp32 :: Float -> Float -> (Ordering, Word32)
ulp32 x y = o
  where  x' = floatInt32 x
         y' = floatInt32 y
         o  | x' > y' = (GT, fromIntegral . abs $ x' - y')
            | x' == y' = (EQ, 0)
            | otherwise = (LT, fromIntegral . abs $ y' - x')

-- | Shift a float by n units of least precision.
--
shift32 :: Int32 -> Float -> Float
shift32 n = int32Float . (+ n) . floatInt32

-- | Compare two floats for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
-- 
within32 :: Word32 -> Float -> Float -> Bool
within32 tol a b = snd (ulp32 a b) <~ tol

f32ord :: Conn Float (Lowered Ordering)
f32ord = fldord

ordf32 :: Conn (Lifted Ordering) Float
ordf32 = ordfld

-- | All 'Int08' values are exactly representable in a 'Float'.
f32i08 :: Trip Float (Extended Int8)
f32i08 = Trip f g h where
  f x | x > imax = Top
      | x ~~ (-1/0) = Bottom
      | x < imin = Extended bottom
      | otherwise = Extended $ P.ceiling x

  g = extends P.fromIntegral

  h x | x ~~ (1/0) = Top
      | x > imax = Extended top
      | x < imin = Bottom
      | otherwise = Extended $ P.floor x

  imax = 127 

  imin = -128

-- | All 'Int16' values are exactly representable in a 'Float'.
f32i16 :: Trip Float (Extended Int16)
f32i16 = Trip f g h where
  f x | x > imax = Top
      | x ~~ -1/0 = Bottom
      | x < imin = Extended bottom
      | otherwise = Extended $ P.ceiling x

  g = extends P.fromIntegral

  h x | x ~~ 1/0 = Top
      | x > imax = Extended top
      | x < imin = Bottom
      | otherwise = Extended $ P.floor x

  imax = 32767 

  imin = -32768

-- | Exact embedding up to the largest representable 'Int32'.
f32i32 :: Conn Float (Maybe Int32)
f32i32 = Conn (nanf f) (nan g) where
  f x | abs x <~ 2**24-1 = P.ceiling x
      | otherwise = if x >~ 0 then 2^24 else bottom

  g i | abs' i <~ 2^24-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**24

-- | Exact embedding up to the largest representable 'Int32'.
i32f32 :: Conn (Maybe Int32) Float
i32f32 = Conn (nan g) (nanf f) where
  f x | abs x <~ 2**24-1 = P.floor x
      | otherwise = if x >~ 0 then top else -2^24

  g i | abs i <~ 2^24-1 = fromIntegral i
      | otherwise = if i >~ 0 then 2**24 else -1/0

---------------------------------------------------------------------
-- Double
---------------------------------------------------------------------

-- | Minimum positive value.
--
-- >>> shift64 (-1) minSub64
-- 0.0
-- 
minSub64 :: Double
minSub64 = shift64 1 0

-- | Minimum normalized value.
--
-- >>> shift (-1) minNorm64
-- 2.8480945388892175e-306
-- 
minNorm64 :: Double
minNorm64 = word64Double 0x0080000000000000

-- | Maximum representable odd integer. 
--
-- > maxOdd64 = 2**53 - 1
--
maxOdd64 :: Double
maxOdd64 = 9.007199254740991e15

-- | Maximum finite value.
--
-- > maxNorm64 = shift64 (-1) top
--
-- >>> shift64 1 maxNorm64
-- Infinity
-- 
maxNorm64 :: Double
maxNorm64 = shift64 (-1) top 

-- | Difference between 1 and the smallest representable value greater than 1.
--
-- > epsilon64 = shift64 1 1 - 1
--
epsilon64 :: Double
epsilon64 = shift64 1 1 - 1

-- | Compute signed distance in units of least precision.
--
-- @ 'ulp64' x ('shift64' ('abs' n) x) '==' ('EQ', 'abs' n) @
--
ulp64 :: Double -> Double -> (Ordering, Word64)
ulp64 x y = o
  where  x' = doubleInt64 x
         y' = doubleInt64 y
         o  | x' > y' = (GT, fromIntegral . abs $ x' - y')
            | x' == y' = (EQ, 0)
            | otherwise = (LT, fromIntegral . abs $ y' - x')

-- | Shift by /Int64/ units of least precision.
--
shift64 :: Int64 -> Double -> Double
shift64 n = int64Double . (+ n) . doubleInt64

-- | Compare two double-precision floats for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
-- 
within64 :: Word64 -> Double -> Double -> Bool
within64 tol a b = snd (ulp64 a b) <~ tol

f64f32 :: Trip Double Float
f64f32 = Trip f g h where
  f x = let est = double2Float x in
          if g est >~ x
          then est
          else ascendf est g x

  g = float2Double

  h x = let est = double2Float x in
          if g est <~ x
          then est
          else descendf est g x

  ascendf z g1 y = until (\x -> g1 x >~ y) (<~) (shift32 1) z

  descendf z f1 x = until (\y -> f1 y <~ x) (>~) (shift32 (-1)) z

f64ord :: Conn Double (Lowered Ordering)
f64ord = fldord

ordf64 :: Conn (Lifted Ordering) Double
ordf64 = ordfld

-- | All 'Int8' values are exactly representable in a 'Double'.
f64i08 :: Trip Double (Extended Int8)
f64i08 = Trip f g h where
  f x | x > imax = Top
      | x ~~ (-1/0) || x ~~ (0/0) = Bottom
      | x < imin = Extended bottom
      | otherwise = Extended $ P.ceiling x

  g = extends P.fromIntegral

  h x | x ~~ (1/0) = Top
      | x > imax = Extended top
      | x < imin = Bottom
      | otherwise = Extended $ P.floor x

  imax = 127 

  imin = -128

-- | All 'Int16' values are exactly representable in a 'Double'.
f64i16 :: Trip Double (Extended Int16)
f64i16 = Trip f g h where
  f x | x > imax = Top
      | x ~~ (-1/0) || x ~~ (0/0) = Bottom
      | x < imin = Extended bottom
      | otherwise = Extended $ P.ceiling x

  g = extends P.fromIntegral

  h x | x ~~ (1/0) = Top
      | x > imax = Extended top
      | x < imin = Bottom
      | otherwise = Extended $ P.floor x

  imax = 32767 

  imin = -32768

-- | All 'Int32' values are exactly representable in a 'Double'.
f64i32 :: Trip Double (Extended Int32)
f64i32 = Trip f g h where
  f x | x > imax = Top
      | x ~~ (-1/0) || x ~~ (0/0) = Bottom
      | x < imin = Extended bottom
      | otherwise = Extended $ P.ceiling x

  g = extends P.fromIntegral

  h x | x ~~ (1/0) = Top
      | x > imax = Extended top
      | x < imin = Bottom
      | otherwise = Extended $ P.floor x

  imax = 2147483647 

  imin = -2147483648

-- | Exact embedding up to the largest representable 'Int64'.
f64i64 :: Conn Double (Maybe Int64)
f64i64 = Conn (nanf f) (nan g) where
  f x | abs x <~ 2**53-1 = P.ceiling x
      | otherwise = if x >~ 0 then 2^53 else bottom

  g i | abs' i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**53
  
-- | Exact embedding up to the largest representable 'Int64'.
i64f64 :: Conn (Maybe Int64) Double
i64f64 = Conn (nan g) (nanf f) where
  f x | abs x <~ 2**53-1 = P.floor x
      | otherwise = if x >~ 0 then top else -2^53

  g i | abs i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 2**53 else -1/0

-- | Exact embedding up to the largest representable 'Int64'.
f64ixx :: Conn Double (Maybe Int)
f64ixx = Conn (nanf f) (nan g) where
  f x | abs x <~ 2**53-1 = P.ceiling x
      | otherwise = if x >~ 0 then 2^53 else bottom

  g i | abs' i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**53
  
-- | Exact embedding up to the largest representable 'Int64'.
ixxf64 :: Conn (Maybe Int) Double
ixxf64 = Conn (nan g) (nanf f) where
  f x | abs x <~ 2**53-1 = P.floor x
      | otherwise = if x >~ 0 then top else -2^53

  g i | abs i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 2**53 else -1/0

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

{-
f32c32 :: Conn Float CFloat
f32c32 = Conn CFloat $ \(CFloat f) -> f

f64c64 :: Conn Double CDouble
f64c64 = Conn CDouble $ \(CDouble f) -> f

f32u32 :: Conn Float Ulp32
f32u32 = Conn (Ulpf . floatInt32) (int32Float . unUlp32)

u32f32 :: Conn Ulpf Float
u32f32 = Conn (int32Float . unUlp32) (Ulpf . floatInt32)

-- correct but maybe replace w/ Graded / Yoneda / Indexed etc
u32w64 :: Conn Ulpf (Maybe Word64)
u32w64 = Conn f g where
  conn = i32wf >>> w32w64

  of32set  = 2139095041 :: Word64
  of32set' = 2139095041 :: Int32

  f x@(Ulpf y) | ulp32Maybe x = Maybe
               | neg y = Just $ fromIntegral (y + of32set')
               | otherwise = Just $ (fromIntegral y) + of32set
               where fromIntegral = connl conn

  g x = case x of
          Maybe -> Ulpf of32set'
          Just y | y < of32set -> Ulpf $ (fromIntegral y) P.- of32set'
                | otherwise  -> Ulpf $ fromIntegral ((min 4278190081 y) P.- of32set)
               where fromIntegral = connr conn

--order of magnitude
f32w08 :: Trip Float (Maybe Word8)
f32w08 = Trip (nanf f) (nan (0/0) g) (nanf h) where
  h x = if x > 0 then 0 else connr w08wf $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min 254 (h x)

-}

abs' :: (Eq a, Bounded a, Num a) => a -> a
abs' x = if x ~~ bottom then abs (x+1) else abs x

nanf :: (Eq a, Lattice a) => Floating a => (a -> b) -> a -> Maybe b
nanf f x | x ~~ 0/0 = Nothing
         | otherwise = Just (f x)

nan :: Fractional b => (a -> b) -> Maybe a -> b
nan = maybe (0/0)

extf f x | x ~~ 0/0 = Bottom -- ?
         | otherwise = Extended (f x)

-- Non-monotonic function 
signed64 :: Word64 -> Int64
signed64 x | x < 0x8000000000000000 = fromIntegral x
           | otherwise      = fromIntegral (top P.- (x P.- 0x8000000000000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned64 :: Int64 -> Word64
unsigned64 x | x >~ 0  = fromIntegral x
             | otherwise = 0x8000000000000000 + (top P.- (fromIntegral x))

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
           | otherwise      = fromIntegral (top P.- (x P.- 0x80000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned32 :: Int32 -> Word32
unsigned32 x | x >~ 0  = fromIntegral x
             | otherwise = 0x80000000 + (top P.- (fromIntegral x))

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

fldord :: (Bounded a, Fractional a) => Conn a (Lowered Ordering)
fldord = Conn (Left . f) (lowered g) where
  g GT = top
  g EQ = 0
  g LT = bottom
  
  f x | x ~~ bottom = LT
      | x <~ 0      = EQ
      | otherwise   = GT

ordfld :: (Bounded a, Fractional a) => Conn (Lifted Ordering) a
ordfld = Conn (lifted g) (Right . h) where
  g GT = top
  g EQ = 0
  g LT = bottom

  h x | x ~~ top  = GT
      | x >~ 0    = EQ
      | otherwise = LT
