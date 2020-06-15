{-# Language ConstraintKinds #-}
{-# Language Safe            #-}
module Data.Connection.Float (
  -- * Connections
    f32i08
  , f32i16
  --, f32i32
  , min32
  , max32
  , covers
  , ulp
  , shift
  , within
  , epsilon
) where

import safe Data.Bool
import safe Data.Connection.Conn
import safe Data.Int
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Order.Syntax
import safe Data.Word
import safe GHC.Float as F
import safe Prelude hiding (Eq(..), Ord(..), until)
import safe qualified Prelude as P 

---------------------------------------------------------------------
-- Float
---------------------------------------------------------------------

-- | A /NaN/-handling min32 function.
--
-- > min32 x NaN = x
-- > min32 NaN y = y
--
min32 :: Float -> Float -> Float
min32 x y = case (isNaN x, isNaN y) of
  (False, False) -> if x <= y then x else y
  (False, True) -> x
  (True, False) -> y
  (True, True)  -> x

-- | A /NaN/-handling max32 function.
--
-- > max32 x NaN = x
-- > max32 NaN y = y
--
max32 :: Float -> Float -> Float
max32 x y = case (isNaN x, isNaN y) of
  (False, False) -> if x >= y then x else y
  (False, True) -> x
  (True, False) -> y
  (True, True)  -> x

-- | Covering relation on the /N5/ lattice of floats.
--
-- < https://en.wikipedia.org/wiki/Covering_relation >
--
-- >>> covers 1 (shift 1 1)
-- True
-- >>> covers 1 (shift 2 1)
-- False
--
covers :: Float -> Float -> Bool
covers x y = x ~~ shift (-1) y

-- | Compute the signed distance between two floats in units of least precision.
--
-- >>> ulp 1.0 (shift 1 1.0)
-- Just (LT,1)
-- >>> ulp (0.0/0.0) 1.0
-- Nothing
--
ulp :: Float -> Float -> Maybe (Ordering, Word32)
ulp x y = fmap f $ pcompare x y
  where  x' = floatInt32 x
         y' = floatInt32 y
         f LT = (LT, fromIntegral . abs $ y' - x')
         f EQ = (EQ, 0)
         f GT = (GT, fromIntegral . abs $ x' - y')

-- | Shift a float by /n/ units of least precision.
--
-- >>> shift 1 0
-- 1.0e-45
-- >>> shift 1 $ 0/0
-- NaN
-- >>> shift (-1) $ 0/0
-- NaN
-- >>> shift 1 $ 1/0
-- Infinity
--
shift :: Int32 -> Float -> Float
shift n x | x ~~ 0/0 = x
          | otherwise = int32Float . clamp32 . (+ n) . floatInt32 $ x

-- | Compare two floats for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
-- 
within :: Word32 -> Float -> Float -> Bool
within tol x y = maybe False ((<= tol) . snd) $ ulp x y

-- | Difference between 1 and the smallest representable value greater than 1.
--
-- > epsilon = shift 1 1 - 1
--
-- >>> epsilon
-- 1.1920929e-7
--
epsilon :: Float
epsilon = shift 1 1.0 - 1.0

{-
-- | Minimal32 positive value.
--
-- >>> minimal32
-- 1.0e-45
-- >>> shift (-1) minimal32
-- 0
--
minimal32 :: Float
minimal32 = shift 1 0.0

-- | Maximum finite value.
--
-- >>> maximal32
-- 3.4028235e38
-- >>> shift 1 maximal32
-- Infinity
-- >>> shift (-1) $ negate maximal32
-- -Infinity
--
maximal32 :: Float
maximal32 = shift (-1) maxBound 

-}

---------------------------------------------------------------------
-- Float
---------------------------------------------------------------------

-- | All 'Data.Int.Int08' values are exactly representable in a 'Float'.
f32i08 :: Conn k Float (Extended Int8)
f32i08 = signedTriple 127

-- | All 'Data.Int.Int16' values are exactly representable in a 'Float'.
f32i16 :: Conn k Float (Extended Int16)
f32i16 = signedTriple 32767

{-
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
-}

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

signedTriple :: (Bounded a, Integral a) => Float -> Conn k Float (Extended a)
signedTriple high = Conn f g h where

  f = liftExtended (~~ -1/0) (\x -> x ~~ 0/0 || x > high) $ \x -> if x < low then minBound else P.ceiling x

  g = extended (-1/0) (1/0) P.fromIntegral
 
  h = liftExtended (\x -> x ~~ 0/0 || x < low) (~~ 1/0) $ \x -> if x > high then maxBound else P.floor x

  low = -1 - high

-- Non-monotonic function 
signed32 :: Word32 -> Int32
signed32 x | x < 0x80000000 = fromIntegral x
           | otherwise      = fromIntegral (maxBound - (x - 0x80000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned32 :: Int32 -> Word32
unsigned32 x | x >= 0  = fromIntegral x
             | otherwise = 0x80000000 + (maxBound - (fromIntegral x))

-- Clamp between the int representations of -1/0 and 1/0 
clamp32 :: Int32 -> Int32
clamp32 = P.max (-2139095041) . P.min 2139095040

int32Float :: Int32 -> Float
int32Float = word32Float . unsigned32

floatInt32 :: Float -> Int32
floatInt32 = signed32 . floatWord32 

-- Bit-for-bit conversion.
word32Float :: Word32 -> Float
word32Float = F.castWord32ToFloat

-- Bit-for-bit conversion.
floatWord32 :: Float -> Word32
floatWord32 = (+0) .  F.castFloatToWord32


{-

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
                | otherwise  -> Ulpf $ fromIntegral ((min32 4278190081 y) P.- of32set)
               where fromIntegral = connr conn

--order of magnitude
f32w08 :: Trip Float (Maybe Word8)
f32w08 = Trip (nanf f) (nan (0/0) g) (nanf h) where
  h x = if x > 0 then 0 else connr w08wf $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min32 254 (h x)

abs' :: (Eq a, Bounded a, Num a) => a -> a
abs' x = if x ~~ minBound then abs (x+1) else abs x

-- Bit-for-bit conversion.
word32Float :: Word32 -> Float
word32Float = F.castWord32ToFloat

-- TODO force to pos representation?
-- Bit-for-bit conversion.
floatWord32 :: Float -> Word32
floatWord32 = (+0) .  F.castFloatToWord32
-}

