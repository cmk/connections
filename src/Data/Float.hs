{-# LANGUAGE CPP, ForeignFunctionInterface #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Float (
    Float
  , module Data.Float
  , module F
) where

import Prelude hiding (Num(..), Fractional(..), Floating(..),  (^^), (^), RealFloat(..), Real(..), Enum(..))

import Control.Category ((>>>))
import Foreign.C
import Data.Word
import Data.Prd.Nan hiding (isNan)
import Data.Int
import Data.Prd
import Data.Semifield
import Data.Semiring
import Data.Semigroup.Join
import Data.Function (on)
import Data.Connection 

--import Data.Numbers.CrackNum (floatToFP)
import Data.Bits ((.&.))


import GHC.Real hiding (Fractional(..), (^^), (^), div)
import Data.Ratio

import qualified Prelude as P
import qualified Control.Category as C
import qualified Data.Bits as B
import GHC.Float as F
import qualified GHC.Float.RealFracMethods as R

{-
λ> unit f32i64 aNan
Float (-9.223372e18)
λ> F.float2Int (3.0252336e+35)
-9223372036854775808
λ> F.float2Int (3.0252336e+25)
-9223372036854775808

TODO:
different Conns for embedding a Float in the lower portion of a Double,
versus middle / higher

-}


----------------------------------------------------------------
-- Float utils
----------------------------------------------------------------


-- | Bitwise equality.
eqf :: Float -> Float -> Bool
eqf = (==) `on` floatWord32

signBitf :: Float -> Bool
signBitf x = if x =~ anan then False else msbMask x /= 0

evenBitf :: Float -> Bool
evenBitf x = lsbMask x == 0

-- | maximal (positive) finite value.
maxNormf :: Float
maxNormf = shiftf (-1) (1/0)

-- | minimal (positive) normalized value.
minNormf :: Float
minNormf = word32Float 0x00800000

-- | maximal representable odd integer. 
--
-- @ maxOddf = 2**24 - 1@
--
maxOddf :: Float
maxOddf = 16777215

-- | minimal (positive) value.
minSubf :: Float
minSubf = shiftf 1 0

-- | difference between 1 and the smallest representable value greater than 1.
epsilonf :: Float
epsilonf = shiftf 1 1 - 1

splitf :: Float -> Either Float Float
splitf x = case signBitf x of
  True -> Left x
  _    -> Right x




-- | Shift by /Int32/ units of least precision.

-- TODO replace w/ Yoneda / Index / Graded
shiftf :: Int32 -> Float -> Float
shiftf n = int32Float . (+ n) . floatInt32

-- | Compare two 'Float' values for approximate equality, using
-- Dawson's method.
--
-- required accuracy is specified in ULPs (units of least
-- precision).  If the two numbers differ by the given number of ULPs
-- or less, this function returns @True@.
withinf :: Word32 -> Float -> Float -> Bool
withinf tol a b = ulpDistance a b <~ tol


ulps :: Float -> Float -> (Bool, Word32)
ulps x y = o
  where  x' = floatInt32 x
         y' = floatInt32 y
         o  | x' >~ y' = (False, fromIntegral . abs $ x' - y')
            | otherwise = (True, fromIntegral . abs $ y' - x')

ulpDistance :: Float -> Float -> Word32
ulpDistance x y = snd $ ulps x y

ulpDelta :: Float -> Float -> Int
ulpDelta x y = if lesser then d' else (-1) * d'
  where (lesser, d) = ulps x y
        d' = fromIntegral d

ulpDelta' :: Float -> Float -> Int32
ulpDelta' x y = if lesser then d' else (-1) * d'
  where (lesser, d) = ulps x y
        d' = fromIntegral d


----------------------------------------------------------------
-- Float connections
----------------------------------------------------------------

{-
f32ord :: Trip Float (Nan Ordering)
f32ord = fldord

  g (Def GT) = 1/0
  g (Def LT) = - 1/0
  g (Def EQ) = 0
  g Nan = 0/0
  
  f x | isNaN x    = Nan
  f x | isInf (-x) = Def LT
  f x | x <~ 0     = Def EQ
  f x | otherwise  = Def GT

  h x | isNaN x    = Nan
  h x | isInf x    = Def GT
  h x | x >~ 0     = Def EQ
  h x | otherwise  = Def LT
-}



-- TODO: 
-- * handle underflow / overflow / loss of precision
-- * try using 'properFraction'
ratf32 :: Trip Rational Float
ratf32 = Trip f g h
  where h (0 :% 0) = 0/0
        h (x :% 0) = if x > 0 then 1/0 else (-1/0)
        h x = P.fromRational x --F.fromRat' x

        g x | F.isFloatNaN x == 1 = 0 :% 0
            | F.isFloatInfinite x == 1 = if x > 0 then (1 :% 0) else (-1 :% 0)
            | otherwise = toRational x

        -- fix / remove
        help x = case pcompare x 0 of
                   Just LT -> shiftf (-1) x
                   Just EQ -> x
                   Just GT -> shiftf 1 x
                   Nothing -> 0/0

        f x = let y = h x in if g y `ne` x then help y else y

{-

--TODO check these 4 probably buggy
f32ixx :: Trip Float (Nan (Inf Int))
f32ixx = Trip
  (liftNan f)
  (nan (0/0) $ g)
  (liftNan h)
  where
    f x | not (finite x) && signBit x = minimal
        | not (finite x) && not (signBit x) = maximal
        | otherwise = R.celingFloatInt x

    g = F.int2Float

    h x | not (finite x) && signBit x = minimal
        | not (finite x) && not (signBit x) = maximal
        | otherwise = R.floorFloatInt x

f64ixx :: Trip Double (Nan Int)
f64ixx = Trip
  (liftNan R.ceilingDoubleInt)
  (nan (0/0) $ F.int2Double)
  (liftNan R.floorDoubleInt)

-}


-- >>> ceiling' f32int (0/0)
-- Nan
-- >>> ceiling' f32int 0.1
-- Def 1
-- >>> ceiling' f32int 0.9
-- Def 1
-- >>> ceiling' f32int 1.1
-- Def 2
-- >>> ceiling' f32int (-1.1)
-- Def (-1)
--
{- slightly broken
f32int :: Trip Float (Nan Integer)
f32int = Trip
  (liftNan R.ceilingFloatInteger)
  (nan (0/0) $ flip F.rationalToFloat 1) -- TODO map large / small ints to Inf / NInf
  (liftNan R.floorFloatInteger)

f64int :: Trip Double (Nan Integer)
f64int = Trip
  (liftNan R.ceilingDoubleInteger)
  (nan (0/0) $ flip F.rationalToDouble 1)
  (liftNan R.floorDoubleInteger)

f32w08 :: Trip Float (Nan Word8)
f32w08 = Trip (liftNan f) (nan (0/0) g) (liftNan h) where
  h x = if x > 0 then 0 else connr w08w32 $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min 254 (h x)
-}



----------------------------------------------------------------
-- Ulp32
----------------------------------------------------------------

-- | 32 bit unit of least precision type.
--
newtype Ulp32 = Ulp32 { unUlp32 :: Int32 } deriving Show

ulp32Nan :: Ulp32 -> Bool
ulp32Nan (Ulp32 x) = x /= (min 2139095040 . max (- 2139095041)) x

instance Eq Ulp32 where
    x == y | ulp32Nan x && ulp32Nan y = True
           | ulp32Nan x || ulp32Nan y = False
           | otherwise                = on (==) unUlp32 x y

instance Prd Ulp32 where
    x <~ y | ulp32Nan x && ulp32Nan y = True
           | ulp32Nan x || ulp32Nan y = False
           | otherwise                = on (<~) unUlp32 x y

instance Minimal Ulp32 where
    minimal = Ulp32 $ -2139095041

instance Maximal Ulp32 where
    maximal = Ulp32 $ 2139095040

instance Semigroup (Additive Ulp32) where
    Additive (Ulp32 x) <> Additive (Ulp32 y) = Additive . Ulp32 $ x + y

instance Monoid (Additive Ulp32) where
    mempty = Additive $ Ulp32 0

instance Semigroup (Multiplicative Ulp32) where
    Multiplicative (Ulp32 x) <> Multiplicative (Ulp32 y) = Multiplicative . Ulp32 $ x * y

instance Monoid (Multiplicative Ulp32) where
    mempty = Multiplicative $ Ulp32 1

instance Presemiring Ulp32
instance Semiring Ulp32

instance Semigroup (Join Ulp32) where
    Join (Ulp32 x) <> Join (Ulp32 y) = Join . Ulp32 $ max x y

f32u32 :: Conn Float Ulp32
f32u32 = Conn (Ulp32 . floatInt32) (int32Float . unUlp32)

u32f32 :: Conn Ulp32 Float
u32f32 = Conn (int32Float . unUlp32) (Ulp32 . floatInt32)

-- fromIntegral (maxBound :: Ulp32) + 1 , image of aNan


--newtype Ulp a = Ulp { unUlp :: a }
-- instance 
{- correct but should replace w/ Graded / Yoneda / Indexed etc
u32w64 :: Conn Ulp32 (Nan Word64)
u32w64 = Conn f g where
  conn = i32w32 >>> w32w64

  offset  = 2139095041 :: Word64
  offset' = 2139095041 :: Int32

  f x@(Ulp32 y) | ulp32Nan x = Nan
                | negative y = Def $ fromIntegral (y + offset')
                | otherwise = Def $ (fromIntegral y) + offset
               where fromIntegral = connl conn

  g x = case x of
          Nan -> Ulp32 offset'
          Def y | y < offset -> Ulp32 $ (fromIntegral y) P.- offset'
                | otherwise  -> Ulp32 $ fromIntegral ((min 4278190081 y) P.- offset)
               where fromIntegral = connr conn
-}

{-

-- |
-- Calculate relative error of two numbers:
--
-- \[ \frac{|a - b|}{\max(|a|,|b|)} \]
--
-- It lies in [0,1) interval for numbers with same sign and (1,2] for
-- numbers with different sign. If both arguments are zero or negative
-- zero function returns 0. If at least one argument is transfinite it
-- returns NaN
relativeError :: Float -> Float -> Float
relativeError a b
  | a == 0 && b == 0 = 0
  | otherwise        = abs (a - b) / fmax (abs a) (abs b) -- TODO need /

-- | Check that relative error between two numbers @a@ and @b@. If
-- 'relativeError' returns Nan it returns @False@.
eqRelErr :: Float -- ^ /eps/ relative error should be in [0,1) range
         -> Float -- ^ /a/
         -> Float -- ^ /b/
         -> Bool
eqRelErr eps a b = relativeError a b < eps

-}



-- internal


--
--TODO handle neg case, get # of nans/denormals, collect constants         

abs' :: Eq a => Ord a => Bound a => Ring a => a -> a
abs' x = if x == minimal then abs (x+one) else abs x


lsbMask :: Float -> Word32
lsbMask x = 0x00000001 .&. floatWord32 x

msbMask :: Float -> Word32
msbMask x = 0x80000000 .&. floatWord32 x

-- floatWord32 maximal == exponent maximal
expMask :: Float -> Word32
expMask x = 0x7f800000 .&. floatWord32 x

-- chk f = f >= 0 ==> f == word32Float $ exponent f + significand f
sigMask :: Float -> Word32
sigMask x = 0x007FFFFF .&. floatWord32 x



{-
-- | first /NaN/ value. 
--naN :: Float
--naN = 0/0 -- inc pInf 

-- | Positive infinity
--
-- @nInf = 1/0@
--
pInf :: Float
pInf = word32Float 0x7f800000

-- | Negative infinity
--
-- @nInf = -1/0@
--
nInf :: Float
nInf = word32Float 0xff800000 
-}


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

-- TODO force to positive representation?
-- Bit-for-bit conversion.
floatWord32 :: Float -> Word32
floatWord32 = (+0) .  F.castFloatToWord32

