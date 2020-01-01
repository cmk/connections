{-# LANGUAGE CPP, ForeignFunctionInterface #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Float (
    Float
  , module Data.Float
  , module Data.Connection.Float
) where

import Prelude hiding (Floating(..), RealFloat(..), Real(..), Enum(..))

import Foreign.C
import Data.Word
import Data.Prd.Nan
import Data.Connection.Float
import Data.Int (Int32)
import Data.Prd
import Data.Function (on)
import Data.Connection 

--import Data.Numbers.CrackNum (floatToFP)
import Data.Bits ((.&.))

import qualified Prelude as P
import qualified Data.Bits as B
import qualified GHC.Float as F

--disp x = floatToFP x


split :: Float -> Either Float Float
split x = case signBit x of
  True -> Left x
  _    -> Right x

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

signBit :: Float -> Bool
signBit x = if isNanf x then False else msbMask x /= 0

evenBit :: Float -> Bool
evenBit x = lsbMask x == 0

-- | maximal (positive) finite value.
maxNorm :: Float
maxNorm = shift (-1) pInf

-- | minimal (positive) normalized value.
minNorm :: Float
minNorm = word32Float 0x00800000

-- | maximal representable odd integer. 
--
-- @ maxOdd = 2**24 - 1@
--
maxOdd :: Float
maxOdd = 16777215

-- | minimal (positive) value.
minSub :: Float
minSub = shift 0 1

-- | difference between 1 and the smallest representable value greater than 1.
epsilon :: Float
epsilon = shift 1 1 - 1

-- | first /NaN/ value. 
aNan :: Float
aNan = 0/0 -- inc pInf 

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

-- Bitwise equality
eq' :: Float -> Float -> Bool
eq' = (==) `on` floatWord32

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

-- | 
--
-- @nan x == indeterminate x@
--
isNanf :: Float -> Bool
isNanf x = F.isFloatNaN x == 1

pinf :: Float -> Bool
pinf x = infinite x && positive x 

ninf :: Float -> Bool
ninf x = infinite x && negative x

infinite :: Float -> Bool
infinite x = F.isFloatInfinite x == 1

denormalized :: Float -> Bool
denormalized x = F.isFloatDenormalized x == 1

finite :: Float -> Bool
finite x = F.isFloatFinite x == 1

nzero :: Float -> Bool
nzero x = F.isFloatNegativeZero x == 1


----------------------------------------------------------------
-- Ulps-based comparison
----------------------------------------------------------------

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

----------------------------------------------------------------
-- Ulps-based comparison
----------------------------------------------------------------

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

-- | Compare two 'Float' values for approximate equality, using
-- Dawson's method.
--
-- required accuracy is specified in ULPs (units of least
-- precision).  If the two numbers differ by the given number of ULPs
-- or less, this function returns @True@.
within :: Word32 -> Float -> Float -> Bool
within tol a b = ulpDistance a b <~ tol

{-
foreign import ccall unsafe "fdim" fdim :: Double -> Double -> Double

foreign import ccall unsafe "fdimf" fdim :: Float -> Float -> Float

foreign import ccall unsafe "fmaxf" fmax :: Float -> Float -> Float

foreign import ccall unsafe "fminf" fmin :: Float -> Float -> Float


-- Arithmetic functions

mul :: Float -> Float -> Float
mul = liftFloat2 F.timesFloat 

-- | 'pow' returns the value of x to the exponent y.
--
pow :: Float -> Float -> Float
pow = liftFloat2 F.powerFloat

add :: Float -> Float -> Float
add = liftFloat2 F.plusFloat

sub :: Float -> Float -> Float
sub = liftFloat2 F.minusFloat

neg :: Float -> Float
neg = liftFloat F.negateFloat

div :: Float -> Float -> Float
div = liftFloat2 F.divideFloat

-- | 'sqrt' returns the non-negative square root of x.
--
sqrt :: Float -> Float
sqrt = liftFloat F.sqrtFloat

-- | 'fabs' returns the absolute value of a floating-point number x.
--
fabs :: Float -> Float
fabs = liftFloat F.fabsFloat

-- | 'fma a x b' returns /a*x + b/
foreign import ccall unsafe "fmaf" fma :: Float -> Float -> Float -> Float

-- | 'cbrt' returns the cube root of x.
--
foreign import ccall unsafe "cbrtf" cbrt :: Float -> Float


-- Exponential and logarithmic functions

-- | 'exp' returns /e/ raised to the value of the given argument /x/. 
--
exp :: Float -> Float
exp = liftFloat F.expFloat

-- | 'exp2' returns 2 raised to the value of the given argument /x/. 
--
foreign import ccall unsafe "exp2f" exp2 :: Float -> Float

-- | 'exmp1' returns the exponential of /x-1/.
--
expm1 :: Float -> Float
expm1 = liftFloat F.expm1Float

-- | 'log' returns the value of the natural logarithm of argument x.
--
log :: Float -> Float
log = liftFloat F.logFloat

-- | 'log1pf' returns the log of 1+x.
--
log1p :: Float -> Float
log1p = liftFloat F.log1pFloat

-- | 'ilogb' returns x's exponent n, in integer format.
--    ilogb(+-Infinity) re- turns INT_MAX and ilogb(0) returns INT_MIN.
--
foreign import ccall unsafe "ilogbf" ilogb :: Float -> CInt

-- | ldexp function multiplies a floating-point number by an integral power of 2.
-- ldexp is not defined in the Haskell 98 report.
--
foreign import ccall unsafe "ldexpf" ldexp :: Float -> CInt -> Float

-- | 'log10' returns the value of the logarithm of argument x to base 10.
-- log10 is not defined in the Haskell 98 report.
--
foreign import ccall unsafe "log10f" log10 :: Float -> Float

-- | 'log1pf' returns the log of 1+x.
--
--foreign import ccall unsafe "log1pf" log1p :: Float -> Float

foreign import ccall unsafe "log2f" log2 :: Float -> Float

-- | 'logb' returns x's exponent n, a signed integer converted to floating-point.  
-- 
-- > logb(+-Infinity) = +Infinity;
-- > logb(0) = -Infinity with a division by zero exception.
--
foreign import ccall unsafe "logbf" logb :: Float -> Float

-- | scalbn(x, n) returns x*(2**n) computed by exponent manipulation.
foreign import ccall unsafe "scalbnf" scalbn :: Float -> CInt -> Float

-- | scalbln(x, n) returns x*(2**n) computed by exponent manipulation.
foreign import ccall unsafe "scalblnf" scalbln :: Float -> CLong -> Float



-- Trigonometric functions

-- | 'hypot' returns the sqrt(x*x+y*y) in such a way that
-- underflow will not happen, and overflow occurs only if the final result
-- deserves it.  
-- 
-- > hypot(Infinity, v) = hypot(v, Infinity) = +Infinity for all v, including NaN.
--
foreign import ccall unsafe "hypotf" hypot :: Float -> Float -> Float

-- | 'tan' returns the tangent of x (measured in radians). 
-- A large magnitude argument may yield a result with little or no
-- significance.
--
tan :: Float -> Float
tan = liftFloat F.tanFloat

-- | 'sin' returns the sine of x (measured in radians). 
-- A large magnitude argument may yield a result with little or no
-- significance.
--
sin :: Float -> Float
sin = liftFloat F.sinFloat

-- | 'cos' returns the cosine of x (measured in radians).
--
-- A large magnitude argument may yield a result with little or no significance.  
--
cos :: Float -> Float
cos = liftFloat F.cosFloat

-- | 'atan' returns the principal value of the arc tangent of x
-- in the range [-pi/2, +pi/2].
--
atan :: Float -> Float
atan = liftFloat F.atanFloat

-- | 'atan2' returns the principal value of the arc tangent of
-- y/x, using the signs of both arguments to determine the quadrant of the
-- return value.
--
foreign import ccall unsafe "atan2f"  atan2 :: Float -> Float -> Float

-- | 'asin' returns the principal value of the arc sine of x in the range [-pi/2, +pi/2].
--
asin :: Float -> Float
asin = liftFloat F.asinFloat

-- | 'acos' returns the principal value of the arc cosine of x in the range [0, pi]
--
acos :: Float -> Float
acos = liftFloat F.acosFloat

-- | 'tanh' returns the hyperbolic tangent of x.
--
tanh :: Float -> Float
tanh = liftFloat F.tanhFloat

-- | 'sinh' returns the hyperbolic sine of x.
--
sinh :: Float -> Float
sinh = liftFloat F.sinhFloat

-- | 'cosh' returns the hyperbolic cosine of x.
--
cosh :: Float -> Float
cosh = liftFloat F.coshFloat

-- | 'atanh' returns the inverse hyperbolic tangent of x.
--
atanh :: Float -> Float
atanh = liftFloat F.atanh

-- | 'asinh' returns the inverse hyperbolic sine of x.
--
asinh :: Float -> Float
asinh = liftFloat F.asinh

-- | 'acosh' returns the inverse hyperbolic cosine of x.
--
acosh :: Float -> Float
acosh = liftFloat F.acosh

liftFloat :: (F.Float -> F.Float) -> Float -> Float
liftFloat f x = Float $ f x

liftFloat' :: (F.Float -> a) -> Float -> a
liftFloat' f x = f x

liftFloat2 :: (F.Float -> F.Float -> F.Float) -> Float -> Float -> Float
liftFloat2 f x (Float y) = Float $ f x y

liftFloat2' :: (F.Float -> F.Float -> a) -> Float -> Float -> a
liftFloat2' f x (Float y) = f x y
-}
