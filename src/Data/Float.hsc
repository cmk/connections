{-# LANGUAGE CPP, ForeignFunctionInterface #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Float (
    Float
  , Double
  , module Data.Float
) where

import Data.Bits ((.&.))
import Data.Connection 
import Data.Function (on)
import Data.Int
import Data.Prd
import Data.Word
import Foreign hiding (shift)
import Foreign.C
import GHC.Float as F
import Prelude hiding (Ord(..), Enum(..))
import System.IO.Unsafe (unsafePerformIO)
import qualified Prelude as P


{-# LINE 28 "Foreign/C/Math/Double.hsc" #-}


-- | The acos function computes the principal value of the arc cosine of x
-- in the range [0, pi]
--
acos :: Double -> Double
acos x = realToFrac (c_acos (realToFrac x))
{-# INLINE acos #-}

foreign import ccall unsafe "math.h acos"
     c_acos     :: CDouble -> CDouble

-- | The asin function computes the principal value of the arc sine of x in
-- the range [-pi/2, +pi/2].
--
asin :: Double -> Double
asin x = realToFrac (c_asin (realToFrac x))
{-# INLINE asin #-}

foreign import ccall unsafe "math.h asin"
     c_asin     :: CDouble -> CDouble

-- | The atan function computes the principal value of the arc tangent of x
-- in the range [-pi/2, +pi/2].
--
atan :: Double -> Double
atan x = realToFrac (c_atan (realToFrac x))
{-# INLINE atan #-}

foreign import ccall unsafe "math.h atan"
     c_atan     :: CDouble -> CDouble

-- | The atan2 function computes the principal value of the arc tangent of
-- y/x, using the signs of both arguments to determine the quadrant of the
-- return value.
--
atan2 :: Double -> Double -> Double
atan2 x y = realToFrac (c_atan2 (realToFrac x) (realToFrac y))
{-# INLINE atan2 #-}

foreign import ccall unsafe "math.h atan2"
     c_atan2    :: CDouble -> CDouble -> CDouble

-- | The cos function computes the cosine of x (measured in radians).
-- A large magnitude argument may yield a result with little or no significance.  For a
-- discussion of error due to roundoff, see math(3).
--
cos :: Double -> Double
cos x = realToFrac (c_cos (realToFrac x))
{-# INLINE cos #-}

foreign import ccall unsafe "math.h cos"
     c_cos      :: CDouble -> CDouble

-- | The sin function computes the sine of x (measured in radians). 
-- A large magnitude argument may yield a result with little or no
-- significance.  For a discussion of error due to roundoff, see math(3).
--
sin :: Double -> Double
sin x = realToFrac (c_sin (realToFrac x))
{-# INLINE sin #-}

foreign import ccall unsafe "math.h sin"
     c_sin      :: CDouble -> CDouble

-- | The tan function computes the tangent of x (measured in radians). 
-- A large magnitude argument may yield a result with little or no
-- significance.  For a discussion of error due to roundoff, see math(3).
--
tan :: Double -> Double
tan x = realToFrac (c_tan (realToFrac x))
{-# INLINE tan #-}

foreign import ccall unsafe "math.h tan"
     c_tan      :: CDouble -> CDouble

-- | The cosh function computes the hyperbolic cosine of x.
--
cosh :: Double -> Double
cosh x = realToFrac (c_cosh (realToFrac x))
{-# INLINE cosh #-}

foreign import ccall unsafe "math.h cosh"
     c_cosh     :: CDouble -> CDouble

-- | The sinh function computes the hyperbolic sine of x.
--
sinh :: Double -> Double
sinh x = realToFrac (c_sinh (realToFrac x))
{-# INLINE sinh #-}

foreign import ccall unsafe "math.h sinh"
     c_sinh     :: CDouble -> CDouble

-- | The tanh function computes the hyperbolic tangent of x.
--
tanh :: Double -> Double
tanh x = realToFrac (c_tanh (realToFrac x))
{-# INLINE tanh #-}

foreign import ccall unsafe "math.h tanh"
     c_tanh     :: CDouble -> CDouble

------------------------------------------------------------------------

-- | The exp() function computes the exponential value of the given argument x. 
--
exp :: Double -> Double
exp x = realToFrac (c_exp (realToFrac x))
{-# INLINE exp  #-}

foreign import ccall unsafe "math.h exp"
     c_exp      :: CDouble -> CDouble

-- | frexp convert floating-point number to fractional and integral components
-- frexp is not defined in the Haskell 98 report.
--
frexp :: Double -> (Double,Int)
frexp x = unsafePerformIO $
    alloca $ \p -> do
        d <- c_frexp (realToFrac x) p
        i <- peek p
        return (realToFrac d, fromIntegral i)

foreign import ccall unsafe "math.h frexp"
     c_frexp    :: CDouble -> Ptr CInt -> IO Double

-- | The ldexp function multiplies a floating-point number by an integral power of 2.
-- ldexp is not defined in the Haskell 98 report.
--
ldexp :: Double -> Int -> Double
ldexp x i = realToFrac (c_ldexp (realToFrac x) (fromIntegral i))
{-# INLINE ldexp #-}

foreign import ccall unsafe "math.h ldexp"
     c_ldexp    :: CDouble -> CInt -> Double

-- | The log() function computes the value of the natural logarithm of argument x.
--
log :: Double -> Double
log x = realToFrac (c_log (realToFrac x))
{-# INLINE log  #-}

foreign import ccall unsafe "math.h log"
     c_log      :: CDouble -> CDouble

-- | The log10 function computes the value of the logarithm of argument x to base 10.
-- log10 is not defined in the Haskell 98 report.
log10 :: Double -> Double
log10 x = realToFrac (c_log10 (realToFrac x))
{-# INLINE log10 #-}

foreign import ccall unsafe "math.h log10"
     c_log10    :: CDouble -> CDouble

-- | The modf function breaks the argument value into integral and fractional
-- parts, each of which has the same sign as the argument.
-- modf is not defined in the Haskell 98 report.
--
modf :: Double -> (Double,Double)
modf x = unsafePerformIO $
    alloca $ \p -> do
        d <- c_modf (realToFrac x) p
        i <- peek p
        return (realToFrac d, realToFrac i)

foreign import ccall unsafe "math.h modf"
     c_modf     :: CDouble -> Ptr CDouble -> IO CDouble

-- | The pow function computes the value of x to the exponent y.
--
pow :: Double -> Double -> Double
pow x y = realToFrac (c_pow (realToFrac x) (realToFrac y))
{-# INLINE pow #-}

foreign import ccall unsafe "math.h pow"
     c_pow      :: CDouble -> CDouble -> CDouble

-- | The sqrt function computes the non-negative square root of x.
--
sqrt :: Double -> Double
sqrt x = realToFrac (c_sqrt (realToFrac x))
{-# INLINE sqrt #-}

foreign import ccall unsafe "math.h sqrt"
     c_sqrt     :: CDouble -> CDouble

-- | The ceil function returns the smallest integral value greater than or equal to x.
--
ceil :: Double -> Double
ceil x = realToFrac (c_ceil (realToFrac x))
{-# INLINE ceil #-}

foreign import ccall unsafe "math.h ceil"
     c_ceil     :: CDouble -> CDouble

-- | The fabs function computes the absolute value of a floating-point number x.
--
fabs :: Double -> Double
fabs x = realToFrac (c_fabs (realToFrac x))
{-# INLINE fabs #-}

foreign import ccall unsafe "math.h fabs"
     c_fabs     :: CDouble -> CDouble

-- | The floor function returns the largest integral value less than or equal to x.
--
floor :: Double -> Double
floor x = realToFrac (c_floor (realToFrac x))
{-# INLINE floor #-}

foreign import ccall unsafe "math.h floor"
     c_floor    :: CDouble -> CDouble

-- | The fmod function computes the floating-point remainder of x \/ y.
--
fmod :: Double -> Double -> Double
fmod x y = realToFrac (c_fmod (realToFrac x) (realToFrac y))
{-# INLINE fmod #-}

foreign import ccall unsafe "math.h fmod"
     c_fmod     :: CDouble -> CDouble -> CDouble

-- | The round function returns the nearest integral value to x; if x lies
-- halfway between two integral values, then these functions return the integral
-- value with the larger absolute value (i.e., it rounds away from zero).
-- 
round :: Double -> Double
round x = realToFrac (c_round (realToFrac x))
{-# INLINE round #-}

foreign import ccall unsafe "math.h round"
     c_round    :: CDouble -> CDouble

-- | The fmod function computes the floating-point remainder of x \/ y.
--
trunc :: Double -> Double
trunc x = realToFrac (c_trunc (realToFrac x))
{-# INLINE trunc #-}

foreign import ccall unsafe "math.h trunc"
     c_trunc    :: CDouble -> CDouble

-- | The erf calculates the error function of x. The error function is defined as:
--
-- > erf(x) = 2/sqrt(pi)*integral from 0 to x of exp(-t*t) dt.
--
erf :: Double -> Double
erf x = realToFrac (c_erf (realToFrac x))
{-# INLINE erf #-}

foreign import ccall unsafe "math.h erf"
     c_erf      :: CDouble -> CDouble

-- | The erfc function calculates the complementary error function of x;
-- that is erfc() subtracts the result of the error function erf(x) from
-- 1.0.  This is useful, since for large x places disappear.
--
erfc :: Double -> Double
erfc x = realToFrac (c_erfc (realToFrac x))
{-# INLINE erfc #-}

foreign import ccall unsafe "math.h erfc"
     c_erfc     :: CDouble -> CDouble

-- | The gamma function.
--
gamma :: Double -> Double
gamma x = realToFrac (c_gamma (realToFrac x))
{-# INLINE gamma #-}

foreign import ccall unsafe "math.h gamma"
     c_gamma    :: CDouble -> CDouble

-- | The hypot function function computes the sqrt(x*x+y*y) in such a way that
-- underflow will not happen, and overflow occurs only if the final result
-- deserves it.  
-- 
-- > hypot(Infinity, v) = hypot(v, Infinity) = +Infinity for all v, including NaN.
--
hypot :: Double -> Double -> Double
hypot x y = realToFrac (c_hypot (realToFrac x) (realToFrac y))
{-# INLINE hypot #-}

foreign import ccall unsafe "math.h hypot"
     c_hypot    :: CDouble -> CDouble -> CDouble

-- | The isinf function returns 1 if the number n is Infinity, otherwise 0.
--
isinf :: Double -> Int
isinf x = fromIntegral (c_isinf (realToFrac x))
{-# INLINE isinf #-}

foreign import ccall unsafe "math.h isinf"
     c_isinf    :: CDouble -> CInt

-- | The isnan function returns 1 if the number n is ``not-a-number'',
-- otherwise 0.
--
isnan :: Double -> Int
isnan x = fromIntegral (c_isnan (realToFrac x))
{-# INLINE isnan #-}

foreign import ccall unsafe "math.h isnan"
     c_isnan    :: CDouble -> CInt

-- | finite returns the value 1 just when -Infinity < x < +Infinity; otherwise
-- a zero is returned (when |x| = Infinity or x is NaN.
--
finite :: Double -> Int
finite x = fromIntegral (c_finite (realToFrac x))
{-# INLINE finite #-}

foreign import ccall unsafe "math.h finite"
     c_finite    :: CDouble -> CInt

-- | The functions j0() and j1() compute the Bessel function of the
-- first kind of the order 0 and the order 1, respectively, for the real
-- value x
--
j0 :: Double -> Double
j0 x = realToFrac (c_j0 (realToFrac x))
{-# INLINE j0 #-}

foreign import ccall unsafe "math.h j0"
     c_j0    :: CDouble -> CDouble

-- | The functions j0() and j1() compute the Bessel function of the
-- first kind of the order 0 and the order 1, respectively, for the real
-- value x
--
j1 :: Double -> Double
j1 x = realToFrac (c_j1 (realToFrac x))
{-# INLINE j1 #-}

foreign import ccall unsafe "math.h j1"
     c_j1    :: CDouble -> CDouble

-- | The functions y0() and y1() compute the linearly independent Bessel
-- function of the second kind of the order 0 and the order 1,
-- respectively, for the positive integer value x (expressed as a double)
--
y0 :: Double -> Double
y0 x = realToFrac (c_y0 (realToFrac x))
{-# INLINE y0 #-}

foreign import ccall unsafe "math.h y0"
     c_y0    :: CDouble -> CDouble

-- | The functions y0() and y1() compute the linearly independent Bessel
-- function of the second kind of the order 0 and the order 1,
-- respectively, for the positive integer value x (expressed as a double)
--
y1 :: Double -> Double
y1 x = realToFrac (c_y1 (realToFrac x))
{-# INLINE y1 #-}

foreign import ccall unsafe "math.h y1"
     c_y1    :: CDouble -> CDouble

-- | yn() computes the Bessel function of the second kind for the
-- integer Bessel0 n for the positive integer value x (expressed as a
-- double).
--
yn :: Int -> Double -> Double
yn x y = realToFrac (c_yn (fromIntegral x) (realToFrac y))
{-# INLINE yn #-}

foreign import ccall unsafe "math.h yn"
     c_yn    :: CInt -> CDouble -> CDouble

-- | lgamma(x) returns ln|| (x)|.
--
lgamma :: Double -> Double
lgamma x = realToFrac (c_lgamma (realToFrac x))
{-# INLINE lgamma #-}

foreign import ccall unsafe "math.h lgamma"
     c_lgamma    :: CDouble -> CDouble


-- | The acosh function computes the inverse hyperbolic cosine of the real argument x. 
--
acosh :: Double -> Double
acosh x = realToFrac (c_acosh (realToFrac x))
{-# INLINE acosh #-}

foreign import ccall unsafe "math.h acosh"
     c_acosh    :: CDouble -> CDouble

-- | The asinh function computes the inverse hyperbolic sine of the real argument. 
--
asinh :: Double -> Double
asinh x = realToFrac (c_asinh (realToFrac x))
{-# INLINE asinh #-}

foreign import ccall unsafe "math.h asinh"
     c_asinh    :: CDouble -> CDouble

-- | The atanh function computes the inverse hyperbolic tangent of the real argument x.
--
atanh :: Double -> Double
atanh x = realToFrac (c_atanh (realToFrac x))
{-# INLINE atanh #-}

foreign import ccall unsafe "math.h atanh"
     c_atanh    :: CDouble -> CDouble

-- | The cbrt function computes the cube root of x.
--
cbrt :: Double -> Double
cbrt x = realToFrac (c_cbrt (realToFrac x))
{-# INLINE cbrt #-}

foreign import ccall unsafe "math.h cbrt"
     c_cbrt    :: CDouble -> CDouble

-- | logb x returns x's exponent n, a signed integer converted to
-- double-precision floating-point.  
-- 
-- > logb(+-Infinity) = +Infinity;
-- > logb(0) = -Infinity with a division by zero exception.
--
logb :: Double -> Double
logb x = realToFrac (c_logb (realToFrac x))
{-# INLINE logb #-}

foreign import ccall unsafe "math.h logb"
     c_logb    :: CDouble -> CDouble


-- | nextafter returns the next machine representable number from x in direction y.
--
nextafter :: Double -> Double -> Double
nextafter x y = realToFrac (c_nextafter (realToFrac x) (realToFrac y))
{-# INLINE nextafter #-}

foreign import ccall unsafe "math.h nextafter"
     c_nextafter    :: CDouble -> CDouble -> CDouble

-- | remainder returns the remainder r := x - n*y where n is the integer
-- nearest the exact value of x/y; moreover if |n - x/y| = 1/2 then n is even.
-- Consequently, the remainder is computed exactly and |r| <= |y|/2.  But
-- remainder(x, 0) and remainder(Infinity, 0) are invalid operations that produce
-- a NaN.  --
remainder :: Double -> Double -> Double
remainder x y = realToFrac (c_remainder (realToFrac x) (realToFrac y))
{-# INLINE remainder #-}

foreign import ccall unsafe "math.h remainder"
     c_remainder    :: CDouble -> CDouble -> CDouble

-- | scalb(x, n) returns x*(2**n) computed by exponent manipulation.
scalb :: Double -> Double -> Double
scalb x y = realToFrac (c_scalb (realToFrac x) (realToFrac y))
{-# INLINE scalb #-}

foreign import ccall unsafe "math.h scalb"
     c_scalb    :: CDouble -> CDouble -> CDouble

-- | significand(x) returns sig, where x := sig * 2**n with 1 <= sig < 2.
-- significand(x) is not defined when x is 0, +-Infinity, or NaN.
--
significand :: Double -> Double
significand x = realToFrac (c_significand (realToFrac x))
{-# INLINE significand #-}

foreign import ccall unsafe "math.h significand"
     c_significand    :: CDouble -> CDouble


-- |  copysign x y returns x with its sign changed to y's.
copysign :: Double -> Double -> Double
copysign x y = realToFrac (c_copysign (realToFrac x) (realToFrac y))
{-# INLINE copysign #-}

foreign import ccall unsafe "math.h copysign"
     c_copysign    :: CDouble -> CDouble -> CDouble

-- | ilogb() returns x's exponent n, in integer format.
--    ilogb(+-Infinity) re- turns INT_MAX and ilogb(0) returns INT_MIN.
--
ilogb :: Double -> Int
ilogb x = fromIntegral (c_ilogb (realToFrac x))
{-# INLINE ilogb #-}

foreign import ccall unsafe "math.h ilogb"
     c_ilogb    :: CDouble -> CInt

-- | The rint() function returns the integral value (represented as a
-- double precision number) nearest to x according to the prevailing
-- rounding mode.
--
rint :: Double -> Double
rint x = realToFrac (c_rint (realToFrac x))
{-# INLINE rint #-}

foreign import ccall unsafe "math.h rint"
     c_rint    :: CDouble -> CDouble


-- | Determine bitwise equality.
--
eq :: Double -> Double -> Bool
eq = (==) `on` doubleWord64

eqf :: Float -> Float -> Bool
eqf = (==) `on` floatWord32

-- | Maximum finite value.
--
-- >>> shift 1 maxNorm
-- Infinity
-- 
maxNorm :: Double
maxNorm = shift (-1) maximal 

maxNormf :: Float
maxNormf = shiftf (-1) maximal 

-- | Minimum normalized value.
--
-- >>> shift (-1) minNorm
-- 0
-- 
minNorm :: Double
minNorm = word64Double 0x0080000000000000

minNormf :: Float
minNormf = word32Float 0x00800000

-- | Maximum representable odd integer. 
--
-- @ maxOdd = 2**53 - 1@
--
maxOdd :: Double
maxOdd = 9.007199254740991e15

-- | Maximum representable odd integer. 
--
-- @ maxOddf = 2**24 - 1@
--
maxOddf :: Float
maxOddf = 1.6777215e7

-- | Minimum positive double value.
--
-- >>> shift (-1) minSub
-- 0.0
-- 
minSub :: Double
minSub = shift 1 0

-- | Minimum positive float value.
--
-- >>> minSubf
-- 1.0e-45
--
minSubf :: Float
minSubf = shiftf 1 0

-- | Difference between 1 and the smallest representable value greater than 1.
epsilon :: Double
epsilon = shift 1 1 - 1

epsilonf :: Float
epsilonf = shiftf 1 1 - 1

-- | Split a 'Double' symmetrically along the sign bit.
--
-- >>> split 0
-- Right 0.0
-- >>> split (shift (-1) 0)
-- Left (-0.0)
-- 
split :: Double -> Either Double Double
split x = case signBit x of
  True -> Left x
  _    -> Right x

splitf :: Float -> Either Float Float
splitf x = case signBitf x of
  True -> Left x
  _    -> Right x


-- | Shift by /Int64/ units of least precision.
--
shift :: Int64 -> Double -> Double
shift n = int64Double . (+ n) . doubleInt64

shiftf :: Int32 -> Float -> Float
shiftf n = int32Float . (+ n) . floatInt32

-- | Compute signed distance in units of least precision.
--
-- @ 'ulps' x ('shift' ('abs' n) x) '==' ('True', 'abs' n) @
--
ulps :: Double -> Double -> (Bool, Word64)
ulps x y = o
  where  x' = doubleInt64 x
         y' = doubleInt64 y
         o  | x' >= y' = (False, fromIntegral . abs $ x' - y')
            | otherwise = (True, fromIntegral . abs $ y' - x')

ulpsf :: Float -> Float -> (Bool, Word32)
ulpsf x y = o
  where  x' = floatInt32 x
         y' = floatInt32 y
         o  | x' >= y' = (False, fromIntegral . abs $ x' - y')
            | otherwise = (True, fromIntegral . abs $ y' - x')

-- | Compute distance in units of least precision.
--
-- @ 'ulps'' x ('shift' n x) '==' 'abs' n @
--
ulps' :: Double -> Double -> Word64
ulps' x y = snd $ ulps x y

ulpsf' :: Float -> Float -> Word32
ulpsf' x y = snd $ ulpsf x y

-- | Compare two values for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
-- 
within :: Word64 -> Double -> Double -> Bool
within tol a b = ulps' a b <= tol

withinf :: Word32 -> Float -> Float -> Bool
withinf tol a b = ulpsf' a b <= tol



{-
ulpDelta :: Float -> Float -> Int
ulpDelta x y = if lesser then d' else (-1) * d'
  where (lesser, d) = ulps x y
        d' = fromIntegral d

ulpDelta' :: Float -> Float -> Int32
ulpDelta' x y = if lesser then d' else (-1) * d'
  where (lesser, d) = ulps x y
        d' = fromIntegral d
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
    x <= y | ulp32Nan x && ulp32Nan y = True
           | ulp32Nan x || ulp32Nan y = False
           | otherwise                = on (<=) unUlp32 x y

instance Minimal Ulp32 where
    minimal = Ulp32 $ -2139095041

instance Maximal Ulp32 where
    maximal = Ulp32 $ 2139095040

f32u32 :: Conn Float Ulp32
f32u32 = Conn (Ulp32 . floatInt32) (int32Float . unUlp32)

u32f32 :: Conn Ulp32 Float
u32f32 = Conn (int32Float . unUlp32) (Ulp32 . floatInt32)

-- fromIntegral (maxBound :: Ulp32) + 1 , image of aNan


--newtype Ulp a = Ulp { unUlp :: a }
-- instance 
{- correct but maybe replace w/ Graded / Yoneda / Indexed etc
u32w64 :: Conn Ulp32 (Nan Word64)
u32w64 = Conn f g where
  conn = i32w32 >>> w32w64

  offset  = 2139095041 :: Word64
  offset' = 2139095041 :: Int32

  f x@(Ulp32 y) | ulp32Nan x = Nan
                | neg y = Def $ fromIntegral (y + offset')
                | otherwise = Def $ (fromIntegral y) + offset
               where fromIntegral = connl conn

  g x = case x of
          Nan -> Ulp32 offset'
          Def y | y < offset -> Ulp32 $ (fromIntegral y) P.- offset'
                | otherwise  -> Ulp32 $ fromIntegral ((min 4278190081 y) P.- offset)
               where fromIntegral = connr conn
-}


-- internal


signBit :: Double -> Bool
signBit x = if x =~ 0/0 then False else msbMask x /= 0

evenBit :: Double -> Bool
evenBit x = lsbMask x == 0

lsbMask :: Double -> Word64
lsbMask x = 0x0000000000000001 .&. doubleWord64 x

msbMask :: Double -> Word64
msbMask x = 0x8000000000000000 .&. doubleWord64 x

-- loatWord64 maximal == exponent maximal
--expMask :: Double -> Word64
--expMask x = 0x7F80000000000000 .&. doubleWord64 x

-- chk  =  >= 0 ==>  == word64Double $ exponent  + signiicand 
sigMask :: Double -> Word64
sigMask x = 0x007FFFFFFFFFFFFF .&. doubleWord64 x



signBitf :: Float -> Bool
signBitf x = if x =~ 0/0 then False else msbMaskf x /= 0

evenBitf :: Float -> Bool
evenBitf x = lsbMaskf x == 0

lsbMaskf :: Float -> Word32
lsbMaskf x = 0x00000001 .&. floatWord32 x

msbMaskf :: Float -> Word32
msbMaskf x = 0x80000000 .&. floatWord32 x

-- floatWord32 maximal == exponent maximal
expMaskf :: Float -> Word32
expMaskf x = 0x7f800000 .&. floatWord32 x

-- chk f = f >= 0 ==> f == word32Float $ exponent f + significand f
sigMaskf :: Float -> Word32
sigMaskf x = 0x007FFFFF .&. floatWord32 x



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

