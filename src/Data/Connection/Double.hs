{-# Language ConstraintKinds #-}
{-# Language Safe            #-}
{-# Language RankNTypes      #-}
module Data.Connection.Double (
    f64f32
  , f64i08
  , f64i16
  , f64i32
  , min64
  , max64
  , ulp
  , covers
  , shift
  , within
  , epsilon
  , until
) where


--import safe Data.Universe.Class
import safe Data.Bool
import safe Data.Connection.Conn
import safe Data.Int
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Order.Syntax hiding (min, max)
import safe Data.Word
import safe GHC.Float as F
import safe Prelude hiding (Eq(..), Ord(..), until)
import safe qualified Data.Connection.Float as F32
import safe qualified Prelude as P

---------------------------------------------------------------------
-- Connections
---------------------------------------------------------------------

f64f32 :: Conn k Double Float
f64f32 = Conn f1 g f2 where
  f1 x = let est = F.double2Float x in
          if g est >~ x
          then est
          else ascend32 est g x

  f2 x = let est = F.double2Float x in
          if g est <~ x
          then est
          else descend32 est g x

  g = F.float2Double

  ascend32 z g1 y = until (\x -> g1 x >~ y) (<~) (F32.shift 1) z

  descend32 z h1 x = until (\y -> h1 y <~ x) (>~) (F32.shift (-1)) z

-- | All 'Data.Int.Int08' values are exactly representable in a 'Double'.
f64i08 :: Conn k Double (Extended Int8)
f64i08 = triple 127

-- | All 'Data.Int.Int16' values are exactly representable in a 'Double'.
f64i16 :: Conn k Double (Extended Int16)
f64i16 = triple 32767

-- | All 'Data.Int.Int32' values are exactly representable in a 'Double'.
f64i32 :: Conn k Double (Extended Int32)
f64i32 = triple 2147483647


---------------------------------------------------------------------
-- Double
---------------------------------------------------------------------

-- | A /NaN/-handling min function.
--
-- > min64 x NaN = x
-- > min64 NaN y = y
--
min64 :: Double -> Double -> Double
min64 x y = case (isNaN x, isNaN y) of
  (False, False) -> if x <= y then x else y
  (False, True) -> x
  (True, False) -> y
  (True, True)  -> x

-- | A /NaN/-handling max function.
--
-- > max64 x NaN = x
-- > max64 NaN y = y
--
max64 :: Double -> Double -> Double
max64 x y = case (isNaN x, isNaN y) of
  (False, False) -> if x >= y then x else y
  (False, True) -> x
  (True, False) -> y
  (True, True)  -> x

-- | Covering relation on the /N5/ lattice of doubles.
--
-- < https://en.wikipedia.org/wiki/Covering_relation >
--
-- >>> covers 1 (shift 1 1)
-- True
-- >>> covers 1 (shift 2 1)
-- False
--
covers :: Double -> Double -> Bool
covers x y = x ~~ shift (-1) y

-- | Compute the signed distance between two doubles in units of least precision.
--
-- >>> ulp 1.0 (shift 1 1.0)
-- Just (LT,1)
-- >>> ulp (0.0/0.0) 1.0
-- Nothing
--
ulp :: Double -> Double -> Maybe (Ordering, Word64)
ulp x y = fmap f $ pcompare x y
  where  x' = doubleInt64 x
         y' = doubleInt64 y
         f LT = (LT, fromIntegral . abs $ y' - x')
         f EQ = (EQ, 0)
         f GT = (GT, fromIntegral . abs $ x' - y')

-- | Shift by /n/ units of least precision.
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
shift :: Int64 -> Double -> Double
shift n x | x ~~ 0/0 = x
          | otherwise = int64Double . clamp64 . (+ n) . doubleInt64 $ x

-- | Compare two double-precision floats for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
-- 
within :: Word64 -> Double -> Double -> Bool
within tol x y = maybe False ((<= tol) . snd) $ ulp x y

-- | Difference between 1 and the smallest representable value greater than 1.
--
-- > epsilon = shift 1 1 - 1
--
-- >>> epsilon
-- 2.220446049250313e-16
--
epsilon :: Double
epsilon = shift 1 1.0 - 1.0

{-

-- | Minimal positive value.
--
-- >>> minimal64
-- 5.0e-324
-- >>> shift (-1) minimal64
-- 0
--
minimal64 :: Double
minimal64 = shift 1 0.0

-- | Maximum finite value.
--
-- >>> maximal64
-- 1.7976931348623157e308
-- >>> shift 1 maximal64
-- Infinity
-- >>> shift (-1) $ negate maximal64
-- -Infinity
-- 
maximal64 :: Double
maximal64 = shift (-1) maxBound 
-}
--------------------------------------------------------------------------------
-- Orphans
---------------------------------------------------------------------
{-
instance Universe Double where
  universe = 0/0 : indexFromTo (minBound ... maxBound)

instance Finite Double
-}
---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

{-# INLINE until #-}
until :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
until pre rel f seed = go seed
  where go x | x' `rel` x = x
             | pre x = x
             | otherwise = go x'
          where x' = f x




-- Non-monotonic function 
signed64 :: Word64 -> Int64
signed64 x | x < 0x8000000000000000 = fromIntegral x
           | otherwise      = fromIntegral (maxBound P.- (x P.- 0x8000000000000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned64 :: Int64 -> Word64
unsigned64 x | x >~ 0  = fromIntegral x
             | otherwise = 0x8000000000000000 + (maxBound P.- (fromIntegral x))

-- Clamp between the int representations of -1/0 and 1/0 
clamp64 :: Int64 -> Int64
clamp64 = P.max (-9218868437227405313) . P.min 9218868437227405312 

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

{-

-- | Exact embedding up to the largest representable 'Int64'.
f64i64 :: Conn Double (Maybe Int64)
f64i64 = Conn (nanf f) (nan g) where
  f x | abs x <~ 2**53-1 = P.ceiling x
      | otherwise = if x >~ 0 then 2^53 else minBound

  g i | abs' i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**53
  
-- | Exact embedding up to the largest representable 'Int64'.
i64f64 :: Conn (Maybe Int64) Double
i64f64 = Conn (nan g) (nanf f) where
  f x | abs x <~ 2**53-1 = P.floor x
      | otherwise = if x >~ 0 then maxBound else -2^53

  g i | abs i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 2**53 else -1/0

-- | Exact embedding up to the largest representable 'Int64'.
f64ixx :: Conn Double (Maybe Int)
f64ixx = Conn (nanf f) (nan g) where
  f x | abs x <~ 2**53-1 = P.ceiling x
      | otherwise = if x >~ 0 then 2^53 else minBound

  g i | abs' i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**53
  
-- | Exact embedding up to the largest representable 'Int64'.
ixxf64 :: Conn (Maybe Int) Double
ixxf64 = Conn (nan g) (nanf f) where
  f x | abs x <~ 2**53-1 = P.floor x
      | otherwise = if x >~ 0 then maxBound else -2^53

  g i | abs i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 2**53 else -1/0

-}


{-
-- |
--
-- @'lower64' x@ is the least element /y/ in the descending
-- chain such that @not $ f y '<~' x@.
--
lower :: Preorder a => Double -> (Double -> a) -> a -> Double
lower z f x = until (\y -> f y <~ x) (>~) (shift $ -1) z

-- |
--
-- @'upper64' y@ is the greatest element /x/ in the ascending
-- chain such that @g x '<~' y@.
--
upper :: Preorder a => Double -> (Double -> a) -> a -> Double
upper z g y = until (\x -> g x >~ y) (<~) (shift 1) z

-- |
--
-- @'lower' x@ is the least element /y/ in the descending
-- chain such that @not $ f y '<~' x@.
--
lower :: Preorder a => Float -> (Float -> a) -> a -> Float
lower z f x = until (\y -> f y <~ x) (>~) (F32.shift $ -1) z

-- |
--
-- @'upper' y@ is the greatest element /x/ in the ascending
-- chain such that @not $ g x '>~' y@.
--
upper :: Preorder a => Float -> (Float -> a) -> a -> Float
upper z g y = until (\x -> g x >~ y) (<~) (F32.shift 1) z
-}


---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

triple :: (Bounded a, Integral a) => Double -> Conn k Double (Extended a)
triple high = Conn f1 g f2 where
  f1 = liftExtended (~~ -1/0) (\x -> x ~~ 0/0 || x > high) $ \x -> if x < low then minBound else P.ceiling x

  f2 = liftExtended (\x -> x ~~ 0/0 || x < low) (~~ 1/0) $ \x -> if x > high then maxBound else P.floor x

  g = extended (-1/0) (1/0) P.fromIntegral
 
  low = -1 - high
