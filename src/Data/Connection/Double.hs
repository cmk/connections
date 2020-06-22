{-# Language ConstraintKinds #-}
{-# Language Safe            #-}
{-# Language RankNTypes      #-}
module Data.Connection.Double (
    f64f32
  , f64i08
  , f64i16
  , f64i32
) where

import safe Data.Bool
import safe Data.Connection.Conn
import safe Data.Lattice
import safe Data.Int
import safe Data.Order
import safe Data.Order.Extended
import safe GHC.Float as F
import safe Prelude as P hiding (Ord(..), Bounded, until)
import safe qualified Data.Order.Float as F32

---------------------------------------------------------------------
-- Connections
---------------------------------------------------------------------

-- | All 'Int08' values are exactly representable in a 'Double'.
f64i08 :: Conn k Double (Extended Int8)
f64i08 = triple 127

-- | All 'Int08' values are exactly representable in a 'Double'.
f64i16 :: Conn k Double (Extended Int16)
f64i16 = triple 32767

-- | All 'Int32' values are exactly representable in a 'Double'.
f64i32 :: Conn k Double (Extended Int32)
f64i32 = triple 2147483647

{-

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

-}


f64f32 :: Conn k Double Float
f64f32 = Conn f1 g f2 where
  f1 x = let est = F.double2Float x in
          if g est >~ x
          then est
          else F32.upper32 est g x

  f2 x = let est = F.double2Float x in
          if g est <~ x
          then est
          else F32.lower32 est g x

  g = F.float2Double


{-
  ascendf z g1 y = until (\x -> g1 x >~ y) (<~) (F32.shift 1) z

  descendf z f1 x = until (\y -> f1 y <~ x) (>~) (F32.shift (-1)) z
-}

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

triple :: (Bounded a, Integral a) => Double -> Conn k Double (Extended a)
triple high = Conn f1 g f2 where
  f1 = liftExtended (~~ -1/0) (\x -> x ~~ 0/0 || x > high) $ \x -> if x < low then bottom else P.ceiling x

  f2 = liftExtended (\x -> x ~~ 0/0 || x < low) (~~ 1/0) $ \x -> if x > high then top else P.floor x

  g = extended bottom top P.fromIntegral
 
  low = -1 - high


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
f32w08 :: Conn k Float (Maybe Word8)
f32w08 = Conn (nanf f) (nan (0/0) g) (nanf h) where
  h x = if x > 0 then 0 else connr w08wf $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min 254 (h x)

abs' :: (Eq a, Bounded a, Num a) => a -> a
abs' x = if x ~~ bottom then abs (x+1) else abs x

nanf :: (Eq a, Lattice a) => Floating a => (a -> b) -> a -> Maybe b
nanf f x | x ~~ 0/0 = Nothing
         | otherwise = Just (f x)

nan :: Fractional b => (a -> b) -> Maybe a -> b
nan = maybe (0/0)

extf f x | x ~~ 0/0 = Bottom -- ?
         | otherwise = Extended (f x)

-- Bit-for-bit conversion.
word64Double :: Word64 -> Double
word64Double = F.castWord64ToDouble

-- TODO force to pos representation?
-- Bit-for-bit conversion.
doubleWord64 :: Double -> Word64
doubleWord64 = (+0) . F.castDoubleToWord64

-}



