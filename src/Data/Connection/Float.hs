{-# Language ConstraintKinds #-}
module Data.Connection.Float (
    fltord
  -- * Float
  , f32i08
  , f32i16
  , f32i32
  , i32f32
  -- * Double
  , f64f32
  , f64i08
  , f64i16
  , f64i32
  , f64i64
  , i64f64
) where

import Data.Bool
import Data.Connection.Conn
import Data.Connection.Trip
import Data.Float
import Data.Int
import Data.Prd
import Data.Prd.Nan
import Data.Prd.Top
import GHC.Float (float2Double,double2Float)
import Prelude as P hiding (Ord(..), Bounded, until)

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


-- | All 'Int08' values are exactly representable in a 'Float'.
f32i08 :: Trip Float (Extended Int8)
f32i08 = Trip (liftNan f) (nanf g) (liftNan h) where
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
f32i16 = Trip (liftNan f) (nanf g) (liftNan h) where
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
f32i32 = Conn (liftNan f) (nanf g) where
  f x | abs x <= 2**24-1 = P.ceiling x
      | otherwise = if x >= 0 then 2^24 else minimal

  g i | abs' i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 1/0 else -2**24

-- | Exact embedding up to the largest representable 'Int32'.
i32f32 :: Conn (Nan Int32) Float
i32f32 = Conn (nanf g) (liftNan f) where
  f x | abs x <= 2**24-1 = P.floor x
      | otherwise = if x >= 0 then maximal else -2^24

  g i | abs i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**24 else -1/0

---------------------------------------------------------------------
-- Double
---------------------------------------------------------------------

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
f64i08 = Trip (liftNan f) (nanf g) (liftNan h) where
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
f64i16 = Trip (liftNan f) (nanf g) (liftNan h) where
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
f64i32 = Trip (liftNan f) (nanf g) (liftNan h) where
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
f64i64 = Conn (liftNan f) (nanf g) where
  f x | abs x <= 2**53-1 = P.ceiling x
      | otherwise = if x >= 0 then 2^53 else minimal

  g i | abs' i <= 2^53-1 = fromIntegral i
      | otherwise = if i >= 0 then 1/0 else -2**53
  
-- | Exact embedding up to the largest representable 'Int64'.
i64f64 :: Conn (Nan Int64) Double
i64f64 = Conn (nanf g) (liftNan f) where
  f x | abs x <= 2**53-1 = P.floor x
      | otherwise = if x >= 0 then maximal else -2^53

  g i | abs i <= 2^53-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**53 else -1/0


{- 
f32u32 :: Conn Float Ulp32
f32u32 = Conn (Ulp32 . floatInt32) (int32Float . unUlp32)

u32f32 :: Conn Ulp32 Float
u32f32 = Conn (int32Float . unUlp32) (Ulp32 . floatInt32)

-- correct but maybe replace w/ Graded / Yoneda / Indexed etc
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

{- 
f32w08 :: Trip Float (Nan Word8)
f32w08 = Trip (liftNan f) (nan (0/0) g) (liftNan h) where
  h x = if x > 0 then 0 else connr w08w32 $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min 254 (h x)



floatDouble :: Float -> Double
floatDouble = int64Double . (* 2^ 31) . fromIntegral . floatInt32

foo :: Float -> Double
foo x = int64Double $ e' + s' where
  s' = fromIntegral s * 2^32
  e' = fromIntegral e * 2^35
  (e,s) = signed32 . expMaskf &&& signed32 . sigMaskf $ x

bar x = (e,s) where (e,s) = signed32 . expMaskf &&& signed32 . sigMaskf $ x

f64f32 :: Trip Double Float
f64f32 = Trip f g h where
  f = (fromIntegral . round) :: Double -> Float
  g = floatDouble
  h :: Double -> Float
  h x | abs x <= 1.0e-45 = case sign x of
                             Nothing -> 0/0
                             Just LT -> -minSubf
                             Just EQ -> 0
                             Just GT -> minSubf
      | otherwise = (fromIntegral . round) x
-}

abs' :: Ord a => Minimal a => Num a => a -> a
abs' x = if x =~ minimal then abs (x+1) else abs x
