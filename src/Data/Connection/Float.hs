module Data.Connection.Float where
{- 
  -- * Float
  , f32i32
  , i32f32
  , f32i32'
  -- * Double
  , f64i64
  , i64f64
) where
-}

import Control.Category ((>>>))
import Data.Bits ((.&.))
import Data.Int
import Data.Word
import Data.Float
import Data.Prd
import Data.Prd.Nan
import Data.Function (on)
import Data.Connection
import Data.Connection.Int
import Data.Connection.Word
import GHC.Num (subtract)
import qualified Data.Bits as B
import qualified GHC.Float as F
import qualified GHC.Float.RealFracMethods as R
import Data.Semiring
import Data.Semilattice
import Data.Semilattice.Bounded
import Prelude as P hiding (Num(..), (^), Bounded)
import qualified Control.Category as C

import Data.Ratio

import GHC.Real hiding ((^))


class Prd a => ConnFloat a where
  connFloat :: Conn Float a

instance ConnFloat Float where
  connFloat = C.id

instance ConnFloat (Nan Int32) where
  connFloat = f32i32

instance ConnFloat (Nan Ordering) where
  connFloat = tripl fldord

instance ConnFloat Ulp32 where
  connFloat = f32u32

--instance ConnFloat (Nan Word8) where
--  connFloat = tripl f32w08


class Prd a => ConnDouble a where
  connDouble :: Conn Double a

instance ConnDouble Double where
  connDouble = C.id

--instance ConnDouble Ulp64 where
--  connDouble = f64u64

instance ConnDouble (Nan Int64) where
  connDouble = f64i64

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


abs' x = if x == minimal then abs (x+one) else abs x

-- exact int embedding up to the largest representable int.
f32i32 :: Conn Float (Nan Int32)
f32i32 = Conn (liftNan f) (nan' g) where
  f x | abs x <= 2**24-1 = P.ceiling x
      | otherwise = if x >= 0 then 2^24 else minimal

  g i | abs' i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 1/0 else -2**24

-- exact int embedding up to the largest representable int.
i32f32 :: Conn (Nan Int32) Float
i32f32 = Conn (nan' g) (liftNan f) where
  f x | abs x <= 2**24-1 = P.floor x
      | otherwise = if x >= 0 then maximal else -2^24

  g i | abs i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**24 else -1/0

f32i32' :: Trip Float (Extended Int32)
f32i32' = Trip (liftNan f) (nan' $ bounded minimal g maximal) (liftNan h) where
  f x | abs x <= 2**24-1 = Fin $ P.ceiling x
      | otherwise = if x >= 0 then Fin (2^24) else Bot

  g i | abs i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**24 else -2**24

  h x | abs x <= 2**24-1 = Fin $ P.floor x
      | otherwise = if x >= 0 then Top else Fin (-2^24)

{-
--TODO check these 4 probably buggy
f32ixx :: Trip Float (Nan (Bounded Int))
f32ixx = Trip
  (liftNan f)
  (nan' g)
  (liftNan h)
  where
    f x | not (finite x) && signBitf x = minimal
        | not (finite x) && not (signBitf x) = maximal
        | otherwise = R.ceilingFloatInt x

    g = F.int2Float

    h x | not (finite x) && signBitf x = minimal
        | not (finite x) && not (signBitf x) = maximal
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

f64i64 :: Conn Double (Nan Int64)
f64i64 = Conn (liftNan f) (nan' g) where
  f x | abs x <~ 2**53-1 = P.ceiling x
      | otherwise = if x >~ 0 then 2^53 else minimal

  g i | abs' i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**53
  
i64f64 :: Conn (Nan Int64) Double
i64f64 = Conn (nan' g) (liftNan f) where
  f x | abs x <~ 2**53-1 = P.floor x
      | otherwise = if x >~ 0 then maximal else -2^53

  g i | abs i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 2**53 else -1/0
