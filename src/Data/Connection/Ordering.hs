{-# LANGUAGE Safe              #-}
module Data.Connection.Ordering (
    ordbin
  , binord
  , i08ord
  , i16ord
  , i32ord 
  , i64ord
  , w08ord
  , w16ord
  , w32ord 
  , w64ord
  , ratord
  , f32ord
  , f64ord
) where

import safe Data.Int
import safe Data.Word
import safe Data.Connection.Type
import safe Data.Lattice
import safe Data.Order
import safe GHC.Real (Ratio)
import safe Prelude hiding (Ord(..), Bounded, until)



i08ord :: Trip Int8 Ordering
i08ord = triple

i16ord :: Trip Int16 Ordering
i16ord = triple

i32ord :: Trip Int32 Ordering
i32ord = triple

i64ord :: Trip Int64 Ordering
i64ord = triple

ixxord :: Trip Int Ordering
ixxord = triple

w08ord :: Trip Word8 Ordering
w08ord = triple

w16ord :: Trip Word16 Ordering
w16ord = triple

w32ord :: Trip Word32 Ordering
w32ord = triple

w64ord :: Trip Word64 Ordering
w64ord = triple

wxxord :: Trip Word Ordering
wxxord = triple

ratord :: Trip Rational Ordering
ratord = triple

f32ord :: Trip Float Ordering
f32ord = triple

f64ord :: Trip Double Ordering
f64ord = triple

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------



triple :: (Bounded a, Num a) => Trip a Ordering
triple = Trip f g h where
  g GT = top
  g LT = bottom
  g EQ = 0
  
  f x | x ~~ bottom  = LT
      | x <~ 0  = EQ
      | otherwise  = GT

  h x | x ~~ top  = GT
      | x >~ 0  = EQ
      | otherwise  = LT

{-
ratord :: Conn (Ratio Integer) (Lowered Ordering)
ratord = fldord

ordrat :: Conn (Lifted Ordering) (Ratio Integer)
ordrat = ordfld 

f32ord :: Conn Float (Lowered Ordering)
f32ord = fldord

ordf32 :: Conn (Lifted Ordering) Float
ordf32 = ordfld

f64ord :: Conn Double (Lowered Ordering)
f64ord = fldord

ordf64 :: Conn (Lifted Ordering) Double
ordf64 = ordfld

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
-}
