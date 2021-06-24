{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Connection.Int (
    -- * Int16
    w08i16,
    i08i16,

    -- * Int32
    w08i32,
    w16i32,
    i08i32,
    i16i32,

    -- * Int64
    w08i64,
    w16i64,
    w32i64,
    i08i64,
    i16i64,
    i32i64,
    ixxi64,

    -- * Int
    w08ixx,
    w16ixx,
    w32ixx,
    i08ixx,
    i16ixx,
    i32ixx,
    i64ixx,

    -- * Integer
    w08int,
    w16int,
    w32int,
    w64int,
    wxxint,
    i08int,
    i16int,
    i32int,
    i64int,
    ixxint,
) where

import safe Data.Connection.Cast
import safe Data.Int
import safe Data.Word

-- Int16
w08i16 :: Cast k (Extended Word8) Int16
w08i16 = conn

i08i16 :: Cast k (Extended Int8) Int16
i08i16 = conn

-- Int32
w08i32 :: Cast k (Extended Word8) Int32
w08i32 = conn

w16i32 :: Cast k (Extended Word16) Int32
w16i32 = conn

i08i32 :: Cast k (Extended Int8) Int32
i08i32 = conn

i16i32 :: Cast k (Extended Int16) Int32
i16i32 = conn

-- Int64
w08i64 :: Cast k (Extended Word8) Int64
w08i64 = conn

w16i64 :: Cast k (Extended Word16) Int64
w16i64 = conn

w32i64 :: Cast k (Extended Word32) Int64
w32i64 = conn

i08i64 :: Cast k (Extended Int8) Int64
i08i64 = conn

i16i64 :: Cast k (Extended Int16) Int64
i16i64 = conn

i32i64 :: Cast k (Extended Int32) Int64
i32i64 = conn

-- | /Caution/: This assumes that 'Int' on your system is 64 bits.
ixxi64 :: Cast k Int Int64
ixxi64 = Cast fromIntegral fromIntegral fromIntegral

-- Int
w08ixx :: Cast k (Extended Word8) Int
w08ixx = conn

w16ixx :: Cast k (Extended Word16) Int
w16ixx = conn

w32ixx :: Cast k (Extended Word32) Int
w32ixx = conn

i08ixx :: Cast k (Extended Int8) Int
i08ixx = conn

i16ixx :: Cast k (Extended Int16) Int
i16ixx = conn

i32ixx :: Cast k (Extended Int32) Int
i32ixx = conn

-- | /Caution/: This assumes that 'Int' on your system is 64 bits.
i64ixx :: Cast k Int64 Int
i64ixx = Cast fromIntegral fromIntegral fromIntegral

-- Integer
w08int :: Cast 'L (Extended Word8) (Maybe Integer)
w08int = extint

w16int :: Cast 'L (Extended Word16) (Maybe Integer)
w16int = extint

w32int :: Cast 'L (Extended Word32) (Maybe Integer)
w32int = extint

w64int :: Cast 'L (Extended Word64) (Maybe Integer)
w64int = extint

wxxint :: Cast 'L (Extended Word) (Maybe Integer)
wxxint = extint

i08int :: Cast 'L (Extended Int8) (Maybe Integer)
i08int = extint

i16int :: Cast 'L (Extended Int16) (Maybe Integer)
i16int = extint

i32int :: Cast 'L (Extended Int32) (Maybe Integer)
i32int = extint

i64int :: Cast 'L (Extended Int64) (Maybe Integer)
i64int = extint

ixxint :: Cast 'L (Extended Int) (Maybe Integer)
ixxint = extint

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

{-# INLINE conn #-}
conn :: forall a b k. (Bounded a, Bounded b, Integral a, Integral b) => Cast k (Extended a) b
conn = Cast f g h 
  where
    below = fromIntegral @a minBound - 1
    above = fromIntegral @a maxBound + 1
    
    f = extended minBound above $ fromIntegral
    
    g x | x <= below = NegInf
        | x >= above = PosInf
        | otherwise = Finite $ fromIntegral x

    h = extended below maxBound $ fromIntegral

{-# INLINE extint #-}
extint :: forall a. (Bounded a, Integral a) => Cast 'L (Extended a) (Maybe Integer)
extint = CastL f $ maybe NegInf g
  where
    below = fromIntegral @a minBound - 1
    above = fromIntegral @a maxBound + 1
    
    f = extended Nothing (Just above) (Just . fromIntegral)
    
    g x | x <= below = NegInf
        | x >= above = PosInf
        | otherwise = Finite $ fromIntegral x

