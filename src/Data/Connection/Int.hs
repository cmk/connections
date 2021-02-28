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
    natint,
    i08int,
    i16int,
    i32int,
    i64int,
    ixxint,
) where

import safe Control.Applicative
import safe Control.Monad
import safe Data.Connection.Conn
import safe Data.Int
import safe Data.Word
import safe Numeric.Natural
import safe Prelude

-- Int16
w08i16 :: Conn 'L Word8 (Maybe Int16)
w08i16 = signed

i08i16 :: Conn 'L Int8 (Maybe Int16)
i08i16 = signed

-- Int32
w08i32 :: Conn 'L Word8 (Maybe Int32)
w08i32 = signed

w16i32 :: Conn 'L Word16 (Maybe Int32)
w16i32 = signed

i08i32 :: Conn 'L Int8 (Maybe Int32)
i08i32 = signed

i16i32 :: Conn 'L Int16 (Maybe Int32)
i16i32 = signed

-- Int64
w08i64 :: Conn 'L Word8 (Maybe Int64)
w08i64 = signed

w16i64 :: Conn 'L Word16 (Maybe Int64)
w16i64 = signed

w32i64 :: Conn 'L Word32 (Maybe Int64)
w32i64 = signed

i08i64 :: Conn 'L Int8 (Maybe Int64)
i08i64 = signed

i16i64 :: Conn 'L Int16 (Maybe Int64)
i16i64 = signed

i32i64 :: Conn 'L Int32 (Maybe Int64)
i32i64 = signed

-- Int
w08ixx :: Conn 'L Word8 (Maybe Int)
w08ixx = signed

w16ixx :: Conn 'L Word16 (Maybe Int)
w16ixx = signed

w32ixx :: Conn 'L Word32 (Maybe Int)
w32ixx = signed

i08ixx :: Conn 'L Int8 (Maybe Int)
i08ixx = signed

i16ixx :: Conn 'L Int16 (Maybe Int)
i16ixx = signed

i32ixx :: Conn 'L Int32 (Maybe Int)
i32ixx = signed

-- | /Caution/: This assumes that 'Int' on your system is 64 bits.
i64ixx :: Conn k Int64 Int
i64ixx = Conn fromIntegral fromIntegral fromIntegral

-- Integer
w08int :: Conn 'L Word8 (Maybe Integer)
w08int = signed

w16int :: Conn 'L Word16 (Maybe Integer)
w16int = signed

w32int :: Conn 'L Word32 (Maybe Integer)
w32int = signed

w64int :: Conn 'L Word64 (Maybe Integer)
w64int = signed

wxxint :: Conn 'L Word (Maybe Integer)
wxxint = signed

natint :: Conn 'L Natural (Maybe Integer)
natint = ConnL (fmap fromIntegral . fromPred (/= 0)) (maybe 0 $ fromInteger . max 0)

i08int :: Conn 'L Int8 (Maybe Integer)
i08int = signed

i16int :: Conn 'L Int16 (Maybe Integer)
i16int = signed

i32int :: Conn 'L Int32 (Maybe Integer)
i32int = signed

i64int :: Conn 'L Int64 (Maybe Integer)
i64int = signed

ixxint :: Conn 'L Int (Maybe Integer)
ixxint = signed

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

fromPred :: (a -> Bool) -> a -> Maybe a
fromPred p a = a <$ guard (p a)

signed :: forall a b. (Bounded a, Integral a, Integral b) => Conn 'L a (Maybe b)
signed = ConnL f g
  where
    f = fmap fromIntegral . fromPred (/= minBound)
    g = maybe minBound $ fromIntegral @b . min (fromIntegral @a maxBound) . max (fromIntegral @a minBound)
