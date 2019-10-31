{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Int where

import Data.Int
import Data.Word
import Data.Connection
import Data.Connection.Int
import Numeric.Natural
import qualified Data.Connection.Property as Prop

import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

ri :: (Integral a, Bounded a) => Range a
ri = R.linearFrom 0 minBound maxBound

rint :: Range Integer
rint = R.linearFrom 0 (- 2^127) (2^127)

rnat :: Range Natural
rnat = R.linear 0 (2^128)

prop_connections_int_wrd :: Property
prop_connections_int_wrd = withTests 1000 . property $ do

  i08 <- forAll $ G.integral (ri @Int8)
  w08 <- forAll $ G.integral (ri @Word8)
  i16 <- forAll $ G.integral (ri @Int16)
  w16 <- forAll $ G.integral (ri @Word16)
  i32 <- forAll $ G.integral (ri @Int32)
  w32 <- forAll $ G.integral (ri @Word32)
  i64 <- forAll $ G.integral (ri @Int64)
  w64 <- forAll $ G.integral (ri @Word64)
  int <- forAll $ G.integral rint
  nat <- forAll $ G.integral rnat

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)
  w16' <- forAll $ G.integral (ri @Word16)
  i32' <- forAll $ G.integral (ri @Int32)
  w32' <- forAll $ G.integral (ri @Word32)
  i64' <- forAll $ G.integral (ri @Int64)
  w64' <- forAll $ G.integral (ri @Word64)
  int' <- forAll $ G.integral rint
  nat' <- forAll $ G.integral rnat

  assert $ Prop.connection intnat  int nat
  assert $ Prop.connection i64w64  i64 w64
  assert $ Prop.connection i64w64' i64 w64
  assert $ Prop.connection i32i64  i32 i64
  assert $ Prop.connection i32w32  i32 w32
  assert $ Prop.connection i32w32' i32 w32
  assert $ Prop.connection i16i64  i16 i64
  assert $ Prop.connection i16i32  i16 i32
  assert $ Prop.connection i16w16  i16 w16
  assert $ Prop.connection i16w16' i16 w16
  assert $ Prop.connection i08i64  i08 i64
  assert $ Prop.connection i08i32  i08 i32
  assert $ Prop.connection i08i16  i08 i16
  assert $ Prop.connection i08w08  i08 w08
  assert $ Prop.connection i08w08' i08 w08

  assert $ Prop.monotone' intnat  int int'
  assert $ Prop.monotone' i64w64  i64 i64'
  assert $ Prop.monotone' i64w64' i64 i64'
  assert $ Prop.monotone' i32i64  i32 i32'
  assert $ Prop.monotone' i32w32  i32 i32'
  assert $ Prop.monotone' i32w32' i32 i32'
  assert $ Prop.monotone' i16i64  i16 i16'
  assert $ Prop.monotone' i16i32  i16 i16'
  assert $ Prop.monotone' i16w16  i16 i16'
  assert $ Prop.monotone' i16w16' i16 i16'
  assert $ Prop.monotone' i08i64  i08 i08'
  assert $ Prop.monotone' i08i32  i08 i08'
  assert $ Prop.monotone' i08i16  i08 i08'
  assert $ Prop.monotone' i08w08  i08 i08'
  assert $ Prop.monotone' i08w08' i08 i08'

  assert $ Prop.monotone intnat  nat nat'
  assert $ Prop.monotone i64w64  w64 w64'
  assert $ Prop.monotone i64w64' w64 w64'
  assert $ Prop.monotone i32i64  i64 i64'
  assert $ Prop.monotone i32w32  w32 w32'
  assert $ Prop.monotone i32w32' w32 w32'
  assert $ Prop.monotone i16i64  i64 i64'
  assert $ Prop.monotone i16i32  i32 i32'
  assert $ Prop.monotone i16w16  w16 w16'
  assert $ Prop.monotone i16w16' w16 w16'
  assert $ Prop.monotone i08i64  i64 i64'
  assert $ Prop.monotone i08i32  i32 i32'
  assert $ Prop.monotone i08i16  i16 i16'
  assert $ Prop.monotone i08w08  w08 w08'
  assert $ Prop.monotone i08w08' w08 w08'

  assert $ Prop.closed intnat  int
  assert $ Prop.closed i64w64  i64
  assert $ Prop.closed i64w64' i64
  assert $ Prop.closed i32i64  i32
  assert $ Prop.closed i32w32  i32
  assert $ Prop.closed i32w32' i32
  assert $ Prop.closed i16i64  i16
  assert $ Prop.closed i16i32  i16
  assert $ Prop.closed i16w16  i16
  assert $ Prop.closed i16w16' i16
  assert $ Prop.closed i08i64  i08
  assert $ Prop.closed i08i32  i08
  assert $ Prop.closed i08i16  i08
  assert $ Prop.closed i08w08  i08
  assert $ Prop.closed i08w08' i08

  assert $ Prop.kernel intnat  nat
  assert $ Prop.kernel i64w64' w64
  assert $ Prop.kernel i64w64  w64
  assert $ Prop.kernel i32i64  i64
  assert $ Prop.kernel i32w32' w32
  assert $ Prop.kernel i32w32  w32
  assert $ Prop.kernel i16i64  i64
  assert $ Prop.kernel i16i32  i32
  assert $ Prop.kernel i16w16' w16
  assert $ Prop.kernel i16w16  w16
  assert $ Prop.kernel i08i64  i64
  assert $ Prop.kernel i08i32  i32
  assert $ Prop.kernel i08i16  i16
  assert $ Prop.kernel i08w08' w08
  assert $ Prop.kernel i08w08  w08

tests :: IO Bool
tests = checkParallel $$(discover)
