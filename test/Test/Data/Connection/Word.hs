{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Word where

import Data.Int
import Data.Word
import Data.Connection
import Data.Connection.Word
import Numeric.Natural
import qualified Data.Connection.Property as Prop

import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

ri :: (Integral a, Bounded a) => Range a
ri = R.linearFrom 0 minBound maxBound

rnat :: Range Natural
rnat = R.linear 0 (2^128)

prop_connections_wrd_int :: Property
prop_connections_wrd_int = withTests 1000 . property $ do

  i08 <- forAll $ G.integral (ri @Int8)
  w08 <- forAll $ G.integral (ri @Word8)
  i16 <- forAll $ G.integral (ri @Int16)
  w16 <- forAll $ G.integral (ri @Word16)
  i32 <- forAll $ G.integral (ri @Int32)
  w32 <- forAll $ G.integral (ri @Word32)
  i64 <- forAll $ G.integral (ri @Int64)
  w64 <- forAll $ G.integral (ri @Word64)
  nat <- forAll $ G.integral rnat

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)
  w16' <- forAll $ G.integral (ri @Word16)
  i32' <- forAll $ G.integral (ri @Int32)
  w32' <- forAll $ G.integral (ri @Word32)
  i64' <- forAll $ G.integral (ri @Int64)
  w64' <- forAll $ G.integral (ri @Word64)
  nat' <- forAll $ G.integral rnat

  assert $ Prop.connection w64nat w64 nat
  assert $ Prop.connection w64i64 w64 i64
  assert $ Prop.connection w32nat w32 nat
  assert $ Prop.connection w32w64 w32 w64
  assert $ Prop.connection w32i32 w32 i32
  assert $ Prop.connection w16nat w16 nat
  assert $ Prop.connection w16w64 w16 w64
  assert $ Prop.connection w16w32 w16 w32
  assert $ Prop.connection w16i16 w16 i16
  assert $ Prop.connection w08nat w08 nat
  assert $ Prop.connection w08w64 w08 w64
  assert $ Prop.connection w08w32 w08 w32
  assert $ Prop.connection w08w16 w08 w16
  assert $ Prop.connection w08i08 w08 i08

  assert $ Prop.monotone' w64nat w64 w64'
  assert $ Prop.monotone' w64i64 w64 w64'
  assert $ Prop.monotone' w32nat w32 w32'
  assert $ Prop.monotone' w32w64 w32 w32'
  assert $ Prop.monotone' w32i32 w32 w32'
  assert $ Prop.monotone' w16nat w16 w16'
  assert $ Prop.monotone' w16w64 w16 w16'
  assert $ Prop.monotone' w16w32 w16 w16'
  assert $ Prop.monotone' w16i16 w16 w16'
  assert $ Prop.monotone' w08nat w08 w08'
  assert $ Prop.monotone' w08w64 w08 w08'
  assert $ Prop.monotone' w08w32 w08 w08'
  assert $ Prop.monotone' w08w16 w08 w08'
  assert $ Prop.monotone' w08i08 w08 w08'

  assert $ Prop.monotone w64nat nat nat'
  assert $ Prop.monotone w64i64 i64 i64'
  assert $ Prop.monotone w32nat nat nat'
  assert $ Prop.monotone w32w64 w64 w64'
  assert $ Prop.monotone w32i32 i32 i32'
  assert $ Prop.monotone w16nat nat nat'
  assert $ Prop.monotone w16w64 w64 w64'
  assert $ Prop.monotone w16w32 w32 w32'
  assert $ Prop.monotone w16i16 i16 i16'
  assert $ Prop.monotone w08nat nat nat'
  assert $ Prop.monotone w08w64 w64 w64'
  assert $ Prop.monotone w08w32 w32 w32'
  assert $ Prop.monotone w08w16 w16 w16'
  assert $ Prop.monotone w08i08 i08 i08'

  assert $ Prop.closed w64nat w64
  assert $ Prop.closed w64i64 w64
  assert $ Prop.closed w32nat w32
  assert $ Prop.closed w32w64 w32
  assert $ Prop.closed w32i32 w32
  assert $ Prop.closed w16nat w16
  assert $ Prop.closed w16w64 w16
  assert $ Prop.closed w16w32 w16
  assert $ Prop.closed w16i16 w16
  assert $ Prop.closed w08nat w08
  assert $ Prop.closed w08w64 w08
  assert $ Prop.closed w08w32 w08
  assert $ Prop.closed w08w16 w08
  assert $ Prop.closed w08i08 w08

  assert $ Prop.kernel w64nat nat
  assert $ Prop.kernel w64i64 i64
  assert $ Prop.kernel w32nat nat
  assert $ Prop.kernel w32w64 w64
  assert $ Prop.kernel w32i32 i32
  assert $ Prop.kernel w16nat nat
  assert $ Prop.kernel w16w64 w64
  assert $ Prop.kernel w16w32 w32
  assert $ Prop.kernel w16i16 i16
  assert $ Prop.kernel w08nat nat
  assert $ Prop.kernel w08w64 w64
  assert $ Prop.kernel w08w32 w32
  assert $ Prop.kernel w08w16 w16
  assert $ Prop.kernel w08i08 i08

tests :: IO Bool
tests = checkParallel $$(discover)
