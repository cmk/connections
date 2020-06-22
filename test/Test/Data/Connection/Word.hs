{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Word where

import Data.Int
import Data.Word
import Data.Connection.Conn
import Data.Connection.Word
import Hedgehog
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G

prop_connections :: Property
prop_connections = withTests 1000 . property $ do

  i08 <- forAll $ G.integral (ri @Int8)
  w08 <- forAll $ G.integral (ri @Word8)
  i16 <- forAll $ G.integral (ri @Int16)
  w16 <- forAll $ G.integral (ri @Word16)
  i32 <- forAll $ G.integral (ri @Int32)
  w32 <- forAll $ G.integral (ri @Word32)
  i64 <- forAll $ G.integral (ri @Int64)
  w64 <- forAll $ G.integral (ri @Word64)
  nat <- forAll $ G.integral rn

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)
  w16' <- forAll $ G.integral (ri @Word16)
  i32' <- forAll $ G.integral (ri @Int32)
  w32' <- forAll $ G.integral (ri @Word32)
  i64' <- forAll $ G.integral (ri @Int64)
  w64' <- forAll $ G.integral (ri @Word64)
  nat' <- forAll $ G.integral rn

  assert $ Prop.adjointL w64nat w64 nat
  assert $ Prop.adjointL w64i64 w64 i64
  assert $ Prop.adjointL w32nat w32 nat
  assert $ Prop.adjointL w32w64 w32 w64
  assert $ Prop.adjointL w32i32 w32 i32
  assert $ Prop.adjointL w16nat w16 nat
  assert $ Prop.adjointL w16w64 w16 w64
  assert $ Prop.adjointL w16w32 w16 w32
  assert $ Prop.adjointL w16i16 w16 i16
  assert $ Prop.adjointL w08nat w08 nat
  assert $ Prop.adjointL w08w64 w08 w64
  assert $ Prop.adjointL w08w32 w08 w32
  assert $ Prop.adjointL w08w16 w08 w16
  assert $ Prop.adjointL w08i08 w08 i08

  assert $ Prop.closedL w64nat w64
  assert $ Prop.closedL w64i64 w64
  assert $ Prop.closedL w32nat w32
  assert $ Prop.closedL w32w64 w32
  assert $ Prop.closedL w32i32 w32
  assert $ Prop.closedL w16nat w16
  assert $ Prop.closedL w16w64 w16
  assert $ Prop.closedL w16w32 w16
  assert $ Prop.closedL w16i16 w16
  assert $ Prop.closedL w08nat w08
  assert $ Prop.closedL w08w64 w08
  assert $ Prop.closedL w08w32 w08
  assert $ Prop.closedL w08w16 w08
  assert $ Prop.closedL w08i08 w08

  assert $ Prop.kernelL w64nat nat
  assert $ Prop.kernelL w64i64 i64
  assert $ Prop.kernelL w32nat nat
  assert $ Prop.kernelL w32w64 w64
  assert $ Prop.kernelL w32i32 i32
  assert $ Prop.kernelL w16nat nat
  assert $ Prop.kernelL w16w64 w64
  assert $ Prop.kernelL w16w32 w32
  assert $ Prop.kernelL w16i16 i16
  assert $ Prop.kernelL w08nat nat
  assert $ Prop.kernelL w08w64 w64
  assert $ Prop.kernelL w08w32 w32
  assert $ Prop.kernelL w08w16 w16
  assert $ Prop.kernelL w08i08 i08

  assert $ Prop.monotonicL w64nat w64 w64' nat nat'
  assert $ Prop.monotonicL w64i64 w64 w64' i64 i64'
  assert $ Prop.monotonicL w32nat w32 w32' nat nat'
  assert $ Prop.monotonicL w32w64 w32 w32' w64 w64'
  assert $ Prop.monotonicL w32i32 w32 w32' i32 i32'
  assert $ Prop.monotonicL w16nat w16 w16' nat nat'
  assert $ Prop.monotonicL w16w64 w16 w16' w64 w64'
  assert $ Prop.monotonicL w16w32 w16 w16' w32 w32'
  assert $ Prop.monotonicL w16i16 w16 w16' i16 i16'
  assert $ Prop.monotonicL w08nat w08 w08' nat nat'
  assert $ Prop.monotonicL w08w64 w08 w08' w64 w64'
  assert $ Prop.monotonicL w08w32 w08 w08' w32 w32'
  assert $ Prop.monotonicL w08w16 w08 w08' w16 w16'
  assert $ Prop.monotonicL w08i08 w08 w08' i08 i08'

  assert $ Prop.idempotentL w64nat w64 nat
  assert $ Prop.idempotentL w64i64 w64 i64
  assert $ Prop.idempotentL w32nat w32 nat
  assert $ Prop.idempotentL w32w64 w32 w64
  assert $ Prop.idempotentL w32i32 w32 i32
  assert $ Prop.idempotentL w16nat w16 nat
  assert $ Prop.idempotentL w16w64 w16 w64
  assert $ Prop.idempotentL w16w32 w16 w32
  assert $ Prop.idempotentL w16i16 w16 i16
  assert $ Prop.idempotentL w08nat w08 nat
  assert $ Prop.idempotentL w08w64 w08 w64
  assert $ Prop.idempotentL w08w32 w08 w32
  assert $ Prop.idempotentL w08w16 w08 w16
  assert $ Prop.idempotentL w08i08 w08 i08

tests :: IO Bool
tests = checkParallel $$(discover)
