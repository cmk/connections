{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Word where

import Data.Int
import Data.Word
import Data.Connection.Word
import Test.Data.Connection
import qualified Data.Connection.Property as Prop

import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R


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

  assert $ Prop.monotonel w64nat w64 w64'
  assert $ Prop.monotonel w64i64 w64 w64'
  assert $ Prop.monotonel w32nat w32 w32'
  assert $ Prop.monotonel w32w64 w32 w32'
  assert $ Prop.monotonel w32i32 w32 w32'
  assert $ Prop.monotonel w16nat w16 w16'
  assert $ Prop.monotonel w16w64 w16 w16'
  assert $ Prop.monotonel w16w32 w16 w16'
  assert $ Prop.monotonel w16i16 w16 w16'
  assert $ Prop.monotonel w08nat w08 w08'
  assert $ Prop.monotonel w08w64 w08 w08'
  assert $ Prop.monotonel w08w32 w08 w08'
  assert $ Prop.monotonel w08w16 w08 w08'
  assert $ Prop.monotonel w08i08 w08 w08'

  assert $ Prop.monotoner w64nat nat nat'
  assert $ Prop.monotoner w64i64 i64 i64'
  assert $ Prop.monotoner w32nat nat nat'
  assert $ Prop.monotoner w32w64 w64 w64'
  assert $ Prop.monotoner w32i32 i32 i32'
  assert $ Prop.monotoner w16nat nat nat'
  assert $ Prop.monotoner w16w64 w64 w64'
  assert $ Prop.monotoner w16w32 w32 w32'
  assert $ Prop.monotoner w16i16 i16 i16'
  assert $ Prop.monotoner w08nat nat nat'
  assert $ Prop.monotoner w08w64 w64 w64'
  assert $ Prop.monotoner w08w32 w32 w32'
  assert $ Prop.monotoner w08w16 w16 w16'
  assert $ Prop.monotoner w08i08 i08 i08'

  assert $ Prop.projectivel w64nat w64
  assert $ Prop.projectivel w64i64 w64
  assert $ Prop.projectivel w32nat w32
  assert $ Prop.projectivel w32w64 w32
  assert $ Prop.projectivel w32i32 w32
  assert $ Prop.projectivel w16nat w16
  assert $ Prop.projectivel w16w64 w16
  assert $ Prop.projectivel w16w32 w16
  assert $ Prop.projectivel w16i16 w16
  assert $ Prop.projectivel w08nat w08
  assert $ Prop.projectivel w08w64 w08
  assert $ Prop.projectivel w08w32 w08
  assert $ Prop.projectivel w08w16 w08
  assert $ Prop.projectivel w08i08 w08

  assert $ Prop.projectiver w64nat nat
  assert $ Prop.projectiver w64i64 i64
  assert $ Prop.projectiver w32nat nat
  assert $ Prop.projectiver w32w64 w64
  assert $ Prop.projectiver w32i32 i32
  assert $ Prop.projectiver w16nat nat
  assert $ Prop.projectiver w16w64 w64
  assert $ Prop.projectiver w16w32 w32
  assert $ Prop.projectiver w16i16 i16
  assert $ Prop.projectiver w08nat nat
  assert $ Prop.projectiver w08w64 w64
  assert $ Prop.projectiver w08w32 w32
  assert $ Prop.projectiver w08w16 w16
  assert $ Prop.projectiver w08i08 i08

tests :: IO Bool
tests = checkParallel $$(discover)
