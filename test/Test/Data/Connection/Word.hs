{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Word where

import Data.Int
import Data.Word
import Data.Connection.Trip
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
  inf <- forAll $ gen_top (G.integral rn)

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)
  w16' <- forAll $ G.integral (ri @Word16)
  i32' <- forAll $ G.integral (ri @Int32)
  w32' <- forAll $ G.integral (ri @Word32)
  i64' <- forAll $ G.integral (ri @Int64)
  w64' <- forAll $ G.integral (ri @Word64)
  nat' <- forAll $ G.integral rn
  inf' <- forAll $ gen_top (G.integral rn)

  assert $ Prop.adjoined w64nat w64 nat
  assert $ Prop.adjoined w64i64 w64 i64
  assert $ Prop.adjoined w32nat w32 nat
  assert $ Prop.adjoined w32w64 w32 w64
  assert $ Prop.adjoined w32i32 w32 i32
  assert $ Prop.adjoined w16nat w16 nat
  assert $ Prop.adjoined w16w64 w16 w64
  assert $ Prop.adjoined w16w32 w16 w32
  assert $ Prop.adjoined w16i16 w16 i16
  assert $ Prop.adjoined w08nat w08 nat
  assert $ Prop.adjoined w08w64 w08 w64
  assert $ Prop.adjoined w08w32 w08 w32
  assert $ Prop.adjoined w08w16 w08 w16
  assert $ Prop.adjoined w08i08 w08 i08
  assert $ Prop.adjoined (tripl w08nat') w08 inf
  assert $ Prop.adjoined (tripr w08nat') inf w08
  assert $ Prop.adjoined (tripl w16nat') w16 inf
  assert $ Prop.adjoined (tripr w16nat') inf w16
  assert $ Prop.adjoined (tripl w32nat') w32 inf
  assert $ Prop.adjoined (tripr w32nat') inf w32
  assert $ Prop.adjoined (tripl w64nat') w64 inf
  assert $ Prop.adjoined (tripr w64nat') inf w64

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
  assert $ Prop.closed (tripl w08nat') w08
  assert $ Prop.closed (tripr w08nat') inf
  assert $ Prop.closed (tripl w16nat') w16
  assert $ Prop.closed (tripr w16nat') inf
  assert $ Prop.closed (tripl w32nat') w32
  assert $ Prop.closed (tripr w32nat') inf
  assert $ Prop.closed (tripl w64nat') w64
  assert $ Prop.closed (tripr w64nat') inf

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
  assert $ Prop.kernel (tripl w08nat') inf
  assert $ Prop.kernel (tripr w08nat') w08
  assert $ Prop.kernel (tripl w16nat') inf
  assert $ Prop.kernel (tripr w16nat') w16
  assert $ Prop.kernel (tripl w32nat') inf
  assert $ Prop.kernel (tripr w32nat') w32
  assert $ Prop.kernel (tripl w64nat') inf
  assert $ Prop.kernel (tripr w64nat') w64

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
  assert $ Prop.monotonel (tripl w08nat') w08 w08'
  assert $ Prop.monotonel (tripr w08nat') inf inf'
  assert $ Prop.monotonel (tripl w16nat') w16 w16'
  assert $ Prop.monotonel (tripr w16nat') inf inf'
  assert $ Prop.monotonel (tripl w32nat') w32 w32'
  assert $ Prop.monotonel (tripr w32nat') inf inf'
  assert $ Prop.monotonel (tripl w64nat') w64 w64'
  assert $ Prop.monotonel (tripr w64nat') inf inf'

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
  assert $ Prop.monotoner (tripl w08nat') inf inf'
  assert $ Prop.monotoner (tripr w08nat') w08 w08'
  assert $ Prop.monotoner (tripl w16nat') inf inf'
  assert $ Prop.monotoner (tripr w16nat') w16 w16'
  assert $ Prop.monotoner (tripl w32nat') inf inf'
  assert $ Prop.monotoner (tripr w32nat') w32 w32'
  assert $ Prop.monotoner (tripl w64nat') inf inf'
  assert $ Prop.monotoner (tripr w64nat') w64 w64'

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
  assert $ Prop.projectivel (tripl w08nat') w08
  assert $ Prop.projectivel (tripr w08nat') inf
  assert $ Prop.projectivel (tripl w16nat') w16
  assert $ Prop.projectivel (tripr w16nat') inf
  assert $ Prop.projectivel (tripl w32nat') w32
  assert $ Prop.projectivel (tripr w32nat') inf
  assert $ Prop.projectivel (tripl w64nat') w64
  assert $ Prop.projectivel (tripr w64nat') inf

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
  assert $ Prop.projectiver (tripl w08nat') inf
  assert $ Prop.projectiver (tripr w08nat') w08
  assert $ Prop.projectiver (tripl w16nat') inf
  assert $ Prop.projectiver (tripr w16nat') w16
  assert $ Prop.projectiver (tripl w32nat') inf
  assert $ Prop.projectiver (tripr w32nat') w32
  assert $ Prop.projectiver (tripl w64nat') inf
  assert $ Prop.projectiver (tripr w64nat') w64

tests :: IO Bool
tests = checkParallel $$(discover)
