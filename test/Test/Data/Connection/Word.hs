{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Word where

import Data.Int
import Data.Word
import Data.Connection.Type
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
  inf <- forAll $ gen_lowered (G.integral rn)

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)
  w16' <- forAll $ G.integral (ri @Word16)
  i32' <- forAll $ G.integral (ri @Int32)
  w32' <- forAll $ G.integral (ri @Word32)
  i64' <- forAll $ G.integral (ri @Int64)
  w64' <- forAll $ G.integral (ri @Word64)
  nat' <- forAll $ G.integral rn
  inf' <- forAll $ gen_lowered (G.integral rn)

  assert $ Prop.adjoint w64nat w64 nat
  assert $ Prop.adjoint w64i64 w64 i64
  assert $ Prop.adjoint w32nat w32 nat
  assert $ Prop.adjoint w32w64 w32 w64
  assert $ Prop.adjoint w32i32 w32 i32
  assert $ Prop.adjoint w16nat w16 nat
  assert $ Prop.adjoint w16w64 w16 w64
  assert $ Prop.adjoint w16w32 w16 w32
  assert $ Prop.adjoint w16i16 w16 i16
  assert $ Prop.adjoint w08nat w08 nat
  assert $ Prop.adjoint w08w64 w08 w64
  assert $ Prop.adjoint w08w32 w08 w32
  assert $ Prop.adjoint w08w16 w08 w16
  assert $ Prop.adjoint w08i08 w08 i08
  assert $ Prop.adjoint (tripl w08nat') w08 inf
  assert $ Prop.adjoint (tripr w08nat') inf w08
  assert $ Prop.adjoint (tripl w16nat') w16 inf
  assert $ Prop.adjoint (tripr w16nat') inf w16
  assert $ Prop.adjoint (tripl w32nat') w32 inf
  assert $ Prop.adjoint (tripr w32nat') inf w32
  assert $ Prop.adjoint (tripl w64nat') w64 inf
  assert $ Prop.adjoint (tripr w64nat') inf w64

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

  assert $ Prop.monotoneL w64nat w64 w64'
  assert $ Prop.monotoneL w64i64 w64 w64'
  assert $ Prop.monotoneL w32nat w32 w32'
  assert $ Prop.monotoneL w32w64 w32 w32'
  assert $ Prop.monotoneL w32i32 w32 w32'
  assert $ Prop.monotoneL w16nat w16 w16'
  assert $ Prop.monotoneL w16w64 w16 w16'
  assert $ Prop.monotoneL w16w32 w16 w16'
  assert $ Prop.monotoneL w16i16 w16 w16'
  assert $ Prop.monotoneL w08nat w08 w08'
  assert $ Prop.monotoneL w08w64 w08 w08'
  assert $ Prop.monotoneL w08w32 w08 w08'
  assert $ Prop.monotoneL w08w16 w08 w08'
  assert $ Prop.monotoneL w08i08 w08 w08'
  assert $ Prop.monotoneL (tripl w08nat') w08 w08'
  assert $ Prop.monotoneL (tripr w08nat') inf inf'
  assert $ Prop.monotoneL (tripl w16nat') w16 w16'
  assert $ Prop.monotoneL (tripr w16nat') inf inf'
  assert $ Prop.monotoneL (tripl w32nat') w32 w32'
  assert $ Prop.monotoneL (tripr w32nat') inf inf'
  assert $ Prop.monotoneL (tripl w64nat') w64 w64'
  assert $ Prop.monotoneL (tripr w64nat') inf inf'

  assert $ Prop.monotoneR w64nat nat nat'
  assert $ Prop.monotoneR w64i64 i64 i64'
  assert $ Prop.monotoneR w32nat nat nat'
  assert $ Prop.monotoneR w32w64 w64 w64'
  assert $ Prop.monotoneR w32i32 i32 i32'
  assert $ Prop.monotoneR w16nat nat nat'
  assert $ Prop.monotoneR w16w64 w64 w64'
  assert $ Prop.monotoneR w16w32 w32 w32'
  assert $ Prop.monotoneR w16i16 i16 i16'
  assert $ Prop.monotoneR w08nat nat nat'
  assert $ Prop.monotoneR w08w64 w64 w64'
  assert $ Prop.monotoneR w08w32 w32 w32'
  assert $ Prop.monotoneR w08w16 w16 w16'
  assert $ Prop.monotoneR w08i08 i08 i08'
  assert $ Prop.monotoneR (tripl w08nat') inf inf'
  assert $ Prop.monotoneR (tripr w08nat') w08 w08'
  assert $ Prop.monotoneR (tripl w16nat') inf inf'
  assert $ Prop.monotoneR (tripr w16nat') w16 w16'
  assert $ Prop.monotoneR (tripl w32nat') inf inf'
  assert $ Prop.monotoneR (tripr w32nat') w32 w32'
  assert $ Prop.monotoneR (tripl w64nat') inf inf'
  assert $ Prop.monotoneR (tripr w64nat') w64 w64'

  assert $ Prop.projectiveL w64nat w64
  assert $ Prop.projectiveL w64i64 w64
  assert $ Prop.projectiveL w32nat w32
  assert $ Prop.projectiveL w32w64 w32
  assert $ Prop.projectiveL w32i32 w32
  assert $ Prop.projectiveL w16nat w16
  assert $ Prop.projectiveL w16w64 w16
  assert $ Prop.projectiveL w16w32 w16
  assert $ Prop.projectiveL w16i16 w16
  assert $ Prop.projectiveL w08nat w08
  assert $ Prop.projectiveL w08w64 w08
  assert $ Prop.projectiveL w08w32 w08
  assert $ Prop.projectiveL w08w16 w08
  assert $ Prop.projectiveL w08i08 w08
  assert $ Prop.projectiveL (tripl w08nat') w08
  assert $ Prop.projectiveL (tripr w08nat') inf
  assert $ Prop.projectiveL (tripl w16nat') w16
  assert $ Prop.projectiveL (tripr w16nat') inf
  assert $ Prop.projectiveL (tripl w32nat') w32
  assert $ Prop.projectiveL (tripr w32nat') inf
  assert $ Prop.projectiveL (tripl w64nat') w64
  assert $ Prop.projectiveL (tripr w64nat') inf

  assert $ Prop.projectiveR w64nat nat
  assert $ Prop.projectiveR w64i64 i64
  assert $ Prop.projectiveR w32nat nat
  assert $ Prop.projectiveR w32w64 w64
  assert $ Prop.projectiveR w32i32 i32
  assert $ Prop.projectiveR w16nat nat
  assert $ Prop.projectiveR w16w64 w64
  assert $ Prop.projectiveR w16w32 w32
  assert $ Prop.projectiveR w16i16 i16
  assert $ Prop.projectiveR w08nat nat
  assert $ Prop.projectiveR w08w64 w64
  assert $ Prop.projectiveR w08w32 w32
  assert $ Prop.projectiveR w08w16 w16
  assert $ Prop.projectiveR w08i08 i08
  assert $ Prop.projectiveR (tripl w08nat') inf
  assert $ Prop.projectiveR (tripr w08nat') w08
  assert $ Prop.projectiveR (tripl w16nat') inf
  assert $ Prop.projectiveR (tripr w16nat') w16
  assert $ Prop.projectiveR (tripl w32nat') inf
  assert $ Prop.projectiveR (tripr w32nat') w32
  assert $ Prop.projectiveR (tripl w64nat') inf
  assert $ Prop.projectiveR (tripr w64nat') w64

tests :: IO Bool
tests = checkParallel $$(discover)
