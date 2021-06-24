{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
module Test.Data.Connection.Int where

import Data.Connection.Int
import Data.Int
import Data.Word
import Hedgehog
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G

prop_connections_int16 :: Property
prop_connections_int16 = withTests 1000 . property $ do

  i08 <- forAll $ gen_extended $ G.integral (ri @Int8)
  w08 <- forAll $ gen_extended $ G.integral (ri @Word8)
  i16 <- forAll $ G.integral (ri @Int16)

  i08' <- forAll $ gen_extended $ G.integral (ri @Int8)
  w08' <- forAll $ gen_extended $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)

  assert $ Prop.adjoint w08i16 w08 i16
  assert $ Prop.closed w08i16 w08
  assert $ Prop.kernel w08i16 i16
  assert $ Prop.monotonic w08i16 w08 w08' i16 i16'
  assert $ Prop.idempotent w08i16 w08 i16

  assert $ Prop.adjoint i08i16 i08 i16
  assert $ Prop.closed i08i16 i08
  assert $ Prop.kernel i08i16 i16
  assert $ Prop.monotonic i08i16 i08 i08' i16 i16'
  assert $ Prop.idempotent i08i16 i08 i16

prop_connections_int32 :: Property
prop_connections_int32 = withTests 1000 . property $ do

  i08 <- forAll $ gen_extended $ G.integral (ri @Int8)
  w08 <- forAll $ gen_extended $ G.integral (ri @Word8)
  i16 <- forAll $ gen_extended $ G.integral (ri @Int16)
  w16 <- forAll $ gen_extended $ G.integral (ri @Word16)
  i32 <- forAll $ G.integral (ri @Int32)

  i08' <- forAll $ gen_extended $ G.integral (ri @Int8)
  w08' <- forAll $ gen_extended $ G.integral (ri @Word8)
  i16' <- forAll $ gen_extended $ G.integral (ri @Int16)
  w16' <- forAll $ gen_extended $ G.integral (ri @Word16)
  i32' <- forAll $ G.integral (ri @Int32)

  assert $ Prop.adjoint w08i32 w08 i32
  assert $ Prop.closed w08i32 w08
  assert $ Prop.kernel w08i32 i32
  assert $ Prop.monotonic w08i32 w08 w08' i32 i32'
  assert $ Prop.idempotent w08i32 w08 i32
  
  assert $ Prop.adjoint w16i32 w16 i32
  assert $ Prop.closed w16i32 w16
  assert $ Prop.kernel w16i32 i32
  assert $ Prop.monotonic w16i32 w16 w16' i32 i32'
  assert $ Prop.idempotent w16i32 w16 i32

  assert $ Prop.adjoint i08i32 i08 i32
  assert $ Prop.closed i08i32 i08
  assert $ Prop.kernel i08i32 i32
  assert $ Prop.monotonic i08i32 i08 i08' i32 i32'
  assert $ Prop.idempotent i08i32 i08 i32
  
  assert $ Prop.adjoint i16i32 i16 i32
  assert $ Prop.closed i16i32 i16
  assert $ Prop.kernel i16i32 i32
  assert $ Prop.monotonic i16i32 i16 i16' i32 i32'
  assert $ Prop.idempotent i16i32 i16 i32

prop_connections_int64 :: Property
prop_connections_int64 = withTests 1000 . property $ do

  i08 <- forAll $ gen_extended $ G.integral (ri @Int8)
  w08 <- forAll $ gen_extended $ G.integral (ri @Word8)
  i16 <- forAll $ gen_extended $ G.integral (ri @Int16)
  w16 <- forAll $ gen_extended $ G.integral (ri @Word16)
  i32 <- forAll $ gen_extended $ G.integral (ri @Int32)
  w32 <- forAll $ gen_extended $ G.integral (ri @Word32)
  i64 <- forAll $ G.integral (ri @Int64)

  i08' <- forAll $ gen_extended $ G.integral (ri @Int8)
  w08' <- forAll $ gen_extended $ G.integral (ri @Word8)
  i16' <- forAll $ gen_extended $ G.integral (ri @Int16)
  w16' <- forAll $ gen_extended $ G.integral (ri @Word16)
  i32' <- forAll $ gen_extended $ G.integral (ri @Int32)
  w32' <- forAll $ gen_extended $ G.integral (ri @Word32)
  i64' <- forAll $ G.integral (ri @Int64)

  assert $ Prop.adjoint w08i64 w08 i64
  assert $ Prop.closed w08i64 w08
  assert $ Prop.kernel w08i64 i64
  assert $ Prop.monotonic w08i64 w08 w08' i64 i64'
  assert $ Prop.idempotent w08i64 w08 i64
  
  assert $ Prop.adjoint w16i64 w16 i64
  assert $ Prop.closed w16i64 w16
  assert $ Prop.kernel w16i64 i64
  assert $ Prop.monotonic w16i64 w16 w16' i64 i64'
  assert $ Prop.idempotent w16i64 w16 i64
  
  assert $ Prop.adjoint w32i64 w32 i64
  assert $ Prop.closed w32i64 w32
  assert $ Prop.kernel w32i64 i64
  assert $ Prop.monotonic w32i64 w32 w32' i64 i64'
  assert $ Prop.idempotent w32i64 w32 i64

  assert $ Prop.adjoint i08i64 i08 i64
  assert $ Prop.closed i08i64 i08
  assert $ Prop.kernel i08i64 i64
  assert $ Prop.monotonic i08i64 i08 i08' i64 i64'
  assert $ Prop.idempotent i08i64 i08 i64
  
  assert $ Prop.adjoint i16i64 i16 i64
  assert $ Prop.closed i16i64 i16
  assert $ Prop.kernel i16i64 i64
  assert $ Prop.monotonic i16i64 i16 i16' i64 i64'
  assert $ Prop.idempotent i16i64 i16 i64
  
  assert $ Prop.adjoint i32i64 i32 i64
  assert $ Prop.closed i32i64 i32
  assert $ Prop.kernel i32i64 i64
  assert $ Prop.monotonic i32i64 i32 i32' i64 i64'
  assert $ Prop.idempotent i32i64 i32 i64

prop_connections_int :: Property
prop_connections_int = withTests 1000 . property $ do

  i08 <- forAll $ gen_extended $ G.integral (ri @Int8)
  w08 <- forAll $ gen_extended $ G.integral (ri @Word8)
  i16 <- forAll $ gen_extended $ G.integral (ri @Int16)
  w16 <- forAll $ gen_extended $ G.integral (ri @Word16)
  i32 <- forAll $ gen_extended $ G.integral (ri @Int32)
  w32 <- forAll $ gen_extended $ G.integral (ri @Word32)
  ixx <- forAll $ G.integral (ri @Int)

  i08' <- forAll $ gen_extended $ G.integral (ri @Int8)
  w08' <- forAll $ gen_extended $ G.integral (ri @Word8)
  i16' <- forAll $ gen_extended $ G.integral (ri @Int16)
  w16' <- forAll $ gen_extended $ G.integral (ri @Word16)
  i32' <- forAll $ gen_extended $ G.integral (ri @Int32)
  w32' <- forAll $ gen_extended $ G.integral (ri @Word32)
  ixx' <- forAll $ G.integral (ri @Int)

  assert $ Prop.adjoint w08ixx w08 ixx
  assert $ Prop.closed w08ixx w08
  assert $ Prop.kernel w08ixx ixx
  assert $ Prop.monotonic w08ixx w08 w08' ixx ixx'
  assert $ Prop.idempotent w08ixx w08 ixx
  
  assert $ Prop.adjoint w16ixx w16 ixx
  assert $ Prop.closed w16ixx w16
  assert $ Prop.kernel w16ixx ixx
  assert $ Prop.monotonic w16ixx w16 w16' ixx ixx'
  assert $ Prop.idempotent w16ixx w16 ixx
  
  assert $ Prop.adjoint w32ixx w32 ixx
  assert $ Prop.closed w32ixx w32
  assert $ Prop.kernel w32ixx ixx
  assert $ Prop.monotonic w32ixx w32 w32' ixx ixx'
  assert $ Prop.idempotent w32ixx w32 ixx

  assert $ Prop.adjoint i08ixx i08 ixx
  assert $ Prop.closed i08ixx i08
  assert $ Prop.kernel i08ixx ixx
  assert $ Prop.monotonic i08ixx i08 i08' ixx ixx'
  assert $ Prop.idempotent i08ixx i08 ixx
  
  assert $ Prop.adjoint i16ixx i16 ixx
  assert $ Prop.closed i16ixx i16
  assert $ Prop.kernel i16ixx ixx
  assert $ Prop.monotonic i16ixx i16 i16' ixx ixx'
  assert $ Prop.idempotent i16ixx i16 ixx
  
  assert $ Prop.adjoint i32ixx i32 ixx
  assert $ Prop.closed i32ixx i32
  assert $ Prop.kernel i32ixx ixx
  assert $ Prop.monotonic i32ixx i32 i32' ixx ixx'
  assert $ Prop.idempotent i32ixx i32 ixx

prop_connections_integer :: Property
prop_connections_integer = withTests 1000 . property $ do

  i08 <- forAll $ gen_extended $ G.integral (ri @Int8)
  w08 <- forAll $ gen_extended $ G.integral (ri @Word8)
  i16 <- forAll $ gen_extended $ G.integral (ri @Int16)
  w16 <- forAll $ gen_extended $ G.integral (ri @Word16)
  i32 <- forAll $ gen_extended $ G.integral (ri @Int32)
  w32 <- forAll $ gen_extended $ G.integral (ri @Word32)
  i64 <- forAll $ gen_extended $ G.integral (ri @Int64)
  w64 <- forAll $ gen_extended $ G.integral (ri @Word64)
  ixx <- forAll $ gen_extended $ G.integral (ri @Int)
  wxx <- forAll $ gen_extended $ G.integral (ri @Word)
  int <- forAll $ gen_maybe $ G.integral ri'

  i08' <- forAll $ gen_extended $ G.integral (ri @Int8)
  w08' <- forAll $ gen_extended $ G.integral (ri @Word8)
  i16' <- forAll $ gen_extended $ G.integral (ri @Int16)
  w16' <- forAll $ gen_extended $ G.integral (ri @Word16)
  i32' <- forAll $ gen_extended $ G.integral (ri @Int32)
  w32' <- forAll $ gen_extended $ G.integral (ri @Word32)
  i64' <- forAll $ gen_extended $ G.integral (ri @Int64)
  w64' <- forAll $ gen_extended $ G.integral (ri @Word64)
  ixx' <- forAll $ gen_extended $ G.integral (ri @Int)
  wxx' <- forAll $ gen_extended $ G.integral (ri @Word)
  int' <- forAll $ gen_maybe (G.integral ri')
  
  assert $ Prop.adjointL w08int w08 int
  assert $ Prop.closedL w08int w08
  assert $ Prop.kernelL w08int int
  assert $ Prop.monotonicL w08int w08 w08' int int'
  assert $ Prop.idempotentL w08int w08 int
  
  assert $ Prop.adjointL w16int w16 int
  assert $ Prop.closedL w16int w16
  assert $ Prop.kernelL w16int int
  assert $ Prop.monotonicL w16int w16 w16' int int'
  assert $ Prop.idempotentL w16int w16 int
  
  assert $ Prop.adjointL w32int w32 int
  assert $ Prop.closedL w32int w32
  assert $ Prop.kernelL w32int int
  assert $ Prop.monotonicL w32int w32 w32' int int'
  assert $ Prop.idempotentL w32int w32 int
  
  assert $ Prop.adjointL w64int w64 int
  assert $ Prop.closedL w64int w64
  assert $ Prop.kernelL w64int int
  assert $ Prop.monotonicL w64int w64 w64' int int'
  assert $ Prop.idempotentL w64int w64 int
 
  assert $ Prop.adjointL wxxint wxx int
  assert $ Prop.closedL wxxint wxx
  assert $ Prop.kernelL wxxint int
  assert $ Prop.monotonicL wxxint wxx wxx' int int'
  assert $ Prop.idempotentL wxxint wxx int
  
  assert $ Prop.adjointL i08int i08 int
  assert $ Prop.closedL i08int i08
  assert $ Prop.kernelL i08int int
  assert $ Prop.monotonicL i08int i08 i08' int int'
  assert $ Prop.idempotentL i08int i08 int
  
  assert $ Prop.adjointL i16int i16 int
  assert $ Prop.closedL i16int i16
  assert $ Prop.kernelL i16int int
  assert $ Prop.monotonicL i16int i16 i16' int int'
  assert $ Prop.idempotentL i16int i16 int
  
  assert $ Prop.adjointL i32int i32 int
  assert $ Prop.closedL i32int i32
  assert $ Prop.kernelL i32int int
  assert $ Prop.monotonicL i32int i32 i32' int int'
  assert $ Prop.idempotentL i32int i32 int
  
  assert $ Prop.adjointL i64int i64 int
  assert $ Prop.closedL i64int i64
  assert $ Prop.kernelL i64int int
  assert $ Prop.monotonicL i64int i64 i64' int int'
  assert $ Prop.idempotentL i64int i64 int
 
  assert $ Prop.adjointL ixxint ixx int
  assert $ Prop.closedL ixxint ixx
  assert $ Prop.kernelL ixxint int
  assert $ Prop.monotonicL ixxint ixx ixx' int int'
  assert $ Prop.idempotentL ixxint ixx int



tests :: IO Bool
tests = checkParallel $$(discover)
