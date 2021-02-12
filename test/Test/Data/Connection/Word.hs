{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Word where

import Data.Int
import Data.Word
import Data.Connection.Word
import Hedgehog
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G

prop_connections_word8 :: Property
prop_connections_word8 = withTests 1000 . property $ do
  i08 <- forAll $ G.integral (ri @Int8)
  w08 <- forAll $ G.integral (ri @Word8)

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)

  assert $ Prop.adjointL i08w08 i08 w08
  assert $ Prop.closedL i08w08 i08
  assert $ Prop.kernelL i08w08 w08
  assert $ Prop.monotonicL i08w08 i08 i08' w08 w08'
  assert $ Prop.idempotentL i08w08 i08 w08

prop_connections_word16 :: Property
prop_connections_word16 = withTests 1000 . property $ do

  i08 <- forAll $ G.integral (ri @Int8)
  w08 <- forAll $ G.integral (ri @Word8)
  i16 <- forAll $ G.integral (ri @Int16)
  w16 <- forAll $ G.integral (ri @Word16)

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)
  w16' <- forAll $ G.integral (ri @Word16)
  
  assert $ Prop.adjointL w08w16 w08 w16
  assert $ Prop.closedL w08w16 w08
  assert $ Prop.kernelL w08w16 w16
  assert $ Prop.monotonicL w08w16 w08 w08' w16 w16'
  assert $ Prop.idempotentL w08w16 w08 w16
  
  assert $ Prop.adjointL i08w16 i08 w16
  assert $ Prop.closedL i08w16 i08
  assert $ Prop.kernelL i08w16 w16
  assert $ Prop.monotonicL i08w16 i08 i08' w16 w16'
  assert $ Prop.idempotentL i08w16 i08 w16
  
  assert $ Prop.adjointL i16w16 i16 w16
  assert $ Prop.closedL i16w16 i16
  assert $ Prop.kernelL i16w16 w16
  assert $ Prop.monotonicL i16w16 i16 i16' w16 w16'
  assert $ Prop.idempotentL i16w16 i16 w16

prop_connections_word32 :: Property
prop_connections_word32 = withTests 1000 . property $ do

  i08 <- forAll $ G.integral (ri @Int8)
  w08 <- forAll $ G.integral (ri @Word8)
  i16 <- forAll $ G.integral (ri @Int16)
  w16 <- forAll $ G.integral (ri @Word16)
  i32 <- forAll $ G.integral (ri @Int32)
  w32 <- forAll $ G.integral (ri @Word32)

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)
  w16' <- forAll $ G.integral (ri @Word16)
  i32' <- forAll $ G.integral (ri @Int32)
  w32' <- forAll $ G.integral (ri @Word32)
  
  assert $ Prop.adjointL w08w32 w08 w32
  assert $ Prop.closedL w08w32 w08
  assert $ Prop.kernelL w08w32 w32
  assert $ Prop.monotonicL w08w32 w08 w08' w32 w32'
  assert $ Prop.idempotentL w08w32 w08 w32

  assert $ Prop.adjointL w16w32 w16 w32
  assert $ Prop.closedL w16w32 w16
  assert $ Prop.kernelL w16w32 w32
  assert $ Prop.monotonicL w16w32 w16 w16' w32 w32'
  assert $ Prop.idempotentL w16w32 w16 w32
  
  assert $ Prop.adjointL i08w32 i08 w32
  assert $ Prop.closedL i08w32 i08
  assert $ Prop.kernelL i08w32 w32
  assert $ Prop.monotonicL i08w32 i08 i08' w32 w32'
  assert $ Prop.idempotentL i08w32 i08 w32

  assert $ Prop.adjointL i16w32 i16 w32
  assert $ Prop.closedL i16w32 i16
  assert $ Prop.kernelL i16w32 w32
  assert $ Prop.monotonicL i16w32 i16 i16' w32 w32'
  assert $ Prop.idempotentL i16w32 i16 w32

  assert $ Prop.adjointL i32w32 i32 w32
  assert $ Prop.closedL i32w32 i32
  assert $ Prop.kernelL i32w32 w32
  assert $ Prop.idempotentL i32w32 i32 w32
  assert $ Prop.monotonicL i32w32 i32 i32' w32 w32'

prop_connections_word64 :: Property
prop_connections_word64 = withTests 1000 . property $ do

  i08 <- forAll $ G.integral (ri @Int8)
  w08 <- forAll $ G.integral (ri @Word8)
  i16 <- forAll $ G.integral (ri @Int16)
  w16 <- forAll $ G.integral (ri @Word16)
  i32 <- forAll $ G.integral (ri @Int32)
  w32 <- forAll $ G.integral (ri @Word32)
  i64 <- forAll $ G.integral (ri @Int64)
  w64 <- forAll $ G.integral (ri @Word64)
  ixx <- forAll $ G.integral (ri @Int)

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)
  w16' <- forAll $ G.integral (ri @Word16)
  i32' <- forAll $ G.integral (ri @Int32)
  w32' <- forAll $ G.integral (ri @Word32)
  i64' <- forAll $ G.integral (ri @Int64)
  w64' <- forAll $ G.integral (ri @Word64)
  ixx' <- forAll $ G.integral (ri @Int)

  assert $ Prop.adjointL w08w64 w08 w64
  assert $ Prop.closedL w08w64 w08
  assert $ Prop.kernelL w08w64 w64
  assert $ Prop.monotonicL w08w64 w08 w08' w64 w64'
  assert $ Prop.idempotentL w08w64 w08 w64

  assert $ Prop.adjointL w16w64 w16 w64
  assert $ Prop.closedL w16w64 w16
  assert $ Prop.kernelL w16w64 w64
  assert $ Prop.monotonicL w16w64 w16 w16' w64 w64'
  assert $ Prop.idempotentL w16w64 w16 w64

  assert $ Prop.adjointL w32w64 w32 w64
  assert $ Prop.closedL w32w64 w32
  assert $ Prop.kernelL w32w64 w64
  assert $ Prop.monotonicL w32w64 w32 w32' w64 w64'
  assert $ Prop.idempotentL w32w64 w32 w64
  
  assert $ Prop.adjointL i08w64 i08 w64
  assert $ Prop.closedL i08w64 i08
  assert $ Prop.kernelL i08w64 w64
  assert $ Prop.monotonicL i08w64 i08 i08' w64 w64'
  assert $ Prop.idempotentL i08w64 i08 w64

  assert $ Prop.adjointL i16w64 i16 w64
  assert $ Prop.closedL i16w64 i16
  assert $ Prop.kernelL i16w64 w64
  assert $ Prop.monotonicL i16w64 i16 i16' w64 w64'
  assert $ Prop.idempotentL i16w64 i16 w64

  assert $ Prop.adjointL i32w64 i32 w64
  assert $ Prop.closedL i32w64 i32
  assert $ Prop.kernelL i32w64 w64
  assert $ Prop.idempotentL i32w64 i32 w64
  assert $ Prop.monotonicL i32w64 i32 i32' w64 w64'

  assert $ Prop.adjointL i64w64 i64 w64
  assert $ Prop.closedL i64w64 i64
  assert $ Prop.kernelL i64w64 w64
  assert $ Prop.idempotentL i64w64 i64 w64
  assert $ Prop.monotonicL i64w64 i64 i64' w64 w64'

  assert $ Prop.adjointL ixxw64 ixx w64
  assert $ Prop.closedL ixxw64 ixx
  assert $ Prop.kernelL ixxw64 w64
  assert $ Prop.idempotentL ixxw64 ixx w64
  assert $ Prop.monotonicL ixxw64 ixx ixx' w64 w64'

prop_connections_word :: Property
prop_connections_word = withTests 1000 . property $ do

  i08 <- forAll $ G.integral (ri @Int8)
  w08 <- forAll $ G.integral (ri @Word8)
  i16 <- forAll $ G.integral (ri @Int16)
  w16 <- forAll $ G.integral (ri @Word16)
  i32 <- forAll $ G.integral (ri @Int32)
  w32 <- forAll $ G.integral (ri @Word32)
  i64 <- forAll $ G.integral (ri @Int64)
  w64 <- forAll $ G.integral (ri @Word64)
  ixx <- forAll $ G.integral (ri @Int)
  wxx <- forAll $ G.integral (ri @Word)

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)
  w16' <- forAll $ G.integral (ri @Word16)
  i32' <- forAll $ G.integral (ri @Int32)
  w32' <- forAll $ G.integral (ri @Word32)
  i64' <- forAll $ G.integral (ri @Int64)
  w64' <- forAll $ G.integral (ri @Word64)
  ixx' <- forAll $ G.integral (ri @Int)
  wxx' <- forAll $ G.integral (ri @Word)

  assert $ Prop.adjointL w08wxx w08 wxx
  assert $ Prop.closedL w08wxx w08
  assert $ Prop.kernelL w08wxx wxx
  assert $ Prop.monotonicL w08wxx w08 w08' wxx wxx'
  assert $ Prop.idempotentL w08wxx w08 wxx

  assert $ Prop.adjointL w16wxx w16 wxx
  assert $ Prop.closedL w16wxx w16
  assert $ Prop.kernelL w16wxx wxx
  assert $ Prop.monotonicL w16wxx w16 w16' wxx wxx'
  assert $ Prop.idempotentL w16wxx w16 wxx

  assert $ Prop.adjointL w32wxx w32 wxx
  assert $ Prop.closedL w32wxx w32
  assert $ Prop.kernelL w32wxx wxx
  assert $ Prop.monotonicL w32wxx w32 w32' wxx wxx'
  assert $ Prop.idempotentL w32wxx w32 wxx

  assert $ Prop.adjoint w64wxx w64 wxx
  assert $ Prop.closed w64wxx w64
  assert $ Prop.kernel w64wxx wxx
  assert $ Prop.monotonic w64wxx w64 w64' wxx wxx'
  assert $ Prop.idempotent w64wxx w64 wxx
  
  assert $ Prop.adjointL i08wxx i08 wxx
  assert $ Prop.closedL i08wxx i08
  assert $ Prop.kernelL i08wxx wxx
  assert $ Prop.monotonicL i08wxx i08 i08' wxx wxx'
  assert $ Prop.idempotentL i08wxx i08 wxx

  assert $ Prop.adjointL i16wxx i16 wxx
  assert $ Prop.closedL i16wxx i16
  assert $ Prop.kernelL i16wxx wxx
  assert $ Prop.monotonicL i16wxx i16 i16' wxx wxx'
  assert $ Prop.idempotentL i16wxx i16 wxx

  assert $ Prop.adjointL i32wxx i32 wxx
  assert $ Prop.closedL i32wxx i32
  assert $ Prop.kernelL i32wxx wxx
  assert $ Prop.idempotentL i32wxx i32 wxx
  assert $ Prop.monotonicL i32wxx i32 i32' wxx wxx'

  assert $ Prop.adjointL i64wxx i64 wxx
  assert $ Prop.closedL i64wxx i64
  assert $ Prop.kernelL i64wxx wxx
  assert $ Prop.idempotentL i64wxx i64 wxx
  assert $ Prop.monotonicL i64wxx i64 i64' wxx wxx'

  assert $ Prop.adjointL ixxwxx ixx wxx
  assert $ Prop.closedL ixxwxx ixx
  assert $ Prop.kernelL ixxwxx wxx
  assert $ Prop.idempotentL ixxwxx ixx wxx
  assert $ Prop.monotonicL ixxwxx ixx ixx' wxx wxx'

prop_connections_natural :: Property
prop_connections_natural = withTests 1000 . property $ do

  i08 <- forAll $ G.integral (ri @Int8)
  w08 <- forAll $ G.integral (ri @Word8)
  i16 <- forAll $ G.integral (ri @Int16)
  w16 <- forAll $ G.integral (ri @Word16)
  i32 <- forAll $ G.integral (ri @Int32)
  w32 <- forAll $ G.integral (ri @Word32)
  i64 <- forAll $ G.integral (ri @Int64)
  w64 <- forAll $ G.integral (ri @Word64)
  ixx <- forAll $ G.integral (ri @Int)
  wxx <- forAll $ G.integral (ri @Word)
  int <- forAll $ G.integral ri''
  nat <- forAll $ G.integral rn

  i08' <- forAll $ G.integral (ri @Int8)
  w08' <- forAll $ G.integral (ri @Word8)
  i16' <- forAll $ G.integral (ri @Int16)
  w16' <- forAll $ G.integral (ri @Word16)
  i32' <- forAll $ G.integral (ri @Int32)
  w32' <- forAll $ G.integral (ri @Word32)
  i64' <- forAll $ G.integral (ri @Int64)
  w64' <- forAll $ G.integral (ri @Word64)
  ixx' <- forAll $ G.integral (ri @Int)
  wxx' <- forAll $ G.integral (ri @Word)
  int' <- forAll $ G.integral ri''
  nat' <- forAll $ G.integral rn

  assert $ Prop.adjointL w08nat w08 nat
  assert $ Prop.closedL w08nat w08
  assert $ Prop.kernelL w08nat nat
  assert $ Prop.monotonicL w08nat w08 w08' nat nat'
  assert $ Prop.idempotentL w08nat w08 nat

  assert $ Prop.adjointL w16nat w16 nat
  assert $ Prop.closedL w16nat w16
  assert $ Prop.kernelL w16nat nat
  assert $ Prop.monotonicL w16nat w16 w16' nat nat'
  assert $ Prop.idempotentL w16nat w16 nat

  assert $ Prop.adjointL w32nat w32 nat
  assert $ Prop.closedL w32nat w32
  assert $ Prop.kernelL w32nat nat
  assert $ Prop.monotonicL w32nat w32 w32' nat nat'
  assert $ Prop.idempotentL w32nat w32 nat

  assert $ Prop.adjointL w64nat w64 nat
  assert $ Prop.closedL w64nat w64
  assert $ Prop.kernelL w64nat nat
  assert $ Prop.monotonicL w64nat w64 w64' nat nat'
  assert $ Prop.idempotentL w64nat w64 nat

  assert $ Prop.adjointL wxxnat wxx nat
  assert $ Prop.closedL wxxnat wxx
  assert $ Prop.kernelL wxxnat nat
  assert $ Prop.monotonicL wxxnat wxx wxx' nat nat'
  assert $ Prop.idempotentL wxxnat wxx nat
  
  assert $ Prop.adjointL i08nat i08 nat
  assert $ Prop.closedL i08nat i08
  assert $ Prop.kernelL i08nat nat
  assert $ Prop.monotonicL i08nat i08 i08' nat nat'
  assert $ Prop.idempotentL i08nat i08 nat

  assert $ Prop.adjointL i16nat i16 nat
  assert $ Prop.closedL i16nat i16
  assert $ Prop.kernelL i16nat nat
  assert $ Prop.monotonicL i16nat i16 i16' nat nat'
  assert $ Prop.idempotentL i16nat i16 nat

  assert $ Prop.adjointL i32nat i32 nat
  assert $ Prop.closedL i32nat i32
  assert $ Prop.kernelL i32nat nat
  assert $ Prop.idempotentL i32nat i32 nat
  assert $ Prop.monotonicL i32nat i32 i32' nat nat'

  assert $ Prop.adjointL i64nat i64 nat
  assert $ Prop.closedL i64nat i64
  assert $ Prop.kernelL i64nat nat
  assert $ Prop.idempotentL i64nat i64 nat
  assert $ Prop.monotonicL i64nat i64 i64' nat nat'

  assert $ Prop.adjointL ixxnat ixx nat
  assert $ Prop.closedL ixxnat ixx
  assert $ Prop.kernelL ixxnat nat
  assert $ Prop.idempotentL ixxnat ixx nat
  assert $ Prop.monotonicL ixxnat ixx ixx' nat nat'

  assert $ Prop.adjointL intnat int nat
  assert $ Prop.closedL intnat int
  assert $ Prop.kernelL intnat nat
  assert $ Prop.idempotentL intnat int nat
  assert $ Prop.monotonicL intnat int int' nat nat'


tests :: IO Bool
tests = checkParallel $$(discover)
