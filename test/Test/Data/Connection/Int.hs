{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Int where

import Data.Connection.Int
import Data.Connection.Conn
import Data.Int
import Data.Word
import Hedgehog
import Prelude hiding (Bounded)
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G

prop_connectionsL :: Property
prop_connectionsL = withTests 1000 . property $ do

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
  int <- forAll $ G.integral ri'
  nat <- forAll $ G.integral rn
  mnt <- forAll $ gen_maybe (G.integral ri')

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
  int' <- forAll $ G.integral ri'
  nat' <- forAll $ G.integral rn
  mnt' <- forAll $ gen_maybe (G.integral ri')

  assert $ Prop.adjointL intnat  int nat
  --assert $ Prop.adjointL natint  nat mnt
  assert $ Prop.adjointL ixxwxx  ixx wxx
  assert $ Prop.adjointL i64w64  i64 w64
  assert $ Prop.adjointL i32w32  i32 w32
  assert $ Prop.adjointL i16w16  i16 w16
  assert $ Prop.adjointL i08w08  i08 w08

  assert $ Prop.closedL intnat  int
  --assert $ Prop.closedL natint  nat
  assert $ Prop.closedL ixxwxx  ixx
  assert $ Prop.closedL i64w64  i64
  assert $ Prop.closedL i32w32  i32
  assert $ Prop.closedL i16w16  i16
  assert $ Prop.closedL i08w08  i08

  assert $ Prop.kernelL intnat  nat
  --assert $ Prop.kernelL natint  mnt
  assert $ Prop.kernelL ixxwxx  wxx
  assert $ Prop.kernelL i64w64  w64
  assert $ Prop.kernelL i32w32  w32
  assert $ Prop.kernelL i16w16  w16
  assert $ Prop.kernelL i08w08  w08

  assert $ Prop.monotonicL intnat  int int' nat nat'
  --assert $ Prop.monotonicL natint  nat nat' mnt mnt'
  assert $ Prop.monotonicL ixxwxx  ixx ixx' wxx wxx'
  assert $ Prop.monotonicL i64w64  i64 i64' w64 w64'
  assert $ Prop.monotonicL i32w32  i32 i32' w32 w32'
  assert $ Prop.monotonicL i16w16  i16 i16' w16 w16'
  assert $ Prop.monotonicL i08w08  i08 i08' w08 w08'

  assert $ Prop.idempotentL intnat  int nat
  -- assert $ Prop.idempotentL natint  nat mnt
  assert $ Prop.idempotentL ixxwxx  ixx wxx
  assert $ Prop.idempotentL i64w64  i64 w64
  assert $ Prop.idempotentL i32w32  i32 w32
  assert $ Prop.idempotentL i16w16  i16 w16
  assert $ Prop.idempotentL i08w08  i08 w08

prop_connectionsR :: Property
prop_connectionsR = withTests 1000 . property $ do

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
  int <- forAll $ G.integral ri'
  nat <- forAll $ G.integral rn
  mnt <- forAll $ gen_maybe (G.integral ri')

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
  int' <- forAll $ G.integral ri'
  nat' <- forAll $ G.integral rn
  mnt' <- forAll $ gen_maybe (G.integral ri')

  assert $ Prop.adjointR (swapR intnat) nat int
  -- assert $ Prop.adjointR (swapR natint) mnt nat
  assert $ Prop.adjointR (swapR ixxwxx) wxx ixx
  assert $ Prop.adjointR (swapR i64w64) w64 i64
  assert $ Prop.adjointR (swapR i32w32) w32 i32
  assert $ Prop.adjointR (swapR i16w16) w16 i16
  assert $ Prop.adjointR (swapR i08w08) w08 i08

  assert $ Prop.closedR (swapR intnat) nat
  --assert $ Prop.closedR (swapR natint) mnt
  assert $ Prop.closedR (swapR ixxwxx) wxx
  assert $ Prop.closedR (swapR i64w64) w64
  assert $ Prop.closedR (swapR i32w32) w32
  assert $ Prop.closedR (swapR i16w16) w16
  assert $ Prop.closedR (swapR i08w08) w08

  assert $ Prop.kernelR (swapR intnat) int
  --assert $ Prop.kernelR (swapR natint) nat
  assert $ Prop.kernelR (swapR ixxwxx) ixx
  assert $ Prop.kernelR (swapR i64w64) i64
  assert $ Prop.kernelR (swapR i32w32) i32
  assert $ Prop.kernelR (swapR i16w16) i16
  assert $ Prop.kernelR (swapR i08w08) i08

  assert $ Prop.monotonicR (swapR intnat)  nat nat' int int'
  -- assert $ Prop.monotonicR (swapR natint)  mnt mnt' nat nat'
  assert $ Prop.monotonicR (swapR ixxwxx)  wxx wxx' ixx ixx'
  assert $ Prop.monotonicR (swapR i64w64)  w64 w64' i64 i64'
  assert $ Prop.monotonicR (swapR i32w32)  w32 w32' i32 i32'
  assert $ Prop.monotonicR (swapR i16w16)  w16 w16' i16 i16'
  assert $ Prop.monotonicR (swapR i08w08)  w08 w08' i08 i08'

  assert $ Prop.idempotentR (swapR intnat) nat int
  -- assert $ Prop.idempotentR (swapR natint) mnt nat
  assert $ Prop.idempotentR (swapR ixxwxx) wxx ixx
  assert $ Prop.idempotentR (swapR i64w64) w64 i64
  assert $ Prop.idempotentR (swapR i32w32) w32 i32
  assert $ Prop.idempotentR (swapR i16w16) w16 i16
  assert $ Prop.idempotentR (swapR i08w08) w08 i08

tests :: IO Bool
tests = checkParallel $$(discover)
