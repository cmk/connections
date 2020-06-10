{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Int where

import Data.Connection.Int
import Data.Connection.Type
import Data.Int
import Data.Word
import Hedgehog
import Prelude hiding (Bounded)
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
  ixx <- forAll $ G.integral (ri @Int)
  wxx <- forAll $ G.integral (ri @Word)
  int <- forAll $ G.integral ri'
  nat <- forAll $ G.integral rn
  mnt <- forAll $ gen_lifted (G.integral ri')

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
  mnt' <- forAll $ gen_lifted (G.integral ri')

  assert $ Prop.adjoint intnat  int nat
  assert $ Prop.adjoint natint  nat mnt
  assert $ Prop.adjoint ixxwxx  ixx wxx
  assert $ Prop.adjoint i64w64  i64 w64
  assert $ Prop.adjoint i32w32  i32 w32
  assert $ Prop.adjoint i16w16  i16 w16
  assert $ Prop.adjoint i08w08  i08 w08

  assert $ Prop.closed intnat  int
  assert $ Prop.closed natint  nat
  assert $ Prop.closed ixxwxx  ixx
  assert $ Prop.closed i64w64  i64
  assert $ Prop.closed i32w32  i32
  assert $ Prop.closed i16w16  i16
  assert $ Prop.closed i08w08  i08

  assert $ Prop.kernel intnat  nat
  assert $ Prop.kernel natint  mnt
  assert $ Prop.kernel ixxwxx  wxx
  assert $ Prop.kernel i64w64  w64
  assert $ Prop.kernel i32w32  w32
  assert $ Prop.kernel i16w16  w16
  assert $ Prop.kernel i08w08  w08

  assert $ Prop.monotoneL intnat  int int'
  assert $ Prop.monotoneL natint  nat nat'
  assert $ Prop.monotoneL ixxwxx  ixx ixx'
  assert $ Prop.monotoneL i64w64  i64 i64'
  assert $ Prop.monotoneL i32w32  i32 i32'
  assert $ Prop.monotoneL i16w16  i16 i16'
  assert $ Prop.monotoneL i08w08  i08 i08'

  assert $ Prop.monotoneR intnat  nat nat'
  assert $ Prop.monotoneR natint  mnt mnt'
  assert $ Prop.monotoneR ixxwxx  wxx wxx'
  assert $ Prop.monotoneR i64w64  w64 w64'
  assert $ Prop.monotoneR i32w32  w32 w32'
  assert $ Prop.monotoneR i16w16  w16 w16'
  assert $ Prop.monotoneR i08w08  w08 w08'

  assert $ Prop.projectiveL intnat  int
  assert $ Prop.projectiveL natint  nat
  assert $ Prop.projectiveL ixxwxx  ixx
  assert $ Prop.projectiveL i64w64  i64
  assert $ Prop.projectiveL i32w32  i32
  assert $ Prop.projectiveL i16w16  i16
  assert $ Prop.projectiveL i08w08  i08

  assert $ Prop.projectiveR intnat  nat
  assert $ Prop.projectiveR natint  mnt
  assert $ Prop.projectiveR ixxwxx  wxx
  assert $ Prop.projectiveR i64w64  w64
  assert $ Prop.projectiveR i32w32  w32
  assert $ Prop.projectiveR i16w16  w16
  assert $ Prop.projectiveR i08w08  w08

tests :: IO Bool
tests = checkParallel $$(discover)
