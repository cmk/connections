{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Int where

import Data.Connection
import Data.Connection.Int
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
  mnt <- forAll $ gen_bot (G.integral ri')
  inf <- forAll $ gen_bnd (G.integral ri')

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
  mnt' <- forAll $ gen_bot (G.integral ri')
  inf' <- forAll $ gen_bnd (G.integral ri')

  assert $ Prop.connection intnat  int nat
  assert $ Prop.connection natint  nat mnt
  assert $ Prop.connection ixxwxx  ixx wxx
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
  assert $ Prop.connection (tripl i64int) i64 inf
  assert $ Prop.connection (tripr i64int) inf i64
  assert $ Prop.connection (tripl i32int) i32 inf
  assert $ Prop.connection (tripr i32int) inf i32
  assert $ Prop.connection (tripl i16int) i16 inf
  assert $ Prop.connection (tripr i16int) inf i16
  assert $ Prop.connection (tripl i08int) i08 inf
  assert $ Prop.connection (tripr i08int) inf i08

  assert $ Prop.closed intnat  int
  assert $ Prop.closed natint  nat
  assert $ Prop.closed ixxwxx  ixx
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
  assert $ Prop.closed (tripl i64int) i64
  assert $ Prop.closed (tripr i64int) inf
  assert $ Prop.closed (tripl i32int) i32
  assert $ Prop.closed (tripr i32int) inf
  assert $ Prop.closed (tripl i16int) i16
  assert $ Prop.closed (tripr i16int) inf
  assert $ Prop.closed (tripl i08int) i08
  assert $ Prop.closed (tripr i08int) inf

  assert $ Prop.kernel intnat  nat
  assert $ Prop.kernel natint  mnt
  assert $ Prop.kernel ixxwxx  wxx
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
  assert $ Prop.kernel (tripl i64int) inf
  assert $ Prop.kernel (tripr i64int) i64
  assert $ Prop.kernel (tripl i32int) inf
  assert $ Prop.kernel (tripr i32int) i32
  assert $ Prop.kernel (tripl i16int) inf
  assert $ Prop.kernel (tripr i16int) i16
  assert $ Prop.kernel (tripl i08int) inf
  assert $ Prop.kernel (tripr i08int) i08

  assert $ Prop.monotonel intnat  int int'
  assert $ Prop.monotonel natint  nat nat'
  assert $ Prop.monotonel ixxwxx  ixx ixx'
  assert $ Prop.monotonel i64w64  i64 i64'
  assert $ Prop.monotonel i64w64' i64 i64'
  assert $ Prop.monotonel i32i64  i32 i32'
  assert $ Prop.monotonel i32w32  i32 i32'
  assert $ Prop.monotonel i32w32' i32 i32'
  assert $ Prop.monotonel i16i64  i16 i16'
  assert $ Prop.monotonel i16i32  i16 i16'
  assert $ Prop.monotonel i16w16  i16 i16'
  assert $ Prop.monotonel i16w16' i16 i16'
  assert $ Prop.monotonel i08i64  i08 i08'
  assert $ Prop.monotonel i08i32  i08 i08'
  assert $ Prop.monotonel i08i16  i08 i08'
  assert $ Prop.monotonel i08w08  i08 i08'
  assert $ Prop.monotonel i08w08' i08 i08'
  assert $ Prop.monotonel (tripl i64int) i64 i64'
  assert $ Prop.monotonel (tripr i64int) inf inf'
  assert $ Prop.monotonel (tripl i32int) i32 i32'
  assert $ Prop.monotonel (tripr i32int) inf inf'
  assert $ Prop.monotonel (tripl i16int) i16 i16'
  assert $ Prop.monotonel (tripr i16int) inf inf'
  assert $ Prop.monotonel (tripl i08int) i08 i08'
  assert $ Prop.monotonel (tripr i08int) inf inf'

  assert $ Prop.monotoner intnat  nat nat'
  assert $ Prop.monotoner natint  mnt mnt'
  assert $ Prop.monotoner ixxwxx  wxx wxx'
  assert $ Prop.monotoner i64w64  w64 w64'
  assert $ Prop.monotoner i64w64' w64 w64'
  assert $ Prop.monotoner i32i64  i64 i64'
  assert $ Prop.monotoner i32w32  w32 w32'
  assert $ Prop.monotoner i32w32' w32 w32'
  assert $ Prop.monotoner i16i64  i64 i64'
  assert $ Prop.monotoner i16i32  i32 i32'
  assert $ Prop.monotoner i16w16  w16 w16'
  assert $ Prop.monotoner i16w16' w16 w16'
  assert $ Prop.monotoner i08i64  i64 i64'
  assert $ Prop.monotoner i08i32  i32 i32'
  assert $ Prop.monotoner i08i16  i16 i16'
  assert $ Prop.monotoner i08w08  w08 w08'
  assert $ Prop.monotoner i08w08' w08 w08'
  assert $ Prop.monotoner (tripl i64int) inf inf'
  assert $ Prop.monotoner (tripr i64int) i64 i64'
  assert $ Prop.monotoner (tripl i32int) inf inf'
  assert $ Prop.monotoner (tripr i32int) i32 i32'
  assert $ Prop.monotoner (tripl i16int) inf inf'
  assert $ Prop.monotoner (tripr i16int) i16 i16'
  assert $ Prop.monotoner (tripl i08int) inf inf'
  assert $ Prop.monotoner (tripr i08int) i08 i08'

  assert $ Prop.projectivel intnat  int
  assert $ Prop.projectivel natint  nat
  assert $ Prop.projectivel ixxwxx  ixx
  assert $ Prop.projectivel i64w64  i64
  assert $ Prop.projectivel i64w64' i64
  assert $ Prop.projectivel i32i64  i32
  assert $ Prop.projectivel i32w32  i32
  assert $ Prop.projectivel i32w32' i32
  assert $ Prop.projectivel i16i64  i16
  assert $ Prop.projectivel i16i32  i16
  assert $ Prop.projectivel i16w16  i16
  assert $ Prop.projectivel i16w16' i16
  assert $ Prop.projectivel i08i64  i08
  assert $ Prop.projectivel i08i32  i08
  assert $ Prop.projectivel i08i16  i08
  assert $ Prop.projectivel i08w08  i08
  assert $ Prop.projectivel i08w08' i08
  assert $ Prop.projectivel (tripl i64int) i64
  assert $ Prop.projectivel (tripr i64int) inf
  assert $ Prop.projectivel (tripl i32int) i32
  assert $ Prop.projectivel (tripr i32int) inf
  assert $ Prop.projectivel (tripl i16int) i16
  assert $ Prop.projectivel (tripr i16int) inf
  assert $ Prop.projectivel (tripl i08int) i08
  assert $ Prop.projectivel (tripr i08int) inf

  assert $ Prop.projectiver intnat  nat
  assert $ Prop.projectiver natint  mnt
  assert $ Prop.projectiver ixxwxx  wxx
  assert $ Prop.projectiver i64w64' w64
  assert $ Prop.projectiver i64w64  w64
  assert $ Prop.projectiver i32i64  i64
  assert $ Prop.projectiver i32w32' w32
  assert $ Prop.projectiver i32w32  w32
  assert $ Prop.projectiver i16i64  i64
  assert $ Prop.projectiver i16i32  i32
  assert $ Prop.projectiver i16w16' w16
  assert $ Prop.projectiver i16w16  w16
  assert $ Prop.projectiver i08i64  i64
  assert $ Prop.projectiver i08i32  i32
  assert $ Prop.projectiver i08i16  i16
  assert $ Prop.projectiver i08w08' w08
  assert $ Prop.projectiver i08w08  w08
  assert $ Prop.projectiver (tripl i64int) inf
  assert $ Prop.projectiver (tripr i64int) i64
  assert $ Prop.projectiver (tripl i32int) inf
  assert $ Prop.projectiver (tripr i32int) i32
  assert $ Prop.projectiver (tripl i16int) inf
  assert $ Prop.projectiver (tripr i16int) i16
  assert $ Prop.projectiver (tripl i08int) inf
  assert $ Prop.projectiver (tripr i08int) i08

tests :: IO Bool
tests = checkParallel $$(discover)
