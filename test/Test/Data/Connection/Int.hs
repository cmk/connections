{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Int where

import Data.Int
import Data.Word
import Data.Prd
import Data.Prd.Nan
import Data.Semilattice.Bounded
import Data.Connection
import Data.Connection.Int
import Numeric.Natural
import Test.Data.Connection

import qualified Data.Connection.Property as Prop

import Hedgehog
import qualified Hedgehog.Gen as G

import Prelude hiding (Bounded)

prop_connections_f32i32 :: Property
prop_connections_f32i32 = withTests 10000 . property $ do
  x <- forAll gen_f32
  y <- forAll (gen_nan $ G.integral ri)
  x' <- forAll gen_f32
  y' <- forAll (gen_nan $ G.integral ri)
 
  assert $ Prop.connection f32i32 x y
  assert $ Prop.connection i32f32 y x
  assert $ Prop.monotonel f32i32 x x'
  assert $ Prop.monotonel i32f32 y y'
  assert $ Prop.monotoner f32i32 y y'
  assert $ Prop.monotoner i32f32 x x'
  assert $ Prop.closed f32i32 x
  assert $ Prop.closed i32f32 y
  assert $ Prop.kernel i32f32 x
  assert $ Prop.kernel f32i32 y

prop_connections_f64i64 :: Property
prop_connections_f64i64 = withTests 10000 . property $ do
  x <- forAll gen_f64
  y <- forAll (gen_nan $ G.integral ri)
  x' <- forAll gen_f64
  y' <- forAll (gen_nan $ G.integral ri)
 
  assert $ Prop.connection f64i64 x y
  assert $ Prop.connection i64f64 y x
  assert $ Prop.monotonel f64i64 x x'
  assert $ Prop.monotonel i64f64 y y'
  assert $ Prop.monotoner f64i64 y y'
  assert $ Prop.monotoner i64f64 x x'
  assert $ Prop.closed f64i64 x
  assert $ Prop.closed i64f64 y
  assert $ Prop.kernel i64f64 x
  assert $ Prop.kernel f64i64 y

prop_connections_int :: Property
prop_connections_int = withTests 10000 . property $ do

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
  int <- forAll $ G.integral rint
  nat <- forAll $ G.integral rn
  mnt <- forAll $ gen_may (G.integral rint)
  inf <- forAll $ gen_inf (G.integral rint)

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
  int' <- forAll $ G.integral rint
  nat' <- forAll $ G.integral rn
  mnt' <- forAll $ gen_may (G.integral rint)
  inf' <- forAll $ gen_inf (G.integral rint)

  assert $ Prop.connection intnat  int nat
  assert $ Prop.connection natint  nat mnt
  assert $ Prop.connection ixxwxx  ixx wxx
  assert $ Prop.connection (tripl i64int) i64 inf
  assert $ Prop.connection (tripr i64int) inf i64
  assert $ Prop.connection i64w64  i64 w64
  assert $ Prop.connection i64w64' i64 w64
  assert $ Prop.connection (tripl i32int) i32 inf
  assert $ Prop.connection (tripr i32int) inf i32
  assert $ Prop.connection i32i64  i32 i64
  assert $ Prop.connection i32w32  i32 w32
  assert $ Prop.connection i32w32' i32 w32
  assert $ Prop.connection (tripl i16int) i16 inf
  assert $ Prop.connection (tripr i16int) inf i16
  assert $ Prop.connection i16i64  i16 i64
  assert $ Prop.connection i16i32  i16 i32
  assert $ Prop.connection i16w16  i16 w16
  assert $ Prop.connection i16w16' i16 w16
  assert $ Prop.connection (tripl i08int) i08 inf
  assert $ Prop.connection (tripr i08int) inf i08
  assert $ Prop.connection i08i64  i08 i64
  assert $ Prop.connection i08i32  i08 i32
  assert $ Prop.connection i08i16  i08 i16
  assert $ Prop.connection i08w08  i08 w08
  assert $ Prop.connection i08w08' i08 w08

  assert $ Prop.monotonel intnat  int int'
  assert $ Prop.monotonel natint  nat nat'
  assert $ Prop.monotonel ixxwxx  ixx ixx'
  assert $ Prop.monotonel (tripl i64int) i64 i64'
  assert $ Prop.monotonel (tripr i64int) inf inf'
  assert $ Prop.monotonel i64w64  i64 i64'
  assert $ Prop.monotonel i64w64' i64 i64'
  assert $ Prop.monotonel (tripl i32int) i32 i32'
  assert $ Prop.monotonel (tripr i32int) inf inf'
  assert $ Prop.monotonel i32i64  i32 i32'
  assert $ Prop.monotonel i32w32  i32 i32'
  assert $ Prop.monotonel i32w32' i32 i32'
  assert $ Prop.monotonel (tripl i16int) i16 i16'
  assert $ Prop.monotonel (tripr i16int) inf inf'
  assert $ Prop.monotonel i16i64  i16 i16'
  assert $ Prop.monotonel i16i32  i16 i16'
  assert $ Prop.monotonel i16w16  i16 i16'
  assert $ Prop.monotonel i16w16' i16 i16'
  assert $ Prop.monotonel (tripl i08int) i08 i08'
  assert $ Prop.monotonel (tripr i08int) inf inf'
  assert $ Prop.monotonel i08i64  i08 i08'
  assert $ Prop.monotonel i08i32  i08 i08'
  assert $ Prop.monotonel i08i16  i08 i08'
  assert $ Prop.monotonel i08w08  i08 i08'
  assert $ Prop.monotonel i08w08' i08 i08'

  assert $ Prop.monotoner intnat  nat nat'
  assert $ Prop.monotoner natint  mnt mnt'
  assert $ Prop.monotoner ixxwxx  wxx wxx'
  assert $ Prop.monotoner (tripl i64int) inf inf'
  assert $ Prop.monotoner (tripr i64int) i64 i64'
  assert $ Prop.monotoner i64w64  w64 w64'
  assert $ Prop.monotoner i64w64' w64 w64'
  assert $ Prop.monotoner (tripl i32int) inf inf'
  assert $ Prop.monotoner (tripr i32int) i32 i32'
  assert $ Prop.monotoner i32i64  i64 i64'
  assert $ Prop.monotoner i32w32  w32 w32'
  assert $ Prop.monotoner i32w32' w32 w32'
  assert $ Prop.monotoner (tripl i16int) inf inf'
  assert $ Prop.monotoner (tripr i16int) i16 i16'
  assert $ Prop.monotoner i16i64  i64 i64'
  assert $ Prop.monotoner i16i32  i32 i32'
  assert $ Prop.monotoner i16w16  w16 w16'
  assert $ Prop.monotoner i16w16' w16 w16'
  assert $ Prop.monotoner (tripl i08int) inf inf'
  assert $ Prop.monotoner (tripr i08int) i08 i08'
  assert $ Prop.monotoner i08i64  i64 i64'
  assert $ Prop.monotoner i08i32  i32 i32'
  assert $ Prop.monotoner i08i16  i16 i16'
  assert $ Prop.monotoner i08w08  w08 w08'
  assert $ Prop.monotoner i08w08' w08 w08'

  assert $ Prop.closed intnat  int
  assert $ Prop.closed natint  nat
  assert $ Prop.closed ixxwxx  ixx
  assert $ Prop.closed (tripl i64int) i64
  assert $ Prop.closed (tripr i64int) inf
  assert $ Prop.closed i64w64  i64
  assert $ Prop.closed i64w64' i64
  assert $ Prop.closed (tripl i32int) i32
  assert $ Prop.closed (tripr i32int) inf
  assert $ Prop.closed i32i64  i32
  assert $ Prop.closed i32w32  i32
  assert $ Prop.closed i32w32' i32
  assert $ Prop.closed (tripl i16int) i16
  assert $ Prop.closed (tripr i16int) inf
  assert $ Prop.closed i16i64  i16
  assert $ Prop.closed i16i32  i16
  assert $ Prop.closed i16w16  i16
  assert $ Prop.closed i16w16' i16
  assert $ Prop.closed (tripl i08int) i08
  assert $ Prop.closed (tripr i08int) inf
  assert $ Prop.closed i08i64  i08
  assert $ Prop.closed i08i32  i08
  assert $ Prop.closed i08i16  i08
  assert $ Prop.closed i08w08  i08
  assert $ Prop.closed i08w08' i08

  assert $ Prop.kernel intnat  nat
  assert $ Prop.kernel natint  mnt
  assert $ Prop.kernel ixxwxx  wxx
  assert $ Prop.kernel (tripl i64int) inf
  assert $ Prop.kernel (tripr i64int) i64
  assert $ Prop.kernel i64w64' w64
  assert $ Prop.kernel i64w64  w64
  assert $ Prop.kernel (tripl i32int) inf
  assert $ Prop.kernel (tripr i32int) i32
  assert $ Prop.kernel i32i64  i64
  assert $ Prop.kernel i32w32' w32
  assert $ Prop.kernel i32w32  w32
  assert $ Prop.kernel (tripl i16int) inf
  assert $ Prop.kernel (tripr i16int) i16
  assert $ Prop.kernel i16i64  i64
  assert $ Prop.kernel i16i32  i32
  assert $ Prop.kernel i16w16' w16
  assert $ Prop.kernel i16w16  w16
  assert $ Prop.kernel (tripl i08int) inf
  assert $ Prop.kernel (tripr i08int) i08
  assert $ Prop.kernel i08i64  i64
  assert $ Prop.kernel i08i32  i32
  assert $ Prop.kernel i08i16  i16
  assert $ Prop.kernel i08w08' w08
  assert $ Prop.kernel i08w08  w08

tests :: IO Bool
tests = checkParallel $$(discover)
