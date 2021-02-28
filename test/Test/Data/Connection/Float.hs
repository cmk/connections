{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
module Test.Data.Connection.Float where

import Data.Connection.Conn
import Data.Connection.Float
import Data.Int
import Data.Fixed
import Data.Order

import Hedgehog
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G


prop_connection_f32i08 :: Property
prop_connection_f32i08 = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_extended $ G.integral (ri @Int8)
  y' <- forAll $ gen_extended $ G.integral (ri @Int8)

  assert $ Prop.adjoint f32i08 x y
  assert $ Prop.closed f32i08 x
  assert $ Prop.kernel f32i08 y
  assert $ Prop.monotonic f32i08 x x' y y'
  assert $ Prop.idempotent f32i08 x y

prop_connection_f32i16 :: Property
prop_connection_f32i16 = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_extended $ G.integral (ri @Int16)
  y' <- forAll $ gen_extended $ G.integral (ri @Int16)

  assert $ Prop.adjoint f32i16 x y
  assert $ Prop.closed f32i16 x
  assert $ Prop.kernel f32i16 y
  assert $ Prop.monotonic f32i16 x x' y y'
  assert $ Prop.idempotent f32i16 x y

prop_connection_f32i32 :: Property
prop_connection_f32i32 = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_extended $ G.integral (ri @Int32)
  y' <- forAll $ gen_extended $ G.integral (ri @Int32)

  assert $ Prop.adjointL f32i32 x y
  assert $ Prop.closedL f32i32 x
  assert $ Prop.kernelL f32i32 y
  assert $ Prop.monotonicL f32i32 x x' y y'
  assert $ Prop.idempotentL f32i32 x y

prop_connection_f32i64 :: Property
prop_connection_f32i64 = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_extended $ G.integral (ri @Int64)
  y' <- forAll $ gen_extended $ G.integral (ri @Int64)

  assert $ Prop.adjointL f32i64 x y
  assert $ Prop.closedL f32i64 x
  assert $ Prop.kernelL f32i64 y
  assert $ Prop.monotonicL f32i64 x x' y y'
  assert $ Prop.idempotentL f32i64 x y

prop_connection_f32ixx :: Property
prop_connection_f32ixx = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_extended $ G.integral (ri @Int)
  y' <- forAll $ gen_extended $ G.integral (ri @Int)

  assert $ Prop.adjointL f32ixx x y
  assert $ Prop.closedL f32ixx x
  assert $ Prop.kernelL f32ixx y
  assert $ Prop.monotonicL f32ixx x x' y y'
  assert $ Prop.idempotentL f32ixx x y

prop_connection_f32int :: Property
prop_connection_f32int = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_extended $ G.integral ri'
  y' <- forAll $ gen_extended $ G.integral ri'

  assert $ Prop.adjointL f32int x y
  assert $ Prop.closedL f32int x
  assert $ Prop.kernelL f32int y
  assert $ Prop.monotonicL f32int x x' y y'
  assert $ Prop.idempotentL f32int x y

prop_connection_f64i08 :: Property
prop_connection_f64i08 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int8)
  y' <- forAll $ gen_extended $ G.integral (ri @Int8)

  assert $ Prop.adjoint f64i08 x y
  assert $ Prop.closed f64i08 x
  assert $ Prop.kernel f64i08 y
  assert $ Prop.monotonic f64i08 x x' y y'
  assert $ Prop.idempotent f64i08 x y

prop_connection_f64i16 :: Property
prop_connection_f64i16 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int16)
  y' <- forAll $ gen_extended $ G.integral (ri @Int16)

  assert $ Prop.adjoint f64i16 x y
  assert $ Prop.closed f64i16 x
  assert $ Prop.kernel f64i16 y
  assert $ Prop.monotonic f64i16 x x' y y'
  assert $ Prop.idempotent f64i16 x y

prop_connection_f64i32 :: Property
prop_connection_f64i32 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int32)
  y' <- forAll $ gen_extended $ G.integral (ri @Int32)

  assert $ Prop.adjoint f64i32 x y
  assert $ Prop.closed f64i32 x
  assert $ Prop.kernel f64i32 y
  assert $ Prop.monotonic f64i32 x x' y y'
  assert $ Prop.idempotent f64i32 x y

prop_connection_f64i64 :: Property
prop_connection_f64i64 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int64)
  y' <- forAll $ gen_extended $ G.integral (ri @Int64)

  assert $ Prop.adjointL f64i64 x y
  assert $ Prop.closedL f64i64 x
  assert $ Prop.kernelL f64i64 y
  assert $ Prop.monotonicL f64i64 x x' y y'
  assert $ Prop.idempotentL f64i64 x y

prop_connection_f64ixx :: Property
prop_connection_f64ixx = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int)
  y' <- forAll $ gen_extended $ G.integral (ri @Int)

  assert $ Prop.adjointL f64ixx x y
  assert $ Prop.closedL f64ixx x
  assert $ Prop.kernelL f64ixx y
  assert $ Prop.monotonicL f64ixx x x' y y'
  assert $ Prop.idempotentL f64ixx x y

prop_connection_f64int :: Property
prop_connection_f64int = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral ri'
  y' <- forAll $ gen_extended $ G.integral ri'

  assert $ Prop.adjointL f64int x y
  assert $ Prop.closedL f64int x
  assert $ Prop.kernelL f64int y
  assert $ Prop.monotonicL f64int x x' y y'
  assert $ Prop.idempotentL f64int x y

prop_connection_f64f32 :: Property
prop_connection_f64f32 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll f32
  y' <- forAll f32

  assert $ Prop.adjoint (f64f32) x y
  assert $ Prop.closed (f64f32) x
  assert $ Prop.kernel (f64f32) y
  assert $ Prop.monotonic (f64f32) x x' y y'
  assert $ Prop.idempotent (f64f32) x y

tests :: IO Bool
tests = checkParallel $$(discover)
