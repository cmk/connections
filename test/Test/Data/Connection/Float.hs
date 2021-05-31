{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Test.Data.Connection.Float where

import Data.Connection.Float
import qualified Data.Connection.Property as Prop
import Data.Int
import Data.Word
import Hedgehog
import qualified Hedgehog.Gen as G
import Test.Data.Connection

prop_connection_f32w08 :: Property
prop_connection_f32w08 = withTests 1000 . property $ do
    x <- forAll f32
    x' <- forAll f32
    y <- forAll $ gen_extended $ G.integral (ri @Word8)
    y' <- forAll $ gen_extended $ G.integral (ri @Word8)

    assert $ Prop.adjoint f32w08 x y
    assert $ Prop.closed f32w08 x
    assert $ Prop.kernel f32w08 y
    assert $ Prop.monotonic f32w08 x x' y y'
    assert $ Prop.idempotent f32w08 x y

prop_connection_f32w16 :: Property
prop_connection_f32w16 = withTests 1000 . property $ do
    x <- forAll f32
    x' <- forAll f32
    y <- forAll $ gen_extended $ G.integral (ri @Word16)
    y' <- forAll $ gen_extended $ G.integral (ri @Word16)

    assert $ Prop.adjoint f32w16 x y
    assert $ Prop.closed f32w16 x
    assert $ Prop.kernel f32w16 y
    assert $ Prop.monotonic f32w16 x x' y y'
    assert $ Prop.idempotent f32w16 x y

prop_connection_f32w32 :: Property
prop_connection_f32w32 = withTests 1000 . property $ do
    x <- forAll f32
    x' <- forAll f32
    y <- forAll $ gen_extended $ G.integral (ri @Word32)
    y' <- forAll $ gen_extended $ G.integral (ri @Word32)

    assert $ Prop.adjointL f32w32 x y
    assert $ Prop.closedL f32w32 x
    assert $ Prop.kernelL f32w32 y
    assert $ Prop.monotonicL f32w32 x x' y y'
    assert $ Prop.idempotentL f32w32 x y

prop_connection_f32w64 :: Property
prop_connection_f32w64 = withTests 1000 . property $ do
    x <- forAll f32
    x' <- forAll f32
    y <- forAll $ gen_extended $ G.integral (ri @Word64)
    y' <- forAll $ gen_extended $ G.integral (ri @Word64)

    assert $ Prop.adjointL f32w64 x y
    assert $ Prop.closedL f32w64 x
    assert $ Prop.kernelL f32w64 y
    assert $ Prop.monotonicL f32w64 x x' y y'
    assert $ Prop.idempotentL f32w64 x y

prop_connection_f32nat :: Property
prop_connection_f32nat = withTests 1000 . property $ do
    x <- forAll f32
    x' <- forAll f32
    y <- forAll $ gen_extended $ G.integral rn
    y' <- forAll $ gen_extended $ G.integral rn

    assert $ Prop.adjointL f32nat x y
    assert $ Prop.closedL f32nat x
    assert $ Prop.kernelL f32nat y
    assert $ Prop.monotonicL f32nat x x' y y'
    assert $ Prop.idempotentL f32nat x y

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

prop_connection_ratf32 :: Property
prop_connection_ratf32 = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll f32
    y' <- forAll f32

    assert $ Prop.adjoint (ratf32) x y
    assert $ Prop.closed (ratf32) x
    assert $ Prop.kernel (ratf32) y
    assert $ Prop.monotonic (ratf32) x x' y y'
    assert $ Prop.idempotent (ratf32) x y

prop_connection_f64w08 :: Property
prop_connection_f64w08 = withTests 1000 . property $ do
    x <- forAll f64
    x' <- forAll f64
    y <- forAll $ gen_extended $ G.integral (ri @Word8)
    y' <- forAll $ gen_extended $ G.integral (ri @Word8)

    assert $ Prop.adjoint f64w08 x y
    assert $ Prop.closed f64w08 x
    assert $ Prop.kernel f64w08 y
    assert $ Prop.monotonic f64w08 x x' y y'
    assert $ Prop.idempotent f64w08 x y

prop_connection_f64w16 :: Property
prop_connection_f64w16 = withTests 1000 . property $ do
    x <- forAll f64
    x' <- forAll f64
    y <- forAll $ gen_extended $ G.integral (ri @Word16)
    y' <- forAll $ gen_extended $ G.integral (ri @Word16)

    assert $ Prop.adjoint f64w16 x y
    assert $ Prop.closed f64w16 x
    assert $ Prop.kernel f64w16 y
    assert $ Prop.monotonic f64w16 x x' y y'
    assert $ Prop.idempotent f64w16 x y

prop_connection_f64w32 :: Property
prop_connection_f64w32 = withTests 1000 . property $ do
    x <- forAll f64
    x' <- forAll f64
    y <- forAll $ gen_extended $ G.integral (ri @Word32)
    y' <- forAll $ gen_extended $ G.integral (ri @Word32)

    assert $ Prop.adjoint f64w32 x y
    assert $ Prop.closed f64w32 x
    assert $ Prop.kernel f64w32 y
    assert $ Prop.monotonic f64w32 x x' y y'
    assert $ Prop.idempotent f64w32 x y

prop_connection_f64w64 :: Property
prop_connection_f64w64 = withTests 1000 . property $ do
    x <- forAll f64
    x' <- forAll f64
    y <- forAll $ gen_extended $ G.integral (ri @Word64)
    y' <- forAll $ gen_extended $ G.integral (ri @Word64)

    assert $ Prop.adjointL f64w64 x y
    assert $ Prop.closedL f64w64 x
    assert $ Prop.kernelL f64w64 y
    assert $ Prop.monotonicL f64w64 x x' y y'
    assert $ Prop.idempotentL f64w64 x y

prop_connection_f64nat :: Property
prop_connection_f64nat = withTests 1000 . property $ do
    x <- forAll f64
    x' <- forAll f64
    y <- forAll $ gen_extended $ G.integral rn
    y' <- forAll $ gen_extended $ G.integral rn

    assert $ Prop.adjointL f64nat x y
    assert $ Prop.closedL f64nat x
    assert $ Prop.kernelL f64nat y
    assert $ Prop.monotonicL f64nat x x' y y'
    assert $ Prop.idempotentL f64nat x y

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

prop_connection_ratf64 :: Property
prop_connection_ratf64 = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll f64
    y' <- forAll f64

    assert $ Prop.adjoint (ratf64) x y
    assert $ Prop.closed (ratf64) x
    assert $ Prop.kernel (ratf64) y
    assert $ Prop.monotonic (ratf64) x x' y y'
    assert $ Prop.idempotent (ratf64) x y

tests :: IO Bool
tests = checkParallel $$(discover)
