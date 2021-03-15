{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Test.Data.Connection.Ratio where

import qualified Data.Connection.Property as Prop
import Data.Connection.Ratio
import Data.Fixed
import Data.Int
import Data.Word
import Hedgehog
import qualified Hedgehog.Gen as G
import Test.Data.Connection

prop_connection_ratf06 :: Property
prop_connection_ratf06 = withTests 1000 . property $ do
    x <- forAll rat
    x' <- forAll rat
    y <- forAll $ gen_extended fxx
    y' <- forAll $ gen_extended fxx

    assert $ Prop.adjoint (ratfix @E6) x y
    assert $ Prop.closed (ratfix @E6) x
    assert $ Prop.kernel (ratfix @E6) y
    assert $ Prop.monotonic (ratfix @E6) x x' y y'
    assert $ Prop.idempotent (ratfix @E6) x y

prop_connection_ratf09 :: Property
prop_connection_ratf09 = withTests 1000 . property $ do
    x <- forAll rat
    x' <- forAll rat
    y <- forAll $ gen_extended fxx
    y' <- forAll $ gen_extended fxx

    assert $ Prop.adjoint (ratfix @E9) x y
    assert $ Prop.closed (ratfix @E9) x
    assert $ Prop.kernel (ratfix @E9) y
    assert $ Prop.monotonic (ratfix @E9) x x' y y'
    assert $ Prop.idempotent (ratfix @E9) x y

prop_connection_ratf12 :: Property
prop_connection_ratf12 = withTests 1000 . property $ do
    x <- forAll rat
    x' <- forAll rat
    y <- forAll $ gen_extended fxx
    y' <- forAll $ gen_extended fxx

    assert $ Prop.adjoint (ratfix @E12) x y
    assert $ Prop.closed (ratfix @E12) x
    assert $ Prop.kernel (ratfix @E12) y
    assert $ Prop.monotonic (ratfix @E12) x x' y y'
    assert $ Prop.idempotent (ratfix @E12) x y

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

prop_connection_rati08 :: Property
prop_connection_rati08 = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended $ G.integral (ri @Int8)
    y' <- forAll $ gen_extended $ G.integral (ri @Int8)

    assert $ Prop.adjoint (rati08) x y
    assert $ Prop.closed (rati08) x
    assert $ Prop.kernel (rati08) y
    assert $ Prop.monotonic (rati08) x x' y y'
    assert $ Prop.idempotent (rati08) x y

prop_connection_rati16 :: Property
prop_connection_rati16 = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended $ G.integral (ri @Int16)
    y' <- forAll $ gen_extended $ G.integral (ri @Int16)

    assert $ Prop.adjoint (rati16) x y
    assert $ Prop.closed (rati16) x
    assert $ Prop.kernel (rati16) y
    assert $ Prop.monotonic (rati16) x x' y y'
    assert $ Prop.idempotent (rati16) x y

prop_connection_rati32 :: Property
prop_connection_rati32 = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended $ G.integral (ri @Int32)
    y' <- forAll $ gen_extended $ G.integral (ri @Int32)

    assert $ Prop.adjoint (rati32) x y
    assert $ Prop.closed (rati32) x
    assert $ Prop.kernel (rati32) y
    assert $ Prop.monotonic (rati32) x x' y y'
    assert $ Prop.idempotent (rati32) x y

prop_connection_rati64 :: Property
prop_connection_rati64 = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended $ G.integral (ri @Int64)
    y' <- forAll $ gen_extended $ G.integral (ri @Int64)

    assert $ Prop.adjoint (rati64) x y
    assert $ Prop.closed (rati64) x
    assert $ Prop.kernel (rati64) y
    assert $ Prop.monotonic (rati64) x x' y y'
    assert $ Prop.idempotent (rati64) x y

prop_connection_ratint :: Property
prop_connection_ratint = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended $ G.integral ri'
    y' <- forAll $ gen_extended $ G.integral ri'

    assert $ Prop.adjoint (ratint) x y
    assert $ Prop.closed (ratint) x
    assert $ Prop.kernel (ratint) y
    assert $ Prop.monotonic (ratint) x x' y y'
    assert $ Prop.idempotent (ratint) x y

prop_connection_posw08 :: Property
prop_connection_posw08 = withTests 1000 . property $ do
    x <- forAll pos
    x' <- forAll pos
    y <- forAll $ gen_lowered $ G.integral (ri @Word8)
    y' <- forAll $ gen_lowered $ G.integral (ri @Word8)

    assert $ Prop.adjoint (posw08) x y
    assert $ Prop.closed (posw08) x
    assert $ Prop.kernel (posw08) y
    assert $ Prop.monotonic (posw08) x x' y y'
    assert $ Prop.idempotent (posw08) x y

prop_connection_posw16 :: Property
prop_connection_posw16 = withTests 1000 . property $ do
    x <- forAll pos
    x' <- forAll pos
    y <- forAll $ gen_lowered $ G.integral (ri @Word16)
    y' <- forAll $ gen_lowered $ G.integral (ri @Word16)

    assert $ Prop.adjoint (posw16) x y
    assert $ Prop.closed (posw16) x
    assert $ Prop.kernel (posw16) y
    assert $ Prop.monotonic (posw16) x x' y y'
    assert $ Prop.idempotent (posw16) x y

prop_connection_posw32 :: Property
prop_connection_posw32 = withTests 1000 . property $ do
    x <- forAll pos
    x' <- forAll pos
    y <- forAll $ gen_lowered $ G.integral (ri @Word32)
    y' <- forAll $ gen_lowered $ G.integral (ri @Word32)

    assert $ Prop.adjoint (posw32) x y
    assert $ Prop.closed (posw32) x
    assert $ Prop.kernel (posw32) y
    assert $ Prop.monotonic (posw32) x x' y y'
    assert $ Prop.idempotent (posw32) x y

prop_connection_posw64 :: Property
prop_connection_posw64 = withTests 1000 . property $ do
    x <- forAll pos
    x' <- forAll pos
    y <- forAll $ gen_lowered $ G.integral (ri @Word64)
    y' <- forAll $ gen_lowered $ G.integral (ri @Word64)

    assert $ Prop.adjoint (posw64) x y
    assert $ Prop.closed (posw64) x
    assert $ Prop.kernel (posw64) y
    assert $ Prop.monotonic (posw64) x x' y y'
    assert $ Prop.idempotent (posw64) x y

prop_connection_posnat :: Property
prop_connection_posnat = withTests 1000 . property $ do
    x <- forAll pos
    x' <- forAll pos
    y <- forAll $ gen_lowered $ G.integral rn
    y' <- forAll $ gen_lowered $ G.integral rn

    assert $ Prop.adjoint (posnat) x y
    assert $ Prop.closed (posnat) x
    assert $ Prop.kernel (posnat) y
    assert $ Prop.monotonic (posnat) x x' y y'
    assert $ Prop.idempotent (posnat) x y

tests :: IO Bool
tests = checkParallel $$(discover)
