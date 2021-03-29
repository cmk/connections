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

prop_connection_ratw08 :: Property
prop_connection_ratw08 = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended $ G.integral (ri @Word8)
    y' <- forAll $ gen_extended $ G.integral (ri @Word8)

    assert $ Prop.adjoint (ratw08) x y
    assert $ Prop.closed (ratw08) x
    assert $ Prop.kernel (ratw08) y
    assert $ Prop.monotonic (ratw08) x x' y y'
    assert $ Prop.idempotent (ratw08) x y

prop_connection_ratw16 :: Property
prop_connection_ratw16 = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended $ G.integral (ri @Word16)
    y' <- forAll $ gen_extended $ G.integral (ri @Word16)

    assert $ Prop.adjoint (ratw16) x y
    assert $ Prop.closed (ratw16) x
    assert $ Prop.kernel (ratw16) y
    assert $ Prop.monotonic (ratw16) x x' y y'
    assert $ Prop.idempotent (ratw16) x y

prop_connection_ratw32 :: Property
prop_connection_ratw32 = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended $ G.integral (ri @Word32)
    y' <- forAll $ gen_extended $ G.integral (ri @Word32)

    assert $ Prop.adjoint (ratw32) x y
    assert $ Prop.closed (ratw32) x
    assert $ Prop.kernel (ratw32) y
    assert $ Prop.monotonic (ratw32) x x' y y'
    assert $ Prop.idempotent (ratw32) x y

prop_connection_ratw64 :: Property
prop_connection_ratw64 = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended $ G.integral (ri @Word64)
    y' <- forAll $ gen_extended $ G.integral (ri @Word64)

    assert $ Prop.adjoint (ratw64) x y
    assert $ Prop.closed (ratw64) x
    assert $ Prop.kernel (ratw64) y
    assert $ Prop.monotonic (ratw64) x x' y y'
    assert $ Prop.idempotent (ratw64) x y

prop_connection_ratwxx :: Property
prop_connection_ratwxx = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended $ G.integral (ri @Word)
    y' <- forAll $ gen_extended $ G.integral (ri @Word)

    assert $ Prop.adjoint (ratwxx) x y
    assert $ Prop.closed (ratwxx) x
    assert $ Prop.kernel (ratwxx) y
    assert $ Prop.monotonic (ratwxx) x x' y y'
    assert $ Prop.idempotent (ratwxx) x y

prop_connection_ratnat :: Property
prop_connection_ratnat = withTests 1000 . property $ do
    x <- forAll rat
    x' <- forAll rat
    y <- forAll $ gen_extended $ G.integral rn
    y' <- forAll $ gen_extended $ G.integral rn

    assert $ Prop.adjoint ratnat x y
    assert $ Prop.closed ratnat x
    assert $ Prop.kernel ratnat y
    assert $ Prop.monotonic ratnat x x' y y'
    assert $ Prop.idempotent ratnat x y

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

tests :: IO Bool
tests = checkParallel $$(discover)
