{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Data.Connection.Fixed where

import Data.Connection.Fixed
import qualified Data.Connection.Property as Prop
import Data.Fixed
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

prop_connections_micro :: Property
prop_connections_micro = withTests 1000 . property $ do
    f00 <- forAll fxx
    f01 <- forAll fxx
    f02 <- forAll fxx
    f03 <- forAll fxx
    f06 <- forAll fxx

    f00' <- forAll fxx
    f01' <- forAll fxx
    f02' <- forAll fxx
    f03' <- forAll fxx
    f06' <- forAll fxx

    assert $ Prop.adjoint f06f00 f06 f00
    assert $ Prop.closed f06f00 f06
    assert $ Prop.kernel f06f00 f00
    assert $ Prop.monotonic f06f00 f06 f06' f00 f00'
    assert $ Prop.idempotent f06f00 f06 f00

    assert $ Prop.adjoint f06f01 f06 f01
    assert $ Prop.closed f06f01 f06
    assert $ Prop.kernel f06f01 f01
    assert $ Prop.monotonic f06f01 f06 f06' f01 f01'
    assert $ Prop.idempotent f06f01 f06 f01

    assert $ Prop.adjoint f06f02 f06 f02
    assert $ Prop.closed f06f02 f06
    assert $ Prop.kernel f06f02 f02
    assert $ Prop.monotonic f06f02 f06 f06' f02 f02'
    assert $ Prop.idempotent f06f02 f06 f02

    assert $ Prop.adjoint f06f03 f06 f03
    assert $ Prop.closed f06f03 f06
    assert $ Prop.kernel f06f03 f03
    assert $ Prop.monotonic f06f03 f06 f06' f03 f03'
    assert $ Prop.idempotent f06f03 f06 f03

prop_connections_nano :: Property
prop_connections_nano = withTests 1000 . property $ do
    f00 <- forAll fxx
    f01 <- forAll fxx
    f02 <- forAll fxx
    f03 <- forAll fxx
    f06 <- forAll fxx
    f09 <- forAll fxx

    f00' <- forAll fxx
    f01' <- forAll fxx
    f02' <- forAll fxx
    f03' <- forAll fxx
    f06' <- forAll fxx
    f09' <- forAll fxx

    assert $ Prop.adjoint f09f00 f09 f00
    assert $ Prop.closed f09f00 f09
    assert $ Prop.kernel f09f00 f00
    assert $ Prop.monotonic f09f00 f09 f09' f00 f00'
    assert $ Prop.idempotent f09f00 f09 f00

    assert $ Prop.adjoint f09f01 f09 f01
    assert $ Prop.closed f09f01 f09
    assert $ Prop.kernel f09f01 f01
    assert $ Prop.monotonic f09f01 f09 f09' f01 f01'
    assert $ Prop.idempotent f09f01 f09 f01

    assert $ Prop.adjoint f09f02 f09 f02
    assert $ Prop.closed f09f02 f09
    assert $ Prop.kernel f09f02 f02
    assert $ Prop.monotonic f09f02 f09 f09' f02 f02'
    assert $ Prop.idempotent f09f02 f09 f02

    assert $ Prop.adjoint f09f03 f09 f03
    assert $ Prop.closed f09f03 f09
    assert $ Prop.kernel f09f03 f03
    assert $ Prop.monotonic f09f03 f09 f09' f03 f03'
    assert $ Prop.idempotent f09f03 f09 f03

    assert $ Prop.adjoint f09f06 f09 f06
    assert $ Prop.closed f09f06 f09
    assert $ Prop.kernel f09f06 f06
    assert $ Prop.monotonic f09f06 f09 f09' f06 f06'
    assert $ Prop.idempotent f09f06 f09 f06

prop_connections_pico :: Property
prop_connections_pico = withTests 1000 . property $ do
    f00 <- forAll fxx
    f01 <- forAll fxx
    f02 <- forAll fxx
    f03 <- forAll fxx
    f06 <- forAll fxx
    f09 <- forAll fxx
    f12 <- forAll fxx

    f00' <- forAll fxx
    f01' <- forAll fxx
    f02' <- forAll fxx
    f03' <- forAll fxx
    f06' <- forAll fxx
    f09' <- forAll fxx
    f12' <- forAll fxx

    assert $ Prop.adjoint f12f00 f12 f00
    assert $ Prop.closed f12f00 f12
    assert $ Prop.kernel f12f00 f00
    assert $ Prop.monotonic f12f00 f12 f12' f00 f00'
    assert $ Prop.idempotent f12f00 f12 f00

    assert $ Prop.adjoint f12f01 f12 f01
    assert $ Prop.closed f12f01 f12
    assert $ Prop.kernel f12f01 f01
    assert $ Prop.monotonic f12f01 f12 f12' f01 f01'
    assert $ Prop.idempotent f12f01 f12 f01

    assert $ Prop.adjoint f12f02 f12 f02
    assert $ Prop.closed f12f02 f12
    assert $ Prop.kernel f12f02 f02
    assert $ Prop.monotonic f12f02 f12 f12' f02 f02'
    assert $ Prop.idempotent f12f02 f12 f02

    assert $ Prop.adjoint f12f03 f12 f03
    assert $ Prop.closed f12f03 f12
    assert $ Prop.kernel f12f03 f03
    assert $ Prop.monotonic f12f03 f12 f12' f03 f03'
    assert $ Prop.idempotent f12f03 f12 f03

    assert $ Prop.adjoint f12f06 f12 f06
    assert $ Prop.closed f12f06 f12
    assert $ Prop.kernel f12f06 f06
    assert $ Prop.monotonic f12f06 f12 f12' f06 f06'
    assert $ Prop.idempotent f12f06 f12 f06

    assert $ Prop.adjoint f12f09 f12 f09
    assert $ Prop.closed f12f09 f12
    assert $ Prop.kernel f12f09 f09
    assert $ Prop.monotonic f12f09 f12 f12' f09 f09'
    assert $ Prop.idempotent f12f09 f12 f09

tests :: IO Bool
tests = checkParallel $$(discover)
