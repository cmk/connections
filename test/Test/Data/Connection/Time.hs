{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Test.Data.Connection.Time where

import qualified Data.Connection.Property as Prop
import Data.Connection.Time
import Hedgehog
import qualified Hedgehog.Gen as G
import Test.Data.Connection

sys :: Gen SystemTime
sys = MkSystemTime <$> G.int64 ri <*> G.word32 ri

prop_connection_sysixx :: Property
prop_connection_sysixx = withTests 1000 . property $ do
    x <- forAll sys
    x' <- forAll sys
    y <- forAll $ G.int ri
    y' <- forAll $ G.int ri

    assert $ Prop.adjoint sysixx x y
    assert $ Prop.closed sysixx x
    assert $ Prop.kernel sysixx y
    assert $ Prop.monotonic sysixx x x' y y'
    assert $ Prop.idempotent sysixx x y

prop_connection_f32sys :: Property
prop_connection_f32sys = withTests 1000 . property $ do
    x <- forAll f32
    x' <- forAll f32
    y <- forAll $ gen_extended sys
    y' <- forAll $ gen_extended sys

    assert $ Prop.adjointL f32sys x y
    assert $ Prop.closedL f32sys x
    assert $ Prop.kernelL f32sys y
    assert $ Prop.monotonicL f32sys x x' y y'
    assert $ Prop.idempotentL f32sys x y

prop_connection_f64sys :: Property
prop_connection_f64sys = withTests 1000 . property $ do
    x <- forAll f64
    x' <- forAll f64
    y <- forAll $ gen_extended sys
    y' <- forAll $ gen_extended sys

    assert $ Prop.adjointL f64sys x y
    assert $ Prop.closedL f64sys x
    assert $ Prop.kernelL f64sys y
    assert $ Prop.monotonicL f64sys x x' y y'
    assert $ Prop.idempotentL f64sys x y

prop_connection_ratsys :: Property
prop_connection_ratsys = withTests 1000 . property $ do
    x <- forAll rat'
    x' <- forAll rat'
    y <- forAll $ gen_extended sys
    y' <- forAll $ gen_extended sys

    assert $ Prop.adjoint ratsys x y
    assert $ Prop.closed ratsys x
    assert $ Prop.kernel ratsys y
    assert $ Prop.monotonic ratsys x x' y y'
    assert $ Prop.idempotent ratsys x y

prop_connection_f09sys :: Property
prop_connection_f09sys = withTests 1000 . property $ do
    x <- forAll $ gen_extended fxx
    x' <- forAll $ gen_extended fxx
    y <- forAll $ gen_extended sys
    y' <- forAll $ gen_extended sys

    assert $ Prop.adjoint f09sys x y
    assert $ Prop.closed f09sys x
    assert $ Prop.kernel f09sys y
    assert $ Prop.monotonic f09sys x x' y y'
    assert $ Prop.idempotent f09sys x y

tests :: IO Bool
tests = checkParallel $$(discover)
