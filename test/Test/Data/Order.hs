{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Order where

import Data.Int
import Data.Word
import Hedgehog
import Test.Data.Connection

import qualified Data.Order.Property as Prop
import qualified Hedgehog.Gen as G


prop_order_i08 :: Property
prop_order_i08 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Int8) 
  y <- forAll $ G.integral (ri @Int8) 
  z <- forAll $ G.integral (ri @Int8)
  w <- forAll $ G.integral (ri @Int8) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_order_i16 :: Property
prop_order_i16 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Int16) 
  y <- forAll $ G.integral (ri @Int16) 
  z <- forAll $ G.integral (ri @Int16)
  w <- forAll $ G.integral (ri @Int16) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_order_i32 :: Property
prop_order_i32 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Int32) 
  y <- forAll $ G.integral (ri @Int32) 
  z <- forAll $ G.integral (ri @Int32)
  w <- forAll $ G.integral (ri @Int32) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_order_i64 :: Property
prop_order_i64 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Int64) 
  y <- forAll $ G.integral (ri @Int64) 
  z <- forAll $ G.integral (ri @Int64)
  w <- forAll $ G.integral (ri @Int64) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_order_ixx :: Property
prop_order_ixx = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Int) 
  y <- forAll $ G.integral (ri @Int) 
  z <- forAll $ G.integral (ri @Int)
  w <- forAll $ G.integral (ri @Int) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_order_int :: Property
prop_order_int = withTests 1000 . property $ do
  x <- forAll $ G.integral ri'
  y <- forAll $ G.integral ri' 
  z <- forAll $ G.integral ri'
  w <- forAll $ G.integral ri'
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_order_w08 :: Property
prop_order_w08 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Word8) 
  y <- forAll $ G.integral (ri @Word8) 
  z <- forAll $ G.integral (ri @Word8)
  w <- forAll $ G.integral (ri @Word8) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_order_w16 :: Property
prop_order_w16 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Word16) 
  y <- forAll $ G.integral (ri @Word16) 
  z <- forAll $ G.integral (ri @Word16)
  w <- forAll $ G.integral (ri @Word16) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_order_w32 :: Property
prop_order_w32 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Word32) 
  y <- forAll $ G.integral (ri @Word32) 
  z <- forAll $ G.integral (ri @Word32)
  w <- forAll $ G.integral (ri @Word32) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_order_w64 :: Property
prop_order_w64 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Word64) 
  y <- forAll $ G.integral (ri @Word64) 
  z <- forAll $ G.integral (ri @Word64)
  w <- forAll $ G.integral (ri @Word64) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_order_wxx :: Property
prop_order_wxx = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Word) 
  y <- forAll $ G.integral (ri @Word) 
  z <- forAll $ G.integral (ri @Word)
  w <- forAll $ G.integral (ri @Word) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w

prop_order_nat :: Property
prop_order_nat = withTests 1000 . property $ do
  x <- forAll $ G.integral rn
  y <- forAll $ G.integral rn 
  z <- forAll $ G.integral rn
  w <- forAll $ G.integral rn
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w

prop_order_rat :: Property
prop_order_rat = withTests 1000 . property $ do
  x <- forAll rat
  y <- forAll rat
  z <- forAll rat
  w <- forAll rat
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w

prop_order_pos :: Property
prop_order_pos = withTests 1000 . property $ do
  x <- forAll pos
  y <- forAll pos
  z <- forAll pos
  w <- forAll pos
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w

prop_order_f32 :: Property
prop_order_f32 = withTests 1000 . property $ do
  x <- forAll f32
  y <- forAll f32
  z <- forAll f32
  w <- forAll f32
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w

prop_order_f64 :: Property
prop_order_f64 = withTests 1000 . property $ do
  x <- forAll f64
  y <- forAll f64
  z <- forAll f64
  w <- forAll f64
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w

prop_order_extended :: Property
prop_order_extended = withTests 1000 . property $ do
  x <- forAll . gen_extended $ G.integral (ri @Int8) 
  y <- forAll . gen_extended $ G.integral (ri @Int8) 
  z <- forAll . gen_extended $ G.integral (ri @Int8)
  w <- forAll . gen_extended $ G.integral (ri @Int8) 
  assert $ Prop.preorder x y
  assert $ Prop.order z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric_eq x y
  assert $ Prop.asymmetric_lt x y
  assert $ Prop.antisymmetric_le x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

tests :: IO Bool
tests = checkParallel $$(discover)
