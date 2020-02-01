{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Prd where

import Data.Int
import Data.Word
import Test.Data.Connection
import Hedgehog

import qualified Data.Prd.Property as Prop
import qualified Hedgehog.Gen as G

prop_prd_i08 :: Property
prop_prd_i08 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Int8) 
  y <- forAll $ G.integral (ri @Int8) 
  z <- forAll $ G.integral (ri @Int8)
  w <- forAll $ G.integral (ri @Int8) 
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_i16 :: Property
prop_prd_i16 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Int16) 
  y <- forAll $ G.integral (ri @Int16) 
  z <- forAll $ G.integral (ri @Int16)
  w <- forAll $ G.integral (ri @Int16) 
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_i32 :: Property
prop_prd_i32 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Int32) 
  y <- forAll $ G.integral (ri @Int32) 
  z <- forAll $ G.integral (ri @Int32)
  w <- forAll $ G.integral (ri @Int32) 
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_i64 :: Property
prop_prd_i64 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Int64) 
  y <- forAll $ G.integral (ri @Int64) 
  z <- forAll $ G.integral (ri @Int64)
  w <- forAll $ G.integral (ri @Int64) 
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_ixx :: Property
prop_prd_ixx = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Int) 
  y <- forAll $ G.integral (ri @Int) 
  z <- forAll $ G.integral (ri @Int)
  w <- forAll $ G.integral (ri @Int) 
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_int :: Property
prop_prd_int = withTests 1000 . property $ do
  x <- forAll $ G.integral ri'
  y <- forAll $ G.integral ri' 
  z <- forAll $ G.integral ri'
  w <- forAll $ G.integral ri'
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_w08 :: Property
prop_prd_w08 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Word8) 
  y <- forAll $ G.integral (ri @Word8) 
  z <- forAll $ G.integral (ri @Word8)
  w <- forAll $ G.integral (ri @Word8) 
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_w16 :: Property
prop_prd_w16 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Word16) 
  y <- forAll $ G.integral (ri @Word16) 
  z <- forAll $ G.integral (ri @Word16)
  w <- forAll $ G.integral (ri @Word16) 
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_w32 :: Property
prop_prd_w32 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Word32) 
  y <- forAll $ G.integral (ri @Word32) 
  z <- forAll $ G.integral (ri @Word32)
  w <- forAll $ G.integral (ri @Word32) 
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_w64 :: Property
prop_prd_w64 = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Word64) 
  y <- forAll $ G.integral (ri @Word64) 
  z <- forAll $ G.integral (ri @Word64)
  w <- forAll $ G.integral (ri @Word64) 
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_wxx :: Property
prop_prd_wxx = withTests 1000 . property $ do
  x <- forAll $ G.integral (ri @Word) 
  y <- forAll $ G.integral (ri @Word) 
  z <- forAll $ G.integral (ri @Word)
  w <- forAll $ G.integral (ri @Word) 
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_prd_nat :: Property
prop_prd_nat = withTests 1000 . property $ do
  x <- forAll $ G.integral rn
  y <- forAll $ G.integral rn 
  z <- forAll $ G.integral rn
  w <- forAll $ G.integral rn
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

{-
w = (-61190296498818470224935979790417002496) % 1
y = 784675940593409576367211913280487424 % 1
z = 44351588178463768880997328738947432448 % 1
w = 0 % 0
Prop.chain_31 x y z w
-}

prop_prd_rat :: Property
prop_prd_rat = withTests 1000 . property $ do
  x <- forAll rat
  y <- forAll rat
  z <- forAll rat
  w <- forAll rat
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w

prop_prd_pos :: Property
prop_prd_pos = withTests 1000 . property $ do
  x <- forAll pos
  y <- forAll pos
  z <- forAll pos
  w <- forAll pos
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w

prop_prd_f32 :: Property
prop_prd_f32 = withTests 1000 . property $ do
  x <- forAll f32
  y <- forAll f32
  z <- forAll f32
  w <- forAll f32
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w

prop_prd_f64 :: Property
prop_prd_f64 = withTests 1000 . property $ do
  x <- forAll f64
  y <- forAll f64
  z <- forAll f64
  w <- forAll f64
  assert $ Prop.consistent x y
  assert $ Prop.consistent z w
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z
  assert $ Prop.chain_22 x y z w

tests :: IO Bool
tests = checkParallel $$(discover)
