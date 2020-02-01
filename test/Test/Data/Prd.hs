{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Prd where

import Control.Applicative
import Data.Prd.Nan
import Data.Int
import Data.Word
import Data.Float
import Data.Prd
import Data.Ord
import Data.Connection
import Data.Semilattice.Bounded
--import Data.Connection.Filter
import Numeric.Natural
import Data.Ratio
import Test.Data.Connection

import qualified Data.Prd.Property as Prop
import qualified Data.Connection.Property as Prop

import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

prop_prd_rat :: Property
prop_prd_rat = withTests 1000 . property $ do
  x <- forAll gen_rat
  y <- forAll gen_rat
  z <- forAll gen_rat
  w <- forAll gen_rat
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
  --assert $ Prop.chain_31 x y z w

prop_prd_nat :: Property
prop_prd_nat = withTests 1000 . property $ do
  x <- forAll gen_nat
  y <- forAll gen_nat
  z <- forAll gen_nat
  w <- forAll gen_nat
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

prop_prd_f32 :: Property
prop_prd_f32 = withTests 1000 . property $ do
  x <- forAll gen_f32
  y <- forAll gen_f32
  z <- forAll gen_f32
  w <- forAll gen_f32
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
  --assert $ Prop.chain_31 x y z w



tests :: IO Bool
tests = checkParallel $$(discover)
