{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Float where

import Data.Prd.Nan
import Data.Int
import Data.Word
import Data.Float
import Data.Prd
import Data.Semiring
import Data.Connection
import Data.Connection.Filter
import Data.Connection.Float
import Data.Semigroup.Quantale

import qualified Data.Prd.Property as Prop
import qualified Data.Semiring.Property as Prop
import qualified Data.Connection.Property as Prop

import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

ri :: (Integral a, Bounded a) => Range a
ri = R.exponentialFrom 0 minBound maxBound

rf :: Range Float
rf = R.exponentialFloatFrom 0 (-3.4028235e38) 3.4028235e38

gen_flt32' :: Gen Float
gen_flt32' = G.frequency [(99, gen_flt32), (1, G.element [nInf, pInf, aNan])] 

gen_flt32 :: Gen Float
gen_flt32 = G.float rf

gen_nan :: Gen a -> Gen (Nan a)
gen_nan gen = G.frequency [(9, Def <$> gen), (1, pure NaN)]

prop_prd_ulp32 :: Property
prop_prd_ulp32 = withTests 1000 . property $ do
  x <- connl f32u32 <$> forAll gen_flt32'
  y <- connl f32u32 <$> forAll gen_flt32'
  z <- connl f32u32 <$> forAll gen_flt32'
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z

prop_prd_flt32 :: Property
prop_prd_flt32 = withTests 100000 . property $ do
  x <- forAll gen_flt32'
  y <- forAll gen_flt32'
  z <- forAll gen_flt32'
  w <- forAll gen_flt32'
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

{-
prop_semigroup_float :: Property
prop_semigroup_float = withTests 20000 $ property $ do
  x <- forAll gen_flt32'
  y <- forAll gen_flt32'
  z <- forAll gen_flt32'

  assert $ Prop.neutral_addition' x
  assert $ Prop.associative_addition (abs x) (abs y) (abs z)
-}

prop_connections_flt32_wrd64 :: Property
prop_connections_flt32_wrd64 = withTests 1000 . property $ do
  x <- forAll gen_flt32'
  y <- forAll gen_flt32'
  x' <- forAll gen_flt32'
  y' <- forAll gen_flt32'
  z <- forAll (gen_nan $ G.integral @_ @Word64 ri)
  w <- forAll (gen_nan $ G.integral @_ @Word64 ri)
  z' <- forAll (gen_nan $ G.integral @_ @Word64 ri)
  w' <- forAll (gen_nan $ G.integral @_ @Word64 ri)
  exy <- forAll $ G.element [Left x, Right y]
  exy' <- forAll $ G.element [Left x', Right y']
  ezw <- forAll $ G.element [Left z, Right w]
  ezw' <- forAll $ G.element [Left z', Right w']

  assert $ Prop.closed (idx @Float) x
  assert $ Prop.kernel (idx @Float) z
  assert $ Prop.monotone' (idx @Float) x x'
  assert $ Prop.monotone (idx @Float) z z'
  assert $ Prop.connection (idx @Float) x z

  assert $ Prop.closed (idx @(Float,Float)) (x,y)
  assert $ Prop.kernel (idx @(Float,Float)) (z,w)
  assert $ Prop.monotone' (idx @(Float,Float)) (x,y) (x',y')
  assert $ Prop.monotone (idx @(Float,Float)) (z,w) (z',w')
  assert $ Prop.connection (idx @(Float,Float)) (x,y)(z,w)

  assert $ Prop.closed (idx @(Either Float Float)) exy
  assert $ Prop.kernel (idx @(Either Float Float)) ezw
  assert $ Prop.monotone' (idx @(Either Float Float)) exy exy'
  assert $ Prop.monotone (idx @(Either Float Float)) ezw ezw'
  assert $ Prop.connection (idx @(Either Float Float)) exy ezw

prop_connections_flt32_ulp32 :: Property
prop_connections_flt32_ulp32 = withTests 1000 . property $ do
  x <- forAll gen_flt32'
  y <- Ulp32 <$> forAll (G.integral ri)
  x' <- forAll gen_flt32'
  y' <- Ulp32 <$> forAll (G.integral ri)

  assert $ Prop.connection f32u32 x y
  assert $ Prop.connection u32f32 y x

  assert $ Prop.monotone' f32u32 x x'
  assert $ Prop.monotone' u32f32 y y'

  assert $ Prop.monotone f32u32 y y'
  assert $ Prop.monotone u32f32 x x'

  assert $ Prop.closed f32u32 x
  assert $ Prop.closed u32f32 y

  assert $ Prop.kernel u32f32 x
  assert $ Prop.kernel f32u32 y

prop_connections_flt32_int64 :: Property
prop_connections_flt32_int64 = withTests 1000 . property $ do
  x <- forAll gen_flt32'
  y <- forAll (gen_nan $ G.integral ri)
  x' <- forAll gen_flt32'
  y' <- forAll (gen_nan $ G.integral ri)
 
  assert $ Prop.connection f32i64 x y
  assert $ Prop.connection i64f32 y x

  assert $ Prop.monotone' f32i64 x x'
  assert $ Prop.monotone' i64f32 y y'

  assert $ Prop.monotone f32i64 y y'
  assert $ Prop.monotone i64f32 x x'

  assert $ Prop.closed f32i64 x
  assert $ Prop.closed i64f32 y

  assert $ Prop.kernel i64f32 x
  assert $ Prop.kernel f32i64 y


prop_quantale_flt32 :: Property
prop_quantale_flt32 = withTests 1000 . withShrinks 0 $ property $ do
  x <- forAll gen_flt32 -- we do not require `residr pInf` etc
  y <- forAll gen_flt32'
  z <- forAll gen_flt32'

  assert $ Prop.connection (residl x) y z
  assert $ Prop.connection (residr x) y z

  assert $ Prop.monotone' (residl x) y z
  assert $ Prop.monotone' (residr x) y z

  assert $ Prop.monotone (residl x) y z
  assert $ Prop.monotone (residr x) y z

  assert $ Prop.closed (residl x) y
  assert $ Prop.closed (residr x) y

  assert $ Prop.kernel (residl x) y
  assert $ Prop.kernel (residr x) y

  assert $ residuated x y z

tests :: IO Bool
tests = checkParallel $$(discover)
