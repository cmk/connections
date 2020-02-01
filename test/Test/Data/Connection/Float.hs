{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Float where

import Control.Applicative
import Data.Prd.Nan
import Data.Int
import Data.Word
import Data.Float
import Data.Prd
import Data.Ord
import Data.Connection
import Data.Connection.Ratio
import Data.Semilattice.Bounded
--import Data.Connection.Filter
import Numeric.Natural
import Data.Ratio
import qualified Data.Prd.Property as Prop
import qualified Data.Connection.Property as Prop
import Test.Data.Connection

import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

import Prelude hiding (Bounded)


import GHC.Real hiding (Fractional(..), (^^), (^), div)


--TODO move to Test.Data.Connection
prop_connections_f32nan :: Property
prop_connections_f32nan = withTests 1000 . property $ do
  x <- forAll gen_f32
  x' <- forAll gen_f32
  y <- forAll $ gen_nan (G.float rf) 
  y' <- forAll $ gen_nan (G.float rf)

  assert $ Prop.connection (tripl fldnan) x y
  assert $ Prop.connection (tripr fldnan) y x
  assert $ Prop.monotonel (tripl fldnan) x x'
  assert $ Prop.monotonel (tripr fldnan) y y'
  assert $ Prop.monotoner (tripl fldnan) y y'
  assert $ Prop.monotoner (tripr fldnan) x x'
  assert $ Prop.closed (tripl fldnan) x
  assert $ Prop.closed (tripr fldnan) y -- would fail on y = Def NaN
  assert $ Prop.kernel (tripl fldnan) y
  assert $ Prop.kernel (tripr fldnan) x

prop_connections_f32ord :: Property
prop_connections_f32ord = withTests 1000 . property $ do
  x <- forAll gen_f32
  x' <- forAll gen_f32
  y <- forAll $ gen_nan gen_ord
  y' <- forAll $ gen_nan gen_ord

  let f32ord = fldord :: Trip Float (Nan Ordering)

  assert $ Prop.connection (tripl f32ord) x y
  assert $ Prop.connection (tripr f32ord) y x
  assert $ Prop.monotonel (tripl f32ord) x x'
  assert $ Prop.monotonel (tripr f32ord) y y'
  assert $ Prop.monotoner (tripl f32ord) y y'
  assert $ Prop.monotoner (tripr f32ord) x x'
  assert $ Prop.closed (tripl f32ord) x
  assert $ Prop.closed (tripr f32ord) y
  assert $ Prop.kernel (tripl f32ord) y
  assert $ Prop.kernel (tripr f32ord) x

prop_connections_f32i32 :: Property
prop_connections_f32i32 = withTests 10000 . property $ do
  x <- forAll gen_f32
  y <- forAll (gen_nan $ G.integral ri)
  x' <- forAll gen_f32
  y' <- forAll (gen_nan $ G.integral ri)
 
  assert $ Prop.connection f32i32 x y
  assert $ Prop.connection i32f32 y x
  assert $ Prop.monotonel f32i32 x x'
  assert $ Prop.monotonel i32f32 y y'
  assert $ Prop.monotoner f32i32 y y'
  assert $ Prop.monotoner i32f32 x x'
  assert $ Prop.closed f32i32 x
  assert $ Prop.closed i32f32 y
  assert $ Prop.kernel i32f32 x
  assert $ Prop.kernel f32i32 y

prop_connections_f64i64 :: Property
prop_connections_f64i64 = withTests 10000 . property $ do
  x <- forAll gen_f64
  y <- forAll (gen_nan $ G.integral ri)
  x' <- forAll gen_f64
  y' <- forAll (gen_nan $ G.integral ri)
 
  assert $ Prop.connection f64i64 x y
  assert $ Prop.connection i64f64 y x
  assert $ Prop.monotonel f64i64 x x'
  assert $ Prop.monotonel i64f64 y y'
  assert $ Prop.monotoner f64i64 y y'
  assert $ Prop.monotoner i64f64 x x'
  assert $ Prop.closed f64i64 x
  assert $ Prop.closed i64f64 y
  assert $ Prop.kernel i64f64 x
  assert $ Prop.kernel f64i64 y


{-
prop_prd_u32 :: Property
prop_prd_u32 = withTests 1000 . property $ do
  x <- connl f32u32 <$> forAll gen_f32
  y <- connl f32u32 <$> forAll gen_f32
  z <- connl f32u32 <$> forAll gen_f32
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z

--TODO move to Test.Data.Prd
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

-}

{-

gen_sgn :: Gen Signed
gen_sgn = Signed <$> gen_f32

gen_ugn :: Gen Unsigned
gen_ugn = (Unsigned . abs) <$> gen_f32

prop_connections_f32u32 :: Property
prop_connections_f32u32 = withTests 1000 . property $ do
  x <- forAll gen_f32
  y <- Ulp32 <$> forAll (G.integral ri)
  x' <- forAll gen_f32
  y' <- Ulp32 <$> forAll (G.integral ri)

  assert $ Prop.connection f32u32 x y
  assert $ Prop.connection u32f32 y x
  assert $ Prop.monotonel f32u32 x x'
  assert $ Prop.monotonel u32f32 y y'
  assert $ Prop.monotoner f32u32 y y'
  assert $ Prop.monotoner u32f32 x x'
  assert $ Prop.closed f32u32 x
  assert $ Prop.closed u32f32 y
  assert $ Prop.kernel u32f32 x
  assert $ Prop.kernel f32u32 y

prop_connections_f32sgn :: Property
prop_connections_f32sgn = withTests 10000 . property $ do
  x <- forAll gen_f32
  x' <- forAll gen_f32
  y <- forAll $ gen_sgn
  y' <- forAll $ gen_sgn

  assert $ Prop.connection f32sgn x y
  assert $ Prop.monotonel f32sgn x x'
  assert $ Prop.monotoner f32sgn y y'
  assert $ Prop.closed f32sgn x
  assert $ Prop.kernel f32sgn y



prop_connections_f32w08 :: Property
prop_connections_f32w08 = withTests 10000 . property $ do
  x <- forAll gen_f32
  x' <- forAll gen_f32
  y <- forAll $ gen_nan $ G.integral (ri @Word8)
  y' <- forAll $ gen_nan $ G.integral (ri @Word8)

  assert $ Prop.connection (tripl f32w08) x y
  assert $ Prop.connection (tripr f32w08) y x
  assert $ Prop.monotonel (tripl f32w08) x x'
  assert $ Prop.monotonel (tripr f32w08) y y'
  assert $ Prop.monotoner (tripl f32w08) y y'
  assert $ Prop.monotoner (tripr f32w08) x x'
  assert $ Prop.closed (tripl f32w08) x
  assert $ Prop.closed (tripr f32w08) y
  assert $ Prop.kernel (tripl f32w08) y
  assert $ Prop.kernel (tripr f32w08) x
-}



{-
prop_connections_f32w64 :: Property
prop_connections_f32w64 = withTests 1000 . property $ do
  x <- forAll gen_f32
  y <- forAll gen_f32
  x' <- forAll gen_f32
  y' <- forAll gen_f32
  z <- forAll (gen_nan $ G.integral @_ @Word64 ri)
  w <- forAll (gen_nan $ G.integral @_ @Word64 ri)
  z' <- forAll (gen_nan $ G.integral @_ @Word64 ri)
  w' <- forAll (gen_nan $ G.integral @_ @Word64 ri)
  exy <- forAll $ G.element [Left x, Right y]
  exy' <- forAll $ G.element [Left x', Right y']
  ezw <- forAll $ G.element [Left z, Right w]
  ezw' <- forAll $ G.element [Left z', Right w']

  assert $ Prop.closed (idx @Float) x --TODO in Index.hs
  assert $ Prop.kernel (idx @Float) z
  assert $ Prop.monotonel (idx @Float) x x'
  assert $ Prop.monotoner (idx @Float) z z'
  assert $ Prop.connection (idx @Float) x z

  assert $ Prop.closed (idx @(Float,Float)) (x,y)
  assert $ Prop.kernel (idx @(Float,Float)) (z,w)
  assert $ Prop.monotonel (idx @(Float,Float)) (x,y) (x',y')
  assert $ Prop.monotoner (idx @(Float,Float)) (z,w) (z',w')
  assert $ Prop.connection (idx @(Float,Float)) (x,y)(z,w)

  assert $ Prop.closed (idx @(Either Float Float)) exy
  assert $ Prop.kernel (idx @(Either Float Float)) ezw
  assert $ Prop.monotonel (idx @(Either Float Float)) exy exy'
  assert $ Prop.monotoner (idx @(Either Float Float)) ezw ezw'
  assert $ Prop.connection (idx @(Either Float Float)) exy ezw
-}




tests :: IO Bool
tests = checkParallel $$(discover)
