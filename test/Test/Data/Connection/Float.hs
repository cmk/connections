{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Float where

import Data.Connection.Trip
import Data.Connection.Float
import Data.Float
import Data.Int
import Data.Prd.Nan
import Hedgehog
import Prelude hiding (Ord(..),Bounded, until)
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G

prop_connection_f32ord :: Property
prop_connection_f32ord = withTests 100 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_nan ord
  y' <- forAll $ gen_nan ord

  let f32ord = fltord :: Trip Float (Nan Ordering)

  assert $ Prop.adjoined (tripl f32ord) x y
  assert $ Prop.adjoined (tripr f32ord) y x
  assert $ Prop.closed (tripl f32ord) x
  assert $ Prop.closed (tripr f32ord) y
  assert $ Prop.kernel (tripl f32ord) y
  assert $ Prop.kernel (tripr f32ord) x
  assert $ Prop.monotonel (tripl f32ord) x x'
  assert $ Prop.monotonel (tripr f32ord) y y'
  assert $ Prop.monotoner (tripl f32ord) y y'
  assert $ Prop.monotoner (tripr f32ord) x x'
  assert $ Prop.projectivel (tripl f32ord) x
  assert $ Prop.projectivel (tripr f32ord) y
  assert $ Prop.projectiver (tripl f32ord) y
  assert $ Prop.projectiver (tripr f32ord) x

prop_connection_f32i08 :: Property
prop_connection_f32i08 = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_ext $ G.integral (ri @Int8)
  y' <- forAll $ gen_ext $ G.integral (ri @Int8)

  assert $ Prop.adjoined (tripl f32i08) x y
  assert $ Prop.adjoined (tripr f32i08) y x
  assert $ Prop.closed (tripl f32i08) x
  assert $ Prop.closed (tripr f32i08) y
  assert $ Prop.kernel (tripl f32i08) y
  assert $ Prop.kernel (tripr f32i08) x 
  assert $ Prop.monotonel (tripl f32i08) x x'
  assert $ Prop.monotonel (tripr f32i08) y y'
  assert $ Prop.monotoner (tripl f32i08) y y'
  assert $ Prop.monotoner (tripr f32i08) x x'
  assert $ Prop.projectivel (tripl f32i08) x
  assert $ Prop.projectivel (tripr f32i08) y
  assert $ Prop.projectiver (tripl f32i08) y
  assert $ Prop.projectiver (tripr f32i08) x

prop_connection_f32i16 :: Property
prop_connection_f32i16 = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_ext $ G.integral (ri @Int16)
  y' <- forAll $ gen_ext $ G.integral (ri @Int16)

  assert $ Prop.adjoined (tripl f32i16) x y
  assert $ Prop.adjoined (tripr f32i16) y x
  assert $ Prop.closed (tripl f32i16) x
  assert $ Prop.closed (tripr f32i16) y
  assert $ Prop.kernel (tripl f32i16) y
  assert $ Prop.kernel (tripr f32i16) x 
  assert $ Prop.monotonel (tripl f32i16) x x'
  assert $ Prop.monotonel (tripr f32i16) y y'
  assert $ Prop.monotoner (tripl f32i16) y y'
  assert $ Prop.monotoner (tripr f32i16) x x'
  assert $ Prop.projectivel (tripl f32i16) x
  assert $ Prop.projectivel (tripr f32i16) y
  assert $ Prop.projectiver (tripl f32i16) y
  assert $ Prop.projectiver (tripr f32i16) x

prop_connections_f32 :: Property
prop_connections_f32 = withTests 1000 . property $ do
  x <- forAll f32
  y <- forAll (gen_nan $ G.integral ri)
  x' <- forAll f32
  y' <- forAll (gen_nan $ G.integral ri)
 
  assert $ Prop.adjoined f32i32 x y
  assert $ Prop.adjoined i32f32 y x
  assert $ Prop.closed f32i32 x
  assert $ Prop.closed i32f32 y
  assert $ Prop.kernel i32f32 x
  assert $ Prop.kernel f32i32 y
  assert $ Prop.monotonel f32i32 x x'
  assert $ Prop.monotonel i32f32 y y'
  assert $ Prop.monotoner f32i32 y y'
  assert $ Prop.monotoner i32f32 x x'
  assert $ Prop.projectivel f32i32 x
  assert $ Prop.projectivel i32f32 y
  assert $ Prop.projectiver i32f32 x
  assert $ Prop.projectiver f32i32 y

prop_connection_f64ord :: Property
prop_connection_f64ord = withTests 100 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_nan ord
  y' <- forAll $ gen_nan ord

  let f64ord = fltord :: Trip Double (Nan Ordering)

  assert $ Prop.adjoined (tripl f64ord) x y
  assert $ Prop.adjoined (tripr f64ord) y x
  assert $ Prop.closed (tripl f64ord) x
  assert $ Prop.closed (tripr f64ord) y
  assert $ Prop.kernel (tripl f64ord) y
  assert $ Prop.kernel (tripr f64ord) x
  assert $ Prop.monotonel (tripl f64ord) x x'
  assert $ Prop.monotonel (tripr f64ord) y y'
  assert $ Prop.monotoner (tripl f64ord) y y'
  assert $ Prop.monotoner (tripr f64ord) x x'
  assert $ Prop.projectivel (tripl f64ord) x
  assert $ Prop.projectivel (tripr f64ord) y
  assert $ Prop.projectiver (tripl f64ord) y
  assert $ Prop.projectiver (tripr f64ord) x

prop_connection_f64i08 :: Property
prop_connection_f64i08 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_ext $ G.integral (ri @Int8)
  y' <- forAll $ gen_ext $ G.integral (ri @Int8)

  assert $ Prop.adjoined (tripl f64i08) x y
  assert $ Prop.adjoined (tripr f64i08) y x
  assert $ Prop.closed (tripl f64i08) x
  assert $ Prop.closed (tripr f64i08) y
  assert $ Prop.kernel (tripl f64i08) y
  assert $ Prop.kernel (tripr f64i08) x 
  assert $ Prop.monotonel (tripl f64i08) x x'
  assert $ Prop.monotonel (tripr f64i08) y y'
  assert $ Prop.monotoner (tripl f64i08) y y'
  assert $ Prop.monotoner (tripr f64i08) x x'
  assert $ Prop.projectivel (tripl f64i08) x
  assert $ Prop.projectivel (tripr f64i08) y
  assert $ Prop.projectiver (tripl f64i08) y
  assert $ Prop.projectiver (tripr f64i08) x

prop_connection_f64i16 :: Property
prop_connection_f64i16 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_ext $ G.integral (ri @Int16)
  y' <- forAll $ gen_ext $ G.integral (ri @Int16)

  assert $ Prop.adjoined (tripl f64i16) x y
  assert $ Prop.adjoined (tripr f64i16) y x
  assert $ Prop.closed (tripl f64i16) x
  assert $ Prop.closed (tripr f64i16) y
  assert $ Prop.kernel (tripl f64i16) y
  assert $ Prop.kernel (tripr f64i16) x 
  assert $ Prop.monotonel (tripl f64i16) x x'
  assert $ Prop.monotonel (tripr f64i16) y y'
  assert $ Prop.monotoner (tripl f64i16) y y'
  assert $ Prop.monotoner (tripr f64i16) x x'
  assert $ Prop.projectivel (tripl f64i16) x
  assert $ Prop.projectivel (tripr f64i16) y
  assert $ Prop.projectiver (tripl f64i16) y
  assert $ Prop.projectiver (tripr f64i16) x

prop_connection_f64i32 :: Property
prop_connection_f64i32 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_ext $ G.integral (ri @Int32)
  y' <- forAll $ gen_ext $ G.integral (ri @Int32)

  assert $ Prop.adjoined (tripl f64i32) x y
  assert $ Prop.adjoined (tripr f64i32) y x
  assert $ Prop.closed (tripl f64i32) x
  assert $ Prop.closed (tripr f64i32) y
  assert $ Prop.kernel (tripl f64i32) y
  assert $ Prop.kernel (tripr f64i32) x 
  assert $ Prop.monotonel (tripl f64i32) x x'
  assert $ Prop.monotonel (tripr f64i32) y y'
  assert $ Prop.monotoner (tripl f64i32) y y'
  assert $ Prop.monotoner (tripr f64i32) x x'
  assert $ Prop.projectivel (tripl f64i32) x
  assert $ Prop.projectivel (tripr f64i32) y
  assert $ Prop.projectiver (tripl f64i32) y
  assert $ Prop.projectiver (tripr f64i32) x

prop_connection_f64f32 :: Property
prop_connection_f64f32 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll f32
  y' <- forAll f32

  assert $ Prop.adjoined (tripl f64f32) x y
  assert $ Prop.adjoined (tripr f64f32) y x
  assert $ Prop.closed (tripl f64f32) x
  assert $ Prop.closed (tripr f64f32) y
  assert $ Prop.kernel (tripl f64f32) y
  assert $ Prop.kernel (tripr f64f32) x
  assert $ Prop.monotonel (tripl f64f32) x x'
  assert $ Prop.monotonel (tripr f64f32) y y'
  assert $ Prop.monotoner (tripl f64f32) y y'
  assert $ Prop.monotoner (tripr f64f32) x x'
  assert $ Prop.projectivel (tripl f64f32) x
  assert $ Prop.projectivel (tripr f64f32) y
  assert $ Prop.projectiver (tripl f64f32) y
  assert $ Prop.projectiver (tripr f64f32) x

prop_connections_f64 :: Property
prop_connections_f64 = withTests 1000 . property $ do
  x <- forAll f64
  y <- forAll (gen_nan $ G.integral ri)
  x' <- forAll f64
  y' <- forAll (gen_nan $ G.integral ri)
 
  assert $ Prop.adjoined f64i64 x y
  assert $ Prop.adjoined i64f64 y x
  assert $ Prop.closed f64i64 x
  assert $ Prop.closed i64f64 y
  assert $ Prop.kernel i64f64 x
  assert $ Prop.kernel f64i64 y
  assert $ Prop.monotonel f64i64 x x'
  assert $ Prop.monotonel i64f64 y y'
  assert $ Prop.monotoner f64i64 y y'
  assert $ Prop.monotoner i64f64 x x'
  assert $ Prop.projectivel f64i64 x
  assert $ Prop.projectivel i64f64 y
  assert $ Prop.projectiver i64f64 x
  assert $ Prop.projectiver f64i64 y


{-

prop_prd_u32 :: Property
prop_prd_u32 = withTests 1000 . property $ do
  x <- connl f32u32 <$> forAll f32
  y <- connl f32u32 <$> forAll f32
  z <- connl f32u32 <$> forAll f32
  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z

gen_sgn :: Gen Signed
gen_sgn = Signed <$> f32

gen_ugn :: Gen Unsigned
gen_ugn = (Unsigned . abs) <$> f32

prop_connections_f32u32 :: Property
prop_connections_f32u32 = withTests 1000 . property $ do
  x <- forAll f32
  y <- Ulp32 <$> forAll (G.integral ri)
  x' <- forAll f32
  y' <- Ulp32 <$> forAll (G.integral ri)

  assert $ Prop.adjoined f32u32 x y
  assert $ Prop.adjoined u32f32 y x
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
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_sgn
  y' <- forAll $ gen_sgn

  assert $ Prop.adjoined f32sgn x y
  assert $ Prop.monotonel f32sgn x x'
  assert $ Prop.monotoner f32sgn y y'
  assert $ Prop.closed f32sgn x
  assert $ Prop.kernel f32sgn y

prop_connections_f32w08 :: Property
prop_connections_f32w08 = withTests 10000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_nan $ G.integral (ri @Word8)
  y' <- forAll $ gen_nan $ G.integral (ri @Word8)

  assert $ Prop.adjoined (tripl f32w08) x y
  assert $ Prop.adjoined (tripr f32w08) y x
  assert $ Prop.monotonel (tripl f32w08) x x'
  assert $ Prop.monotonel (tripr f32w08) y y'
  assert $ Prop.monotoner (tripl f32w08) y y'
  assert $ Prop.monotoner (tripr f32w08) x x'
  assert $ Prop.closed (tripl f32w08) x
  assert $ Prop.closed (tripr f32w08) y
  assert $ Prop.kernel (tripl f32w08) y
  assert $ Prop.kernel (tripr f32w08) x

prop_connections_f32w64 :: Property
prop_connections_f32w64 = withTests 1000 . property $ do
  x <- forAll f32
  y <- forAll f32
  x' <- forAll f32
  y' <- forAll f32
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
  assert $ Prop.adjoined (idx @Float) x z

  assert $ Prop.closed (idx @(Float,Float)) (x,y)
  assert $ Prop.kernel (idx @(Float,Float)) (z,w)
  assert $ Prop.monotonel (idx @(Float,Float)) (x,y) (x',y')
  assert $ Prop.monotoner (idx @(Float,Float)) (z,w) (z',w')
  assert $ Prop.adjoined (idx @(Float,Float)) (x,y)(z,w)

  assert $ Prop.closed (idx @(Either Float Float)) exy
  assert $ Prop.kernel (idx @(Either Float Float)) ezw
  assert $ Prop.monotonel (idx @(Either Float Float)) exy exy'
  assert $ Prop.monotoner (idx @(Either Float Float)) ezw ezw'
  assert $ Prop.adjoined (idx @(Either Float Float)) exy ezw
-}


tests :: IO Bool
tests = checkParallel $$(discover)
