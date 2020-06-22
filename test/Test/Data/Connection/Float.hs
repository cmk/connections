{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Float where

import Data.Connection.Conn
import Data.Connection.Float
import Data.Connection.Double
import Data.Int
import Hedgehog
import Prelude hiding (Ord(..),Bounded, until)
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G


prop_connection_f32i08 :: Property
prop_connection_f32i08 = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_extended $ G.integral (ri @Int8)
  y' <- forAll $ gen_extended $ G.integral (ri @Int8)

  assert $ Prop.adjoint (f32i08) x y
  assert $ Prop.closed (f32i08) x
  assert $ Prop.kernel (f32i08) y
  assert $ Prop.monotonic (f32i08) x x' y y'
  assert $ Prop.idempotent (f32i08) x y

prop_connection_f32i16 :: Property
prop_connection_f32i16 = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_extended $ G.integral (ri @Int16)
  y' <- forAll $ gen_extended $ G.integral (ri @Int16)

  assert $ Prop.adjoint (f32i16) x y
  assert $ Prop.closed (f32i16) x
  assert $ Prop.kernel (f32i16) y
  assert $ Prop.monotonic (f32i16) x x' y y'
  assert $ Prop.idempotent (f32i16) x y

prop_connection_f64i08 :: Property
prop_connection_f64i08 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int8)
  y' <- forAll $ gen_extended $ G.integral (ri @Int8)

  assert $ Prop.adjoint (f64i08) x y
  assert $ Prop.closed (f64i08) x
  assert $ Prop.kernel (f64i08) y
  assert $ Prop.monotonic (f64i08) x x' y y'
  assert $ Prop.idempotent (f64i08) x y

prop_connection_f64i16 :: Property
prop_connection_f64i16 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int16)
  y' <- forAll $ gen_extended $ G.integral (ri @Int16)

  assert $ Prop.adjoint (f64i16) x y
  assert $ Prop.closed (f64i16) x
  assert $ Prop.kernel (f64i16) y
  assert $ Prop.monotonic (f64i16) x x' y y'
  assert $ Prop.idempotent (f64i16) x y

prop_connection_f64i32 :: Property
prop_connection_f64i32 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int32)
  y' <- forAll $ gen_extended $ G.integral (ri @Int32)

  assert $ Prop.adjoint (f64i32) x y
  assert $ Prop.closed (f64i32) x
  assert $ Prop.kernel (f64i32) y
  assert $ Prop.monotonic (f64i32) x x' y y'
  assert $ Prop.idempotent (f64i32) x y

{-

prop_connections_f32 :: Property
prop_connections_f32 = withTests 1000 . property $ do
  x <- forAll f32
  y <- forAll (gen_maybe $ G.integral ri)
  x' <- forAll f32
  y' <- forAll (gen_maybe $ G.integral ri)
 
  assert $ Prop.adjoint f32i32 x y
  assert $ Prop.adjoint i32f32 y x
  assert $ Prop.closed f32i32 x
  assert $ Prop.closed i32f32 y
  assert $ Prop.kernel i32f32 x
  assert $ Prop.kernel f32i32 y
  assert $ Prop.monotonicL f32i32 x x'
  assert $ Prop.monotonicL i32f32 y y'
  assert $ Prop.monotonicR f32i32 y y'
  assert $ Prop.monotonicR i32f32 x x'
  assert $ Prop.idempotentL f32i32 x
  assert $ Prop.idempotentL i32f32 y
  assert $ Prop.idempotentR i32f32 x
  assert $ Prop.idempotentR f32i32 y

prop_connections_f64 :: Property
prop_connections_f64 = withTests 1000 . property $ do
  x <- forAll f64
  y <- forAll (gen_maybe $ G.integral ri)
  x' <- forAll f64
  y' <- forAll (gen_maybe $ G.integral ri)
 
  assert $ Prop.adjoint f64i64 x y
  assert $ Prop.adjoint i64f64 y x
  assert $ Prop.closed f64i64 x
  assert $ Prop.closed i64f64 y
  assert $ Prop.kernel i64f64 x
  assert $ Prop.kernel f64i64 y
  assert $ Prop.monotonicL f64i64 x x'
  assert $ Prop.monotonicL i64f64 y y'
  assert $ Prop.monotonicR f64i64 y y'
  assert $ Prop.monotonicR i64f64 x x'
  assert $ Prop.idempotentL f64i64 x
  assert $ Prop.idempotentL i64f64 y
  assert $ Prop.idempotentR i64f64 x
  assert $ Prop.idempotentR f64i64 y

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

  assert $ Prop.adjoint f32u32 x y
  assert $ Prop.adjoint u32f32 y x
  assert $ Prop.monotonicL f32u32 x x'
  assert $ Prop.monotonicL u32f32 y y'
  assert $ Prop.monotonicR f32u32 y y'
  assert $ Prop.monotonicR u32f32 x x'
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

  assert $ Prop.adjoint f32sgn x y
  assert $ Prop.monotonicL f32sgn x x'
  assert $ Prop.monotonicR f32sgn y y'
  assert $ Prop.closed f32sgn x
  assert $ Prop.kernel f32sgn y

prop_connections_f32w08 :: Property
prop_connections_f32w08 = withTests 10000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_n5 $ G.integral (ri @Word8)
  y' <- forAll $ gen_n5 $ G.integral (ri @Word8)

  assert $ Prop.adjoint (tripl f32w08) x y
  assert $ Prop.adjoint (tripr f32w08) y x
  assert $ Prop.monotonicL (tripl f32w08) x x'
  assert $ Prop.monotonicL (tripr f32w08) y y'
  assert $ Prop.monotonicR (tripl f32w08) y y'
  assert $ Prop.monotonicR (tripr f32w08) x x'
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
  z <- forAll (gen_n5 $ G.integral @_ @Word64 ri)
  w <- forAll (gen_n5 $ G.integral @_ @Word64 ri)
  z' <- forAll (gen_n5 $ G.integral @_ @Word64 ri)
  w' <- forAll (gen_n5 $ G.integral @_ @Word64 ri)
  exy <- forAll $ G.element [Left x, Right y]
  exy' <- forAll $ G.element [Left x', Right y']
  ezw <- forAll $ G.element [Left z, Right w]
  ezw' <- forAll $ G.element [Left z', Right w']

  assert $ Prop.closed (idx @Float) x --TODO in Index.hs
  assert $ Prop.kernel (idx @Float) z
  assert $ Prop.monotonicL (idx @Float) x x'
  assert $ Prop.monotonicR (idx @Float) z z'
  assert $ Prop.adjoint (idx @Float) x z

  assert $ Prop.closed (idx @(Float,Float)) (x,y)
  assert $ Prop.kernel (idx @(Float,Float)) (z,w)
  assert $ Prop.monotonicL (idx @(Float,Float)) (x,y) (x',y')
  assert $ Prop.monotonicR (idx @(Float,Float)) (z,w) (z',w')
  assert $ Prop.adjoint (idx @(Float,Float)) (x,y)(z,w)

  assert $ Prop.closed (idx @(EitheR Float Float)) exy
  assert $ Prop.kernel (idx @(EitheR Float Float)) ezw
  assert $ Prop.monotonicL (idx @(EitheR Float Float)) exy exy'
  assert $ Prop.monotonicR (idx @(EitheR Float Float)) ezw ezw'
  assert $ Prop.adjoint (idx @(EitheR Float Float)) exy ezw
-}


tests :: IO Bool
tests = checkParallel $$(discover)
