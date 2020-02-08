{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection where

import Control.Applicative
import Data.Connection
import Data.Float
import Data.Int
import Data.Ord
import Data.Prd
import Data.Prd.Nan
import Data.Ratio
import Data.Semifield
import Data.Semilattice.Bounded
import Data.Word
import GHC.Real hiding (Fractional(..), (^^), (^), div)
import Hedgehog
import Numeric.Natural
import Prelude hiding (Bounded)
import qualified Data.Connection.Property as Prop
import qualified Data.Prd.Property as Prop
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

import Data.Float.Unit

ri :: (Integral a, Bound a) => Range a
ri = R.linearFrom 0 minimal maximal

ri' :: Range Integer
ri' = R.linearFrom 0 (- 2^127) (2^127)

ri'' :: Range Integer
ri'' = R.exponentialFrom 0 (-340282366920938463463374607431768211456) 340282366920938463463374607431768211456

rn :: Range Natural
rn = R.linear 0 (2^128)

rf :: Range Float
rf = R.exponentialFloatFrom 0 (-3.4028235e38) 3.4028235e38

rd :: Range Double
rd = R.exponentialFloatFrom 0 (-1.7976931348623157e308) 1.7976931348623157e308

ord :: Gen Ordering
ord = G.element [LT, EQ, GT]

f32 :: Gen Float
f32 = gen_fld $ G.float rf

f64 :: Gen Double
f64 = gen_fld $ G.double rd

rat :: Gen (Ratio Integer)
rat = gen_fld $ G.realFrac_ (R.linearFracFrom 0 (- 2^127) (2^127))

--TODO harden
unt :: Gen Unit
unt = Unit <$> G.double (R.linearFracFrom 0 0 1)

--TODO include NaN handling
prop_connection_untf64 :: Property
prop_connection_untf64 = withTests 1000 . property $ do
  x <- forAll $ gen_bot unt
  x' <- forAll $ gen_bot unt
  y <- forAll $ G.double rd
  y' <- forAll $ G.double rd

  assert $ Prop.connection untf64 x y
  assert $ Prop.closed untf64 x
  assert $ Prop.kernel untf64 y
  assert $ Prop.monotonel untf64 x x'
  assert $ Prop.monotoner untf64 y y'
  assert $ Prop.projectivel untf64 x
  assert $ Prop.projectiver untf64 y

pos :: Gen (Ratio Natural)
pos = G.frequency [(49, gen), (1, G.element [pinf, anan])]
  where gen = G.realFrac_ (R.linearFracFrom 0 0 (2^127))

gen_dwn :: Gen a -> Gen (Down a)
gen_dwn gen = Down <$> gen

gen_nan :: Gen a -> Gen (Nan a)
gen_nan gen = G.frequency [(9, Def <$> gen), (1, pure Nan)]

gen_bot :: Gen a -> Gen (Maybe a)
gen_bot gen = G.frequency [(9, Just <$> gen), (1, pure Nothing)]

gen_top :: Gen a -> Gen (Top a)
gen_top gen = G.frequency [(9, Fin <$> gen), (1, pure Top)]

gen_bnd :: Gen a -> Gen (Bounded a)
gen_bnd gen = G.frequency [(18, (Just . Fin) <$> gen), (1, pure Nothing), (1, pure $ Just Top)]

gen_lft :: Gen a -> Gen (Lifted a)
gen_lft = gen_nan . gen_top

gen_ext :: Gen a -> Gen (Extended a)
gen_ext = gen_nan . gen_bnd

gen_fld :: Field a => Gen a -> Gen a 
gen_fld gen = G.frequency [(49, gen), (1, G.element [ninf, pinf, anan])]



tests :: IO Bool
tests = checkParallel $$(discover)
