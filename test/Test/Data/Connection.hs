{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection where

import Control.Applicative
import Data.Connection.Ratio
import Data.Float
import Data.Ord
import Data.Prd
import Data.Prd.Nan
import Data.Prd.Top
import Data.Ratio
import GHC.Real hiding (Fractional(..), (^^), (^), div)
import Hedgehog
import Numeric.Natural
import Prelude hiding (Bounded)
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

ri :: (Integral a, Bounded a) => Range a
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
f32 = gen_flt $ G.float rf

f64 :: Gen Double
f64 = gen_flt $ G.double rd

rat :: Gen Rational
rat = G.frequency [(49, gen), (1, G.element [-1 :% 0, 1 :% 0, 0 :% 0])]
  where gen = G.realFrac_ (R.linearFracFrom 0 (- 2^127) (2^127))

pos :: Gen Positive
pos = G.frequency [(49, gen), (1, G.element [1 :% 0, 0 :% 0])]
  where gen = G.realFrac_ (R.linearFracFrom 0 0 (2^127))

gen_dwn :: Gen a -> Gen (Down a)
gen_dwn gen = Down <$> gen

gen_nan :: Gen a -> Gen (Nan a)
gen_nan gen = G.frequency [(9, Def <$> gen), (1, pure Nan)]

--gen_pn5 :: Gen a -> Gen (N5 a)
--gen_pn5 gen = N5 <$> gen

gen_bot :: Gen a -> Gen (Bottom a)
gen_bot gen = G.frequency [(9, Just <$> gen), (1, pure Nothing)]

gen_top :: Gen a -> Gen (Top a)
gen_top gen = G.frequency [(9, Fin <$> gen), (1, pure Top)]

gen_bnd :: Gen a -> Gen (Bound a)
gen_bnd gen = G.frequency [(18, (Just . Fin) <$> gen), (1, pure Nothing), (1, pure $ Just Top)]

gen_lft :: Gen a -> Gen (Lifted a)
gen_lft = gen_nan . gen_top

gen_ext :: Gen a -> Gen (Extended a)
gen_ext = gen_nan . gen_bnd

gen_flt :: Floating a => Gen a -> Gen a 
gen_flt gen = G.frequency [(49, gen), (1, G.element [(-1/0), 1/0, 0/0])]



tests :: IO Bool
tests = checkParallel $$(discover)
