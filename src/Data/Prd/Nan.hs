{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE Safe                #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Prd.Nan where

import Control.Applicative
import Data.Prd
import GHC.Real
import GHC.Generics (Generic, Generic1)
import Prelude hiding (Ord(..), Bounded)

-- | A type with an additional incomparable element allowing for the possibility of undefined values.
data Nan a = Nan | Def a deriving ( Show, Generic, Generic1, Functor)

instance Prd a => Prd (Nan a) where
    Nan <= Nan = True
    _   <= Nan = False
    Nan <= _   = False
    Def a <= Def b = a <= b

instance Applicative Nan where
    pure = Def
    Nan <*> _ = Nan
    Def f <*> x = f <$> x

nan :: b -> (a -> b) -> Nan a -> b
nan _ f (Def y) = f y
nan x _  Nan    = x 

nanf :: Floating b => (a -> b) -> Nan a -> b
nanf f = nan (0/0) f

-- | An exception-safe version of 'nanf' for rationals.
--
nanr :: Integral b => (a -> Ratio b) -> Nan a -> Ratio b
nanr f = nan (0 :% 0) f

isDef :: Nan a -> Bool
isDef Nan = False
isDef _   = True

mapNan :: (a -> b) -> Nan a -> Nan b
mapNan f = nan Nan $ Def . f

joinNan :: Nan (Nan a) -> Nan a
joinNan Nan = Nan
joinNan (Def Nan) = Nan
joinNan (Def (Def a)) = Def a

liftNan :: Prd a => Floating a => (a -> b) -> a -> Nan b
liftNan f x | x =~ 0/0 = Nan
            | otherwise = Def (f x)
