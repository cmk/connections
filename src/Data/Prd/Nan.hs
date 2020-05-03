{-# Language DeriveFunctor       #-}
{-# Language DeriveGeneric       #-}
{-# Language FlexibleContexts    #-}
{-# Language Safe                #-}
{-# Language ScopedTypeVariables #-}
module Data.Prd.Nan where

import safe Control.Applicative
import safe Data.Prd
import safe Data.Prd.Top
import safe GHC.Real
import safe GHC.Generics (Generic, Generic1)
import safe Prelude hiding (Ord(..), Bounded)

type Lifted a = Nan (Top a)
type Lowered a = Nan (Bottom a)
type Extended a = Nan (Bound a)

-- | A type with an additional incomparable element allowing for the possibility of undefined values.
data Nan a = Nan | Def a deriving (Show, Generic, Generic1, Functor)

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

lifted :: Floating b => (a -> b) -> Lifted a -> b
lifted = nanf . top (1/0)

extended :: Bounded b => b -> (a -> b) -> Extended a -> b
extended b f = nan b (bounded f)
