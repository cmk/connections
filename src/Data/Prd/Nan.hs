{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE Safe                #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Prd.Nan where

import Control.Applicative
import Data.Data (Data, Typeable)
import Data.Prd
import Data.Connection
import Data.Semiring
import Data.Semigroup.Additive
import Data.Semigroup.Multiplicative
import GHC.Generics (Generic, Generic1)

-- A type with an additional element allowing for the possibility of unisDef values.
-- Isomorphic to /Maybe a/ but with a different 'Prd' instance.
data Nan a = Nan | Def a
  deriving ( Eq, Ord, Show, Data, Typeable, Generic, Generic1, Functor, Foldable, Traversable)


instance Prd a => Prd (Nan a) where
    Nan <~ Nan = True
    _   <~ Nan = False
    Nan <~ _   = False
    Def a <~ Def b = a <~ b

instance Applicative Nan where
    pure = Def
    Nan <*> _ = Nan
    Def f <*> x = f <$> x

instance (Additive-Semigroup) a => Semigroup (Additive (Nan a)) where
  Additive a <> Additive b = Additive $ liftA2 add a b

-- MinPlus Dioid
instance (Additive-Monoid) a => Monoid (Additive (Nan a)) where
  mempty = Additive $ pure zero

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (Nan a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 mul a b

-- MinPlus Dioid
instance (Multiplicative-Monoid) a => Monoid (Multiplicative (Nan a)) where
  mempty = Multiplicative $ pure one

-- Presemiring with a absorbing element.
instance Presemiring a => Presemiring (Nan a)


{-

instance Field a => Field (Nan a) where

u + Nan = Nan + u = Nan − Nan = Nan
u · Nan = Nan · u = Nan Nan−1 = Nan
Nan  u ⇔ u = Nan u  Nan ⇔ u = Nan
-}

nan :: b -> (a -> b) -> Nan a -> b
nan _ f (Def y) = f y
nan x _  Nan    = x 

isDef :: Nan a -> Bool
isDef Nan = False
isDef _   = True

isNan :: Nan a -> Bool
isNan Nan = True
isNan _   = False

mapNan :: (a -> b) -> Nan a -> Nan b
mapNan f = nan Nan $ Def . f

joinNan :: Nan (Nan a) -> Nan a
joinNan Nan = Nan
joinNan (Def Nan) = Nan
joinNan (Def (Def a)) = Def a
-- collectNan = joinNan . liftNan id

liftNan :: (Prd a, Fractional a) => (a -> b) -> a -> Nan b
liftNan f x | x =~ (0/0) = Nan
            | otherwise = Def (f x)

liftNan' :: RealFloat a => (a -> b) -> a -> Nan b
liftNan' f x | isNaN x = Nan
             | otherwise = Def (f x)

-- Lift all exceptional values
liftAll :: (RealFloat a, Prd a, Bound b) => (a -> b) -> a -> Nan b
liftAll f x | isNaN x = Nan
            | isInf x = Def maximal
            | isInf (-x) = Def minimal
            | otherwise = Def (f x)

isInf :: (RealFloat a, Prd a) => a -> Bool
isInf x = isInfinite x && gt x 0


defnan :: Prd a => Prd b => Conn a b -> Conn (Nan a) (Nan b)
defnan (Conn f g) = Conn (fmap f) (fmap g) 

defnan' :: Prd a => Prd b => Trip a b -> Trip (Nan a) (Nan b)
defnan' (Trip f g h) = Trip (fmap f) (fmap g) (fmap h)

--nanfld :: Prd a => Field a => Trip (Nan a) a
-- Field a => Field (Nan a)
-- /Caution/ this is only legal if (Nan a) has no nans.
fldnan :: Prd a => Fractional a => Trip a (Nan a)
fldnan = Trip f g f where
  f a = if a =~ (0/0) then Nan else Def a 
  g = nan (0/0) id
