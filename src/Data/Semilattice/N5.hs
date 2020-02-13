{-# LANGUAGE DeriveFunctor       #-}
module Data.Semilattice.N5 where

import Control.Applicative
import Data.Prd
import Data.Prd.Nan
import Data.Connection
import Data.Semilattice
import Data.Semiring
import Data.Semifield

import Prelude hiding (Num(..), Ord(..), Fractional(..), Bounded)

-- | Lift a 'Semifield' into a non-modular lattice.
--
-- See <https://en.wikipedia.org/wiki/Modular_lattice#Examples>
--
newtype N5 a = N5 { unN5 :: a } deriving (Show, Functor)

n5 :: (Minimal a, Semifield a, Minimal b, Semifield b) => Conn a b -> Conn (N5 a) (N5 b)
n5 (Conn f g) = Conn (fmap f) (fmap g)

n5' :: Semifield a => Minimal a => Bound b => Trip a (Nan b) -> Trip (N5 a) b
n5' t = Trip f g h where
  Conn f g = n5l . tripl $ t
  Conn _ h = n5r . tripr $ t

n5l :: Semifield a => Minimal a => Maximal b => Conn a (Nan b) -> Conn (N5 a) b
n5l (Conn f g) = Conn f' g' where
  f' (N5 x) = nan maximal id $ f x
  g' = N5 . g . Def

n5r :: Semifield b => Minimal a => Minimal b => Conn (Nan a) b -> Conn a (N5 b)
n5r (Conn f g) = Conn f' g' where
  f' = N5 . f . Def
  g' (N5 x) = nan minimal id $ g x

{-
untf64 :: Conn (Bottom Unit) (N5 Double)
untf64 = Conn f g where
  f = maybe (N5 ninf) (N5 . unUnit)
  g (N5 x) | x >= 0 = Just . Unit $ min 1 x
           | otherwise = Nothing

nan :: b -> (a -> b) -> Nan a -> b

extended :: Field b => (a -> b) -> Extended a -> b
extended f = nan' $ bounded ninf f pinf

liftNan :: Prd a => Semifield a => (a -> b) -> a -> Nan b
liftNan f x | x =~ anan = Nan
            | otherwise = Def (f x)
-}

joinN5 :: Minimal a => Semifield a => N5 a -> N5 a -> N5 a
joinN5 (N5 x) (N5 y) = case pcompare x y of
  Just LT -> N5 y
  Just EQ -> N5 x
  Just GT -> N5 x
  Nothing -> N5 pinf

meetN5 :: Minimal a => Semifield a => N5 a -> N5 a -> N5 a
meetN5 (N5 x) (N5 y) = case pcompare x y of
  Just LT -> N5 x
  Just EQ -> N5 x
  Just GT -> N5 y
  Nothing -> N5 minimal


instance (Minimal a, Semifield a) => Prd (N5 a) where

  -- | 
  -- @ 'anan' '<=' 'pinf' @
  -- @ 'anan' '>=' 'ninf' @
  pcompare (N5 x) (N5 y) | x =~ y = Just EQ
                         | x =~ minimal = Just LT
                         | y =~ minimal = Just GT
                         | x =~ pinf = Just GT
                         | y =~ pinf = Just LT
                         | otherwise = pcompare x y

instance (Minimal a, Semifield a) => Eq (N5 a) where
  (==) = (=~)

instance (Minimal a, Semifield a) => Minimal (N5 a) where
  minimal = N5 minimal

instance (Bound a, Semifield a) => Maximal (N5 a) where
  maximal = N5 maximal

instance (Minimal a, Semifield a) => Semigroup (Meet (N5 a)) where
  (<>) = liftA2 meetN5 

instance (Minimal a, Semifield a) => Monoid (Meet (N5 a)) where
  mempty = Meet $ N5 pinf

instance (Minimal a, Semifield a) => Semigroup (Join (N5 a)) where
  (<>) = liftA2 joinN5

instance (Minimal a, Semifield a) => Monoid (Join (N5 a)) where
  mempty = Join $ N5 minimal

instance (Minimal a, Semifield a) => Lattice (N5 a)

instance (Additive-Semigroup) a => Semigroup (Additive (N5 a)) where
  (<>) = liftA2 (+)

instance (Additive-Monoid) a => Monoid (Additive (N5 a)) where
  mempty = pure zero
 
instance (Additive-Group) a => Magma (Additive (N5 a)) where
  (<<) = liftA2 (-)

instance (Additive-Group) a => Quasigroup (Additive (N5 a))
instance (Additive-Group) a => Loop (Additive (N5 a))
instance (Additive-Group) a => Group (Additive (N5 a))

instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (N5 a)) where
  (<>) = liftA2 (*)

instance (Multiplicative-Monoid) a => Monoid (Multiplicative (N5 a)) where
  mempty = pure one
 
instance (Multiplicative-Group) a => Magma (Multiplicative (N5 a)) where
  (<<) = liftA2 (/)

instance (Multiplicative-Group) a => Quasigroup (Multiplicative (N5 a))
instance (Multiplicative-Group) a => Loop (Multiplicative (N5 a))
instance (Multiplicative-Group) a => Group (Multiplicative (N5 a))

instance Presemiring a => Presemiring (N5 a)
instance Semiring a => Semiring (N5 a)
instance Ring a => Ring (N5 a)
instance Semifield a => Semifield (N5 a)
instance Field a => Field (N5 a)
