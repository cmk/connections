{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Lattice.Heyting (
  -- * Heyting algebras
    HeytingLaw
  , Heyting(..)
  , (==>), (<==)
  , iff
  , heyting
  -- * Re-exports
  , Quantale(..)
  , Meet(..)
) where

import safe Data.Bool
import safe Data.Connection.Conn
import safe Data.Functor.Contravariant
import safe Data.Int
import safe Data.Lattice
import safe Data.Maybe
import safe Data.Order
import safe Data.Order.Syntax
import safe Data.Semigroup.Quantale
import safe Data.Set (Set)
import safe Data.Universe.Class (Finite(..))
import safe Data.Word
import safe Prelude hiding (Ord(..), Bounded)
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set
import safe qualified Prelude as P


-------------------------------------------------------------------------------
-- Heyting algebras
-------------------------------------------------------------------------------

type HeytingLaw a = (Meet-Quantale) a

--prop_residuated :: (Heyting a, Eq a) => a -> a -> a -> Bool
--prop_residuated x y z = x /\ y <= z `iff` y <= (x ==> z) `iff` x <= (y ==> z)

-- | A Heyting algebra is a bounded, distributive lattice equipped with an implication operation.
--
-- /Laws/:
--
-- @
-- x '==>' x           = 'top'
-- x '/\' (x '==>' y)  = x '/\' y
-- y '/\' (x '==>' y)  = y
-- x '==>' (y '==>' z) = (x '/\' y) '==>' z
-- x '==>' (y '/\' z)  = (x '==>' y) '/\' (x '==>' z)
-- 'neg' (x '/\' y)    = 'neg' (x '\/' y)
-- 'neg' (x '\/' y)    = 'neg' x '/\' 'neg' y
-- (x '==>' y) '\/' x '<=' y
-- y '<=' (x '==>' x '/\' y)
-- x '<=' y => (z '==>' x) '<=' (z '==>' y)
-- x '<=' y => (x '==>' z) '<=' (y '==>' z)
-- x '<=' y <=> x '==>' y '==' 'top'
-- x '/\' y '<=' z <=> x '<=' (y '==>' z) <=> y '<=' (x '==>' z)
-- @
--
-- All this means that @x '==>' y@ is an [exponential object](https://ncatlab.org/nlab/show/exptopntial%2Bobject),
-- which makes any Heyting algebra a [cartesian closed category](https://ncatlab.org/nlab/show/cartesian%2Bclosed%2Bcategory).
--
class (Bounded a, HeytingLaw a) => Heyting a where

    infixr 0 <=>

    -- | Logical equivalence.
    --
    (<=>) :: a -> a -> a
    (<=>) x y = (x ==> y) /\ (y ==> x)

    infixr 2 `xor`

    -- | Exclusive or.
    --
    xor :: a -> a -> a
    xor x y = (x \/ y) /\ neg (x /\ y)

    -- | Logical negation.
    --
    -- @ 'neg' x = x '==>' 'bottom' @
    --
    -- Note that Heyting algebras needn't obey the law of the excluded middle:
    --
    -- > EQ \/ neg EQ = EQ \/ (EQ ==> LT) = EQ \/ LT = EQ /= GT
    --
    neg :: a -> a
    neg x = x ==> bottom


iff :: Heyting a => a -> a -> Bool
iff x y = top <~ (x <=> y)

-- | Implication from /a/ is the upper adjoint of conjunction with /a/.
--
heyting :: Heyting a => a -> Conn R a a
heyting a = ConnR (a /\) (a ==>)

instance Heyting Bool where
  neg = P.not

instance Heyting Ordering where
  neg LT = GT
  neg _ = LT

instance Heyting Word8
instance Heyting Word16
instance Heyting Word32
instance Heyting Word64
instance Heyting Word
instance Heyting Int8
instance Heyting Int16
instance Heyting Int32
instance Heyting Int64
instance Heyting Int
instance Heyting a => Heyting (Maybe a)

instance Finite a => Heyting (Predicate a) where
  neg (Predicate f) = Predicate $ \a -> neg (f a)
  (Predicate f) <=> (Predicate g) = Predicate $ \a -> f a <=> g a

-- |
-- Power set: the canonical example of a Boolean algebra
instance (TotalOrder a, Finite a) => Heyting (Set a) where
  --neg a = Set.fromList universe `Set.difference` a
  neg = Set.difference top
  x <=> y = Set.fromList
      [ z
      | z <- universeF
      , Set.member z x `iff` Set.member z y
      ]

instance (TotalOrder k, Finite k, Heyting a) => Heyting (Map.Map k a)
--instance (Heyting a, Quantale (Join a)) => Heyting (Down a)

--complement :: (Order a, Finite a) => Set.Set a -> Set.Set a
--complement xs = Set.fromList [ x | x <- universeF, Set.negMember x xs]
