{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
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
) where

import safe Data.Bool hiding (not)
import safe Data.Connection.Quantale
import safe Data.Int
import safe Data.Lattice
import safe Data.Maybe
import safe Data.Order
import safe Data.Set (Set)
import safe Data.Universe.Class (Finite(..))
import safe Data.Word
import safe Prelude hiding (Ord(..), Bounded, not)
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
-- 'not' (x '/\' y)    = 'not' (x '\/' y)
-- 'not' (x '\/' y)    = 'not' x '/\' 'not' y
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
class (Bounded a, Distributive a, HeytingLaw a) => Heyting a where

    -- | Logical negation.
    --
    -- @ 'not' x = x '==>' 'bottom' @
    --
    -- Note that Heyting algebras needn't obey the law of the excluded middle:
    --
    -- > EQ \/ not EQ = EQ \/ (EQ ==> LT) = EQ \/ LT = EQ /= GT
    --
    not :: a -> a
    not x = x ==> bottom

    infixr 0 <=>

    -- | Logical equivalence.
    --
    (<=>) :: a -> a -> a
    (<=>) x y = (x ==> y) /\ (y ==> x)

    infixr 2 `xor`

    -- | Exclusive or.
    --
    xor :: a -> a -> a
    xor x y = (x \/ y) /\ not (x /\ y)


iff :: Heyting a => a -> a -> Bool
iff x y = top <~ (x <=> y)

--infixr 3 `xor3`
--xor3 :: Heyting a => a -> a -> a -> a
--xor3 x y z = (x `xor` y `xor` z) /\ not (x /\ y /\ z)

instance Heyting Bool where
  not = P.not

instance Heyting Ordering where
  not LT = GT
  not _ = LT

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

-- |
-- Power set: the canonical example of a Boolean algebra
instance (Order a, Finite a) => Heyting (Set a) where
  --not a = Set.fromList universe `Set.difference` a
  not = Set.difference top
  x <=> y = Set.fromList
      [ z
      | z <- universeF
      , Set.member z x `iff` Set.member z y
      ]

instance (Order k, Finite k, Heyting a) => Heyting (Map.Map k a)
--instance (Heyting a, Quantale (Join a)) => Heyting (Down a)

--complement :: (Order a, Finite a) => Set.Set a -> Set.Set a
--complement xs = Set.fromList [ x | x <- universeF, Set.notMember x xs]
