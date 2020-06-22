{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE StandaloneDeriving         #-}

-- | < https://ncatlab.org/nlab/show/quantale >
module Data.Semigroup.Quantale (
    type UnitalQuantale
  , Quantale(..)
  , (<==), (==>)
) where

import safe Control.Applicative
import safe Data.Connection.Conn
import safe Data.Functor.Contravariant
import safe Data.Monoid
import safe Data.Order
import safe Data.Order.Syntax
import safe Data.Int
import safe Data.Word
import safe Data.Semigroup
import safe Data.Semigroup.Join
import safe Data.Universe.Class (Finite(..))
import safe Prelude hiding (Eq(..), Ord(..), floor, ceiling, until)
import safe qualified Data.Order.Float as F32
import safe qualified Data.Order.Double as F64
import safe qualified Data.Map as Map
import safe qualified Data.Map.Merge.Lazy as Map
import safe qualified Data.Set as Set
import safe qualified Prelude as P

-------------------------------------------------------------------------------
-- Quantales
-------------------------------------------------------------------------------

type UnitalQuantale a = (Monoid a, Quantale a)

-- | A residuated, partially ordered semigroup.
--
-- In the interest of broader usability we relax the common definition slightly
-- and use the term 'quantale' to describe any residuated, partially ordered semigroup. 
-- This admits instances of hoops and triangular (co)-norms.
-- 
-- Laws:
--
-- > x \\ x = mempty  
-- > x <~ y iff mempty = x \\ y
-- > x <> (x \\ y) = y <> (y \\ x)  
-- > (x <> y) \\ z = y \\ (x \\ z) (currying)
-- > x <> y <~ z iff y <~ x \\ z iff x <~ z // y.
--
-- See < https://ncatlab.org/nlab/show/quantale >.
--
-- TODO: There are several additional properties that apply when the poset structure
-- is lattice-ordered (i.e. a residuated lattice) or when the semigroup is a 
-- monoid or semiring.
--
class Semigroup a => Quantale a where
    residL :: a -> ConnL a a
    residL x = ConnL (<>x) (//x)
    
    residR :: a -> ConnR a a
    residR x = ConnR (x<>) (x\\)

    infixl 5 // 
    (//) :: a -> a -> a
    x // y = lowerL (residL x) y

    infixr 5 \\
    (\\) :: a -> a -> a
    x \\ y = upperR (residR x) y

infixr 1 ==>

-- | Logical implication.
--
-- @
-- x '==>' x           = 'top'
-- x '/\' (x '==>' y)  = x '/\' y
-- y '/\' (x '==>' y)  = y
-- x '==>' (y '==>' z) = (x '/\' y) '==>' z
-- x '==>' (y '/\' z)  = (x '==>' y) '/\' (x '==>' z)
-- 'meetLe' ((x '==>' y) '\/' x) y
-- 'meetLe' y (x '==>' x '/\' y)
-- 'meetLe' x y => 'meetLe' (z '==>' x) (z '==>' y)
-- 'meetLe' x y => 'meetLe' (x '==>' z) (y '==>' z)
-- 'meetLe' x y <=> x '==>' y '==' 'top'
-- 'meetLe' (x '/\' y) z <=> 'meetLe' x (y '==>' z)
-- @
--
-- See 'Data.Semilattice.Heyting.Heyting' for the laws.
--
(==>) :: (Meet-Quantale) a => a -> a -> a
(==>) x y = getMeet $ Meet x \\ Meet y

infixl 1 <==

(<==) :: (Meet-Quantale) a => a -> a -> a
(<==) x y = getMeet $ Meet x // Meet y

---------------------------------------------------------------------
-- DerivingVia
---------------------------------------------------------------------

instance (Applicative f, Quantale a) => Quantale (F1 f a) where
  F1 x // F1 y = F1 $ (//) <$> x <*> y 
  (\\) = flip (//)

instance (Applicative f, Applicative g, Quantale a) => Quantale (F2 f g a) where
  (//) = liftA2 (//)
  (\\) = flip (//)

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------


{-
--TODO: check compatibility w/ Semigroup instance
instance Quantale Ordering where
    LT \\ _ = GT
    EQ \\ LT = LT
    EQ \\ _ = GT
    GT \\ x = x

    (//) = flip (\\)
-}

instance Quantale All where
  All x \\ All y = All $ x <= y  
  (//) = flip (\\)

instance Quantale a => Quantale (r -> a) where
  (\\) = flip (//)
  (//) = liftA2 (//) 


instance (TotalOrder a, Bounded a) => Quantale (Min a) where
  x \\ y = if x P.> y then y else mempty

  (//) = flip (\\)

{-
instance Quantale a => Quantale (Maybe a) where
  residR = maybe (Conn (Nothing <>) (Nothing\\)) (mapped . residR)
  residL = maybe (Conn (<> Nothing) (//Nothing)) (mapped . residL)

instance Quantale (Sum Float) where
  x \\ y = y // x
  
  -- |
  --
  -- >>> maxOdd32 = Sum 1.6777215e7 :: Sum Float
  -- >>> (maxOdd32 + 2) - 2
  -- Sum {getSum = 1.6777214e7}
  -- >>> (maxOdd32 + 2) // 2
  -- Sum {getSum = 1.6777215e7}
  --
  (//) = liftA2 negFloat

instance Quantale (Sum Double) where
  x \\ y = y // x

  -- |
  --
  -- >>> maxOdd64 = Sum 9.007199254740991e15 :: Sum Double
  -- >>> (maxOdd64 + 2) - 2
  -- Sum {getSum = 9.00719925474099e15}
  -- >>> (maxOdd64 + 2) // 2
  -- Sum {getSum = 9.007199254740991e15}
  --
  (//) = liftA2 negDouble



negDouble :: Double -> Double -> Double
negDouble y x = if y ~~ x then 0 else w where
  z = y - x
  w = if z + x <~ y then up z (x+) y else F64.lower64 z (x+) y 
  up z g y = while (\x -> g x <~ y) (<~) (F64.shift 1) z

negFloat :: Float -> Float -> Float
negFloat y x = if y ~~ x then 0 else w where
  z = y - x
  w = if z + x <~ y then upper' z (x+) y else lower' z (x+) y 

-- @'lower'' x@ is the least element /y/ in the descending
-- chain such that @not $ f y '<~' x@.
--
lower' :: Preorder a => Float -> (Float -> a) -> a -> Float
lower' z f x = until (\y -> f y <~ x) (>~) (F32.shift $ -1) z

-- @'upper' y@ is the greatest element /x/ in the ascending
-- chain such that @g x '<~' y@.
--
upper' :: Preorder a => Float -> (Float -> a) -> a -> Float
upper' z g y = while (\x -> g x <~ y) (<~) (F32.shift 1) z


-}

--lower32 z f x = while (\y -> f y >~ x) (>~) (shift $ -1) z
--upper32 z g y = while (\x -> g x <~ y) (<~) (shift 1) z

{-
-- a \/ b = 1 − [(1 − a) /\ (1 − b)]
-- a /\ b = 1 − [(1 − a) \/ (1 − b)].
-}

---------------------------------------------------------------------
-- Meet-semilattice instances
---------------------------------------------------------------------

deriving via (F1 Meet (Min ())) instance Quantale (Meet ())
deriving via (F1 Meet (Min Word8)) instance Quantale (Meet Word8)
deriving via (F1 Meet (Min Word16)) instance Quantale (Meet Word16)
deriving via (F1 Meet (Min Word32)) instance Quantale (Meet Word32)
deriving via (F1 Meet (Min Word64)) instance Quantale (Meet Word64)
deriving via (F1 Meet (Min Word)) instance Quantale (Meet Word)
deriving via (F1 Meet (Min Int8)) instance Quantale (Meet Int8)
deriving via (F1 Meet (Min Int16)) instance Quantale (Meet Int16)
deriving via (F1 Meet (Min Int32)) instance Quantale (Meet Int32)
deriving via (F1 Meet (Min Int64)) instance Quantale (Meet Int64)
deriving via (F1 Meet (Min Int)) instance Quantale (Meet Int)
deriving via (F2 Meet Down (Join a)) instance Quantale (Join a) => Quantale (Meet (Down a))
deriving via (F2 Join Down (Meet a)) instance Quantale (Meet a) => Quantale (Join (Down a))
deriving via (F1 Meet (r -> Meet a)) instance Quantale (Meet a) => Quantale (Meet (r -> a))

instance Quantale (Meet Bool) where
  (\\) = liftA2 (<=)
  (//) = flip (\\)

instance Quantale (Meet Ordering) where
  (//) = flip (\\)
  (\\) = liftA2 impliesOrdering 
    where
      impliesOrdering LT _ = GT
      impliesOrdering EQ LT = LT
      impliesOrdering EQ _ = GT
      impliesOrdering GT x = x

instance UnitalQuantale (Meet a) => Quantale (Meet (Maybe a)) where
  (//) = flip (\\)
  (\\) = liftA2 impliesMaybe
    where
      impliesMaybe (Just a) (Just b) = Just (a ==> b)
      impliesMaybe Nothing  _        = Just top
      impliesMaybe _        Nothing  = Nothing

instance (Preorder a, UnitalQuantale (Meet a)) => Quantale (Meet (Either a a)) where
  (//) = flip (\\)
  (\\) = liftA2 impliesEither
    where
      impliesEither (Left _)  (Right _)  = Right top
      impliesEither (Right _) l@Left{}   = l
      impliesEither (Right u) (Right u') = Right $ u ==> u'
      impliesEither (Left l)  (Left l')  = case l ==> l' of
        ll' | ll' ~~ top -> Right top
            | otherwise  -> Left ll'

instance Quantale (Meet (Predicate a)) where
  (\\) = liftA2 $ \(Predicate f) (Predicate g) -> Predicate $ \a -> f a <= g a
  (//) = flip (\\)

instance TotalOrder a => Quantale (Meet (Set.Set a)) where
  (\\) = liftA2 (Set.\\)
  (//) = flip (\\)

instance (TotalOrder k, Finite k, UnitalQuantale (Meet a)) => Quantale (Meet (Map.Map k a)) where
  (\\) = liftA2 impliesMap
    where
      impliesMap a b = Map.union x y where
        x = Map.merge
          Map.dropMissing                    -- drop if an element is missing in @b@
          (Map.mapMissing (\_ _ -> top))     -- put @top@ if an element is missing in @a@
          (Map.zipWithMatched (\_ -> (==>))) -- merge  matching elements with @==>@
          a b

        y = Map.fromList [(k, top) | k <- universeF, not (Map.member k a), not (Map.member k b) ]
          -- for elements which are not in a, nor in b add
          -- a @top@ key
{- TODO: compare performance
impliesMap a b =
  Map.intersectionWith (==>) a b
    `Map.union` Map.map (const top) (Map.difference b a)
    `Map.union` Map.fromList [(k, top) | k <- universeF, not (Map.member k a), not (Map.member k b)]
-}


