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
module Data.Lattice (
  -- * Lattices
    Lattice
  , Semilattice(..)
  , bottom
  , (\/)
  , glb
  , join
  , top
  , (/\)
  , lub
  , meet
  -- * Heyting algebras
  , Biheyting
  , Heyting(..)
  -- ** HeytingL
  , (//)
  , neg
  , middle
  , equivL
  , regularL
  , booleanL
  , heytingL
  -- ** HeytingR
  , (\\)
  , non
  , boundary
  , equivR
  , regularR
  , booleanR
  , heytingR
) where

import safe Control.Category ((>>>))
import safe Control.Applicative
import safe Control.Monad.Logic hiding (join)
import safe Data.Bool hiding (not)
import safe Data.Connection.Conn
import safe Data.Connection.Class
import safe Data.Either
import safe Data.Functor.Contravariant
import safe Data.Foldable
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Order.Syntax
import safe Data.Int
import safe Data.Maybe
import safe Data.Monoid
import safe Data.Word
import safe GHC.TypeNats
--import safe Numeric.Natural
import safe Prelude hiding (Eq(..),Ord(..),Bounded)
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Map.Merge.Lazy as Map
import safe qualified Data.Set as Set
import safe qualified Data.Finite as F
import safe qualified Data.Universe.Class as U
import safe qualified Prelude as P

-------------------------------------------------------------------------------
-- Lattices
-------------------------------------------------------------------------------

-- | Lattice lattices.
--
-- A lattice is a partially ordered set in which every two elements have a unique join 
-- (least upper bound or supremum) and a unique meet (greatest lower bound or infimum). 
--
-- These operations may in turn be defined by the lower and upper adjoints to the unique
-- function /a -> (a, a)/.
--
-- /Associativity/
--
-- @
-- x '\/' (y '\/' z) = (x '\/' y) '\/' z
-- x '/\' (y '/\' z) = (x '/\' y) '/\' z
-- @
--
-- /Commutativity/
--
-- @
-- x '\/' y = y '\/' x
-- x '/\' y = y '/\' x
-- @
--
-- /Idempotency/
--
-- @
-- x '\/' x = x
-- x '/\' x = x
-- @
--
-- /<http://en.wikipedia.org/wiki/Absorption_law Absorption>/
--
-- @
-- (x '\/' y) '/\' y = y
-- (x '/\' y) '\/' y = y
-- @
--
-- Note that distributivity is _not_ a requirement for a lattice.
-- However when /a/ is distributive we have;
-- 
-- @
-- 'glb' x y z = 'lub' x y z
-- @
--
-- See <http://en.wikipedia.org/wiki/Lattice_(order)>.
--
type Lattice a = (Semilattice 'L a, Semilattice 'R a)

--class (Bounded k a, Directed k a) => Semilattice k a where
class Bounded k a => Semilattice k a where

    --lattice :: Conn k (Open k a) a
    --lattice = ConnL (foldr (\/) minimal) upper
   
    --TODO: g should be injecting upper/lower sets of a, not just a
    lattice :: Conn k (Logic a) a
    default lattice :: (Bounded 'L a, Bounded 'R a) => Conn k (Logic a) a
    lattice = Conn (foldr (\/) minimal) pure (foldr (/\) maximal)

-- | Take the lattice supremum of a collection.
-- 
join :: (Semilattice 'L a, Foldable f) => f a -> a
join = lowerL lattice . forwards

-- | Take the lattice infimum of a collection.
-- 
meet :: (Semilattice 'R a, Foldable f) => f a -> a
meet = upperR lattice . forwards

-- | The minimal element of a lattice.
--
-- > bottom \/ x = x
-- > bottom /\ x = bottom
--
bottom :: Semilattice 'L a => a
bottom = join $ logic (const id)

-- | The maximal element of a lattice.
--
top :: Semilattice 'R a => a
top = meet $ logic (const id)

-- | Obtain an 'Free' using a 'Data.Foldable.foldr'.
--
-- >>> observeAll $ forwards [0..4]
-- [0,1,2,3,4]
-- >>> F.foldl' (flip (:)) [] $ forwards [0..4]
-- [4,3,2,1,0]
--
forwards :: Foldable f => f a -> Logic a
forwards f = logic (\ h z -> foldr h z f)
{-# INLINE forwards #-}


-------------------------------------------------------------------------------
-- Heyting algebras
-------------------------------------------------------------------------------

-- | A < https://ncatlab.org/nlab/show/co-Heyting+algebra bi-Heyting algebra >.
--
type Biheyting a = (Heyting 'L a, Heyting 'R a)

-- | A Heyting algebra is a bounded, distributive lattice equipped with an implication operation.
--
-- /Heyting 'L/:
--
-- Implication from /a/ is the upper adjoint of conjunction with /a/:
-- 
-- > x <= a // y <=> a /\ x <= y
--
-- Note that Heyting algebras needn't obey the law of the excluded middle:
--
-- > EQ \/ neg EQ = EQ \/ EQ // LT = EQ \/ LT = EQ /= GT
--
-- See < https://ncatlab.org/nlab/show/Heyting+algebra >
--
-- /Heyting 'R/:
-- 
-- Co-implication to /a/ is the lower adjoint of disjunction with /a/:
--
-- > x \\ a <= y <=> x <= y \/ a
--
-- Similarly, co-Heyting algebras needn't obey the law of non-contradiction:
--
-- > EQ /\ non EQ = EQ /\ GT \\ EQ = EQ /\ GT = EQ /= LT
--
-- See < https://ncatlab.org/nlab/show/co-Heyting+algebra >
--
class Lattice a => Heyting k a where
    
    -- | The defining connection of a (co-)Heyting algebra.
    --
    heyting :: a -> Conn k a a


infixr 8 // -- same as ^

-- | Logical implication:
--
-- \( a \Rightarrow b = \vee \{x \mid x \wedge a \leq b \} \)
--
-- /Laws/:
--
-- > x /\ y <= z <=> x <= y // z
-- > x // y <= x // (y \/ z)
-- > x <= y => z // x <= z // y
-- > y <= x // (x /\ y)
-- > x <= y <=> x // y = top
-- > (x \/ z) // y <= x // y
-- > (x /\ y) // z = x // y // z
-- > x // (y /\ z) = x // y /\ x // z
-- > x /\ x // y = x /\ y
--
-- >>> False \\ False
-- True
-- >>> False \\ True
-- True
-- >>> True \\ False
-- False
-- >>> True \\ True
-- True
--
(//) :: Heyting 'L a => a -> a -> a
(//) = embed @'L . heyting

-- | Logical negation.
--
-- @ 'neg' x = x '//' 'bottom' @
--
-- /Laws/:
--
-- > neg bottom = top
-- > neg top = bottom
-- > x <= neg (neg x)
-- > neg (x \/ y) <= neg x
-- > neg (x // y) = neg (neg x) /\ neg y
-- > neg (x \/ y) = neg x /\ neg y
-- > x /\ neg x = bottom
-- > neg (neg (neg x)) = neg x
-- > neg (neg (x \/ neg x)) = top
--
-- Some logics may in addition obey < https://ncatlab.org/nlab/show/De+Morgan+Heyting+algebra De Morgan conditions >.
--
neg :: Heyting 'L a => a -> a
neg x = x // bottom

-- | The Heyting (< https://ncatlab.org/nlab/show/excluded+middle not necessarily excluded>) middle operator.
--
middle :: Heyting 'L a => a -> a
middle x = x \/ neg x

-- | Intuitionistic equivalence.
--
-- When /a=Bool/ this is 'if-and-only-if'.
--
equivL :: Heyting 'L a => a -> a -> a
equivL x y = (x // y) /\ (y // x)

-- | Check that /x/ is a < https://ncatlab.org/nlab/show/regular+element regular element >.
--
regularL :: Heyting 'L a => a -> Bool
regularL x = x == (neg . neg) x

-- | A default Heyting algebra instance for 'boolean'.
--
-- Every Heyting algebra contains a Boolean algebra.
--
-- Double negation is a meet-preserving monad.
--
booleanL :: Heyting 'L a => Conn 'L a a
booleanL = 
  let
    inj x = if regularL x then x else bottom

  in 
    ConnL (neg . neg) inj

-- | Default constructor for a Heyting algebra.
--
heytingL :: Lattice a => (a -> a -> a) -> a -> ConnL a a
heytingL f a = ConnL (/\ a) (f a)

infixl 8 \\ -- same as ^

-- | Logical co-implication:
--
-- \( a \Rightarrow b = \wedge \{x \mid a \leq b \vee x \} \)
--
-- /Laws/:
-- 
-- > x \\ y <= z <=> x <= y \/ z
-- > x \\ y >= (x /\ z) \\ y
-- > x >= y => x \\ z >= y \\ z
-- > x >= x \\ y
-- > x >= y <=> y \\ x = bottom
-- > x \\ (y /\ z) >= x \\ y
-- > z \\ (x \/ y) = z \\ x \\ y
-- > (y \/ z) \\ x = y \\ x \/ z \\ x
-- > x \/ y \\ x = x \/ y
--
-- >>> False \\ False
-- False
-- >>> False \\ True
-- False
-- >>> True \\ False
-- True
-- >>> True \\ True
-- False
-- 
(\\) :: Heyting 'R a => a -> a -> a
(\\) = flip $ embed @'R . heyting

-- | Logical < https://ncatlab.org/nlab/show/co-Heyting+negation co-negation >.
--
-- @ 'non' x = 'top' '\\' x @
--
-- /Laws/:
-- 
-- > non bottom = top
-- > non top = bottom
-- > x >= non (non x)
-- > non (x /\ y) >= non x
-- > non (y \\ x) = non (non x) \/ non y
-- > non (x /\ y) = non x \/ non y
-- > x \/ non x = top
-- > non (non (non x)) = non x
-- > non (non (x /\ non x)) = bottom
--
non :: Heyting 'R a => a -> a
non x = top \\ x

-- | The co-Heyting < https://ncatlab.org/nlab/show/co-Heyting+boundary boundary > operator.    
--
-- > x = boundary x \/ (non . non) x
-- > boundary (x /\ y) = (boundary x /\ y) \/ (x /\ boundary y)  -- (Leibniz rule)
-- > boundary (x \/ y) \/ boundary (x /\ y) = boundary x \/ boundary y
--
boundary :: Heyting 'R a => a -> a
boundary x = x /\ non x

-- | Intuitionistic co-equivalence.
--
equivR :: Heyting 'R a => a -> a -> a
equivR x y = (x \\ y) \/ (y \\ x)

-- | Check that /x/ is a < https://ncatlab.org/nlab/show/regular+element co-regular element >.
--
regularR :: Heyting 'R a => a -> Bool
regularR x = x == (non . non) x

-- | A default co-Heyting algebra instance for 'boolean'.
--
-- Every co-Heyting algebra contains a Boolean algebra.
--
-- Double co-negation is a join-preserving comonad.
--
booleanR :: Heyting 'R a => Conn 'R a a
booleanR =
  let 
    inj x = if regularR x then x else top

  in
    ConnR inj (non . non)

-- | Default constructor for a co-Heyting algebra.
--
heytingR :: Lattice a => (a -> a -> a) -> a -> ConnR a a
heytingR f a = ConnR (`f` a) (a \/)

--boolean :: Biheyting a => Conn k a a
--boolean = Conn (neg . neg) id (non . non)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

latticeL :: Bounded 'L a => Conn 'L (Logic a) a
latticeL = ConnL (foldr (\/) minimal) pure

latticeR :: Bounded 'R a => Conn 'R (Logic a) a
latticeR = ConnR pure (foldr (/\) maximal)

instance Semilattice k ()
instance Semilattice k Bool
instance Semilattice k Ordering
instance Semilattice k Word8
instance Semilattice k Word16
instance Semilattice k Word32
instance Semilattice k Word64
instance Semilattice k Word
instance Semilattice k Int8
instance Semilattice k Int16
instance Semilattice k Int32
instance Semilattice k Int64
instance Semilattice k Int
instance Semilattice k Float
instance Semilattice k Double
instance Semilattice k Rational
instance Semilattice k Positive
instance KnownNat n => Semilattice k (F.Finite n)

--instance (Semilattice 'L a) => Semilattice 'L (Maybe a) where lattice = latticeL
--instance (Semilattice 'R a) => Semilattice 'R (Maybe a) where lattice = latticeR
instance (Eq a, Connection 'L (a,a) a) => Semilattice 'L (Maybe a) where
  lattice = latticeL

instance (Eq a, Bounded 'R a) => Semilattice 'R (Maybe a) where
  lattice = latticeR

instance (Eq a, Connection 'L (a,a) a) => Semilattice 'L (Extended a) where
  lattice = ConnL (foldr (\/) minimal) pure

instance (Eq a, Connection 'R (a,a) a) => Semilattice 'R (Extended a) where
  lattice = ConnR pure (foldr (/\) maximal)

--instance (Lattice a, Lattice b) => Semilattice k (Either a b) 
instance (Eq a, Eq b, Bounded 'L a, Connection 'L (b,b) b) => Semilattice 'L (Either a b) where 
  lattice = ConnL (foldr (\/) minimal) pure

instance (Eq a, Eq b, Connection 'R (a,a) a, Bounded 'R b) => Semilattice 'R (Either a b) where
  lattice = ConnR pure (foldr (/\) maximal)

--instance Semilattice k a => Semilattice k (Extended a)
instance (Lattice a, Lattice b) => Semilattice k (a, b)
instance (U.Finite a, Lattice b) => Semilattice k (a -> b) 

deriving via (a -> a) instance (U.Finite a, Lattice a) => Semilattice k (Endo a)
deriving via (a -> b) instance (U.Finite a, Lattice b) => Semilattice k (Op b a)
deriving via (Op Bool a) instance (U.Finite a) => Semilattice k (Predicate a)

instance (Total a) => Semilattice 'L (Set.Set a) where lattice = latticeL
instance (Total a, U.Finite a) => Semilattice 'R (Set.Set a) where lattice = latticeR

instance Semilattice k IntSet.IntSet

instance (Total a, Semilattice 'L b) => Semilattice 'L (Map.Map a b) where lattice = latticeL
instance (Total a, U.Finite a, Semilattice 'R b) => Semilattice 'R (Map.Map a b) where lattice = latticeR

instance (Semilattice 'L a) => Semilattice 'L (IntMap.IntMap a) where lattice = latticeL
instance (Semilattice 'R a) => Semilattice 'R (IntMap.IntMap a) where lattice = latticeR


impliesL :: (Total a, P.Bounded a) => a -> a -> a
impliesL x y = if x > y then y else P.maxBound

impliesR :: (Total a, P.Bounded a) => a -> a -> a
impliesR x y = if y < x then x else P.minBound

instance Heyting 'L () where heyting = heytingL impliesL
instance Heyting 'L Bool where heyting = heytingL impliesL
instance Heyting 'L Ordering where heyting = heytingL impliesL
instance Heyting 'L Word8 where heyting = heytingL impliesL
instance Heyting 'L Word16 where heyting = heytingL impliesL
instance Heyting 'L Word32 where heyting = heytingL impliesL
instance Heyting 'L Word64 where heyting = heytingL impliesL
instance Heyting 'L Word where heyting = heytingL impliesL
instance Heyting 'L Int8 where heyting = heytingL impliesL
instance Heyting 'L Int16 where heyting = heytingL impliesL
instance Heyting 'L Int32 where heyting = heytingL impliesL
instance Heyting 'L Int64 where heyting = heytingL impliesL
instance Heyting 'L Int where heyting = heytingL impliesL
instance KnownNat n => Heyting 'L (F.Finite n) where heyting = heytingL impliesL

instance Heyting 'R () where heyting = heytingR impliesR
instance Heyting 'R Bool where heyting = heytingR impliesR
instance Heyting 'R Ordering where heyting = heytingR impliesR
instance Heyting 'R Word8 where heyting = heytingR impliesR
instance Heyting 'R Word16 where heyting = heytingR impliesR
instance Heyting 'R Word32 where heyting = heytingR impliesR
instance Heyting 'R Word64 where heyting = heytingR impliesR
instance Heyting 'R Word where heyting = heytingR impliesR
instance Heyting 'R Int8 where heyting = heytingR impliesR
instance Heyting 'R Int16 where heyting = heytingR impliesR
instance Heyting 'R Int32 where heyting = heytingR impliesR
instance Heyting 'R Int64 where heyting = heytingR impliesR
instance Heyting 'R Int where heyting = heytingR impliesR
instance KnownNat n => Heyting 'R (F.Finite n) where heyting = heytingR impliesR

instance (U.Finite a, Biheyting b) => Heyting 'L (a -> b) where
  heyting = heytingL $ liftA2 (//)

instance (U.Finite a, Biheyting b) => Heyting 'R (a -> b) where
  heyting = heytingR $ liftA2 (\\)

deriving via (a -> a) instance (U.Finite a, Biheyting a) => Heyting 'L (Endo a)
deriving via (a -> a) instance (U.Finite a, Biheyting a) => Heyting 'R (Endo a)
deriving via (a -> b) instance (U.Finite a, Biheyting b) => Heyting 'L (Op b a)
deriving via (a -> b) instance (U.Finite a, Biheyting b) => Heyting 'R (Op b a)
deriving via (Op Bool a) instance (U.Finite a) => Heyting 'L (Predicate a)
deriving via (Op Bool a) instance (U.Finite a) => Heyting 'R (Predicate a)

-- |
-- Subdirectly irreducible Heyting algebra.
instance Heyting 'L a => Heyting 'L (Lowered a) where
  heyting = heytingL f where

    (Left a)  `f` (Left b) | a <= b    = top
                           | otherwise = Left (a // b)
    (Right _) `f` a                    = a
    --_         `f` (Right _)            = top

instance Heyting 'L a => Heyting 'L (Lifted a) where
  heyting = heytingL f where
    f (Right a) (Right b) = Right (a // b)
    f (Left _)   _        = Right top
    f _         (Left _)  = bottom

instance Heyting 'L a => Heyting 'L (Maybe a) where
  heyting = heytingL f where
    f (Just a) (Just b)   = Just (a // b)
    f Nothing  _          = Just top
    f _        Nothing    = Nothing

instance Heyting 'L a => Heyting 'L (Extended a) where
  heyting = heytingL f where

    Extended a `f` Extended b | a <= b    = Top
                              | otherwise = Extended (a // b)
    Top        `f` a          = a
    _          `f` Top        = Top
    Bottom     `f` _          = Top
    _          `f` Bottom     = Bottom
 
instance (Total a, U.Finite a) => Heyting 'L (Set.Set a) where
  heyting = heytingL Set.difference

instance (Total a, U.Finite a, Heyting 'L b) => Heyting 'L (Map.Map a b) where

  heyting = heytingL $ \a b ->
    let
      x = Map.merge
            Map.dropMissing                    -- drop if an element is missing in @b@
            (Map.mapMissing (\_ _ -> top))     -- put @top@ if an element is missing in @a@
            (Map.zipWithMatched (\_ -> (//) )) -- merge  matching elements with @`implies`@
            a b

      y = Map.fromList [(k, top) | k <- U.universeF, not (Map.member k a), not (Map.member k b) ]
        -- for elements which are not in a, nor in b add
        -- a @top@ key
    in
      Map.union x y
{-
-- TODO: compare performance
impliesMap a b =
  Map.intersection (`implies`) a b
    `Map.union` Map.map (const top) (Map.difference b a)
    `Map.union` Map.fromList [(k, top) | k <- universeF, not (Map.member k a), not (Map.member k b)]
-}


{-
---------------------------------------------------------------------
-- DerivingVia
---------------------------------------------------------------------

instance (Total a, Fractional a) => Lattice (N5 a) where
  (\/) = liftA2 $ \x y -> maybe (1 / 0) (bool y x . (>= EQ)) (pcompare x y)
  (/\) = liftA2 $ \x y -> maybe (-1 / 0) (bool y x . (<= EQ)) (pcompare x y)

instance (Total a, Fractional a) => Bounded (N5 a) where
  bottom = N5 $ -1/0
  top = N5 $ 1/0

instance Total a => Lattice (Base a) where
  (\/) = max
  (/\) = min

instance (Total a, P.Bounded a) => Bounded (Base a) where
  bottom = Base P.minBound
  top = Base P.maxBound

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------


instance Lattice a => Lattice (Down a) where
  Down x \/ Down y = Down $ x /\ y
  Down x /\ Down y = Down $ x \/ y

instance Bounded a => Bounded (Down a) where
  bottom = Down top
  top = Down bottom

instance Lattice ()
instance Bounded ()
instance Lattice Bool
instance Bounded Bool
instance Lattice Ordering 
instance Bounded Ordering
instance Lattice Word8
instance Bounded Word8
instance Lattice Word16
instance Bounded Word16
instance Lattice Word32
instance Bounded Word32
instance Lattice Word64
instance Bounded Word64
instance Lattice Word
instance Bounded Word
instance Lattice Natural
instance Lattice Positive
instance Bounded Positive

instance Lattice Int8
instance Bounded Int8
instance Lattice Int16
instance Bounded Int16
instance Lattice Int32
instance Bounded Int32
instance Lattice Int64
instance Bounded Int64
instance Lattice Int
instance Bounded Int
instance Lattice Integer
instance Lattice Rational
instance Bounded Rational

instance Lattice (F.Finite n)
instance KnownNat n => Bounded (F.Finite n)

instance Lattice Float
instance Bounded Float
instance Lattice Double
instance Bounded Double

joinMaybe :: Lattice a => Maybe a -> Maybe a -> Maybe a
joinMaybe (Just x) (Just y) = Just (x \/ y)
joinMaybe u@(Just _) _ = u
joinMaybe _ u@(Just _) = u
joinMaybe Nothing Nothing = Nothing

meetMaybe :: Lattice a => Maybe a -> Maybe a -> Maybe a
meetMaybe Nothing Nothing = Nothing
meetMaybe Nothing _ = Nothing
meetMaybe _ Nothing = Nothing
meetMaybe (Just x) (Just y) = Just (x /\ y)

instance (Lattice a) => Lattice (Maybe a) where
  (\/) = joinMaybe
  (/\) = meetMaybe

instance (Bounded a) => Bounded (Maybe a) where
  bottom = Nothing
  top = Just top

joinEither :: (Lattice a, Lattice b) => Either a b -> Either a b -> Either a b
joinEither (Right x) (Right y) = Right (x \/ y)
joinEither u@(Right _) _ = u
joinEither _ u@(Right _) = u
joinEither (Left x) (Left y) = Left (x \/ y)

meetEither :: (Lattice a, Lattice b) => Either a b -> Either a b -> Either a b
meetEither (Left x) (Left y) = Left (x /\ y)
meetEither l@(Left _) _ = l
meetEither _ l@(Left _) = l
meetEither (Right x) (Right y) = Right (x /\ y)

instance (Lattice a, Lattice b) => Lattice (Either a b) where
  (\/) = joinEither
  (/\) = meetEither

instance (Bounded a, Bounded b) => Bounded (Either a b) where
  bottom = Left bottom
  top = Right top

instance Lattice a => Lattice (Extended a) where
  (\/) = joinExtended
  (/\) = meetExtended

instance Lattice a => Bounded (Extended a) where
  bottom = Bottom
  top = Top

joinExtended :: Lattice a => Extended a -> Extended a -> Extended a
joinExtended Top          _            = Top
joinExtended _            Top          = Top
joinExtended (Extended x) (Extended y) = Extended (x \/ y)
joinExtended Bottom       y            = y
joinExtended x            Bottom       = x

meetExtended :: Lattice a => Extended a -> Extended a -> Extended a
meetExtended Top          y            = y
meetExtended x            Top          = x
meetExtended (Extended x) (Extended y) = Extended (x /\ y)
meetExtended Bottom       _            = Bottom
meetExtended _            Bottom       = Bottom

instance (Lattice a, Lattice b) => Lattice (a, b) where
  (x1, y1) \/ (x2, y2) = (x1 \/ x2, y1 \/ y2)
  (x1, y1) /\ (x2, y2) = (x1 /\ x2, y1 /\ y2)

instance (Bounded a, Bounded b) => Bounded (a, b) where
  bottom = (bottom, bottom)
  top = (top, top)

instance (Finite a, Lattice b) => Lattice (a -> b) where
  (\/) = liftA2 (\/)
  (/\) = liftA2 (/\)
 
instance (Finite a, Bounded b) => Bounded (a -> b) where
  bottom = pure bottom
  top = pure top

deriving via (a -> a) instance (Finite a, Lattice a) => Lattice (Endo a)
deriving via (a -> a) instance (Finite a, Bounded a) => Bounded (Endo a)

deriving via (a -> b) instance (Finite a, Lattice b) => Lattice (Op b a)
deriving via (a -> b) instance (Finite a, Bounded b) => Bounded (Op b a)

deriving via (Op Bool a) instance (Finite a) => Lattice (Predicate a)
deriving via (Op Bool a) instance (Finite a) => Bounded (Predicate a)

instance Total a => Lattice (Set.Set a) where
  (\/) = Set.union 
  (/\) = Set.intersection 

instance (Total a, Finite a) => Bounded (Set.Set a) where
  bottom = Set.empty
  top = Set.fromList universeF

instance Lattice IntSet.IntSet where
  (\/) = IntSet.union 
  (/\) = IntSet.intersection 

instance Bounded IntSet.IntSet where
  bottom = IntSet.empty
  top = IntSet.fromList universeF

instance (Total k, Lattice a) => Lattice (Map.Map k a) where
  (\/) = Map.union (\/)
  (/\) = Map.intersection (/\)

instance (Total k, Finite k, Bounded a) => Bounded (Map.Map k a) where
  bottom = Map.empty
  top = Map.fromList (universeF `zip` repeat top)

instance (Lattice a) => Lattice (IntMap.IntMap a) where
  (\/) = IntMap.union (\/)
  (/\) = IntMap.intersection (/\)

instance (Bounded a) => Bounded (IntMap.IntMap a) where
  bottom = IntMap.empty
  top = IntMap.fromList (universeF `zip` repeat top)

-}

{-
instance (Applicative m, Lattice r) => Lattice (ContT r m a) where
  (<>) = liftA2 joinCont

instance (Applicative m, Bounded r) => Bounded (ContT r m a) where
  mempty = pure . ContT . const $ pure bottom

instance Monad m => Lattice (SelectT r m a) where
  (<>) = liftA2 joinSelect

instance MonadPlus m => Bounded (SelectT r m a)) where
  bottom = pure empty

joinCont :: (Applicative m, Lattice r) => ContT r m a -> ContT r m a -> ContT r m a
joinCont (ContT f) (ContT g) = ContT $ \p -> liftA2 (\/) (f p) (g p) 

joinSelect :: Monad m => SelectT r m b -> SelectT r m b -> SelectT r m b
joinSelect x y = branch x y >>= id
  where
    ifM c x y = c >>= \b -> if b then x else y
    branch x y = SelectT $ \p -> ifM ((== top) <$> p x) (pure x) (pure y)

-}

{-
-- | Reduce a lattice expression:
-- 
-- > (a11 /\ ... /\ a1m) \/ (a21 /\ ... /\ a2n) \/ ...
--
reduce1 :: (Lattice a, Foldable1 f, Functor f) => f (f a) -> a
reduce1 = join1 . fmap meet1
{-# INLINE reduce1 #-}

-- | The join of a list of join-semilattice elements (of length at least top)
join1 :: Foldable1 f => Lattice a => f a -> a
join1 = join1 id

-- | Fold over a non-empty collection using the join operation of an arbitrary join semilattice.
--
join1 :: Foldable1 t => Lattice a => (b -> a) -> t b -> a
join1 f = foldMap1 f
{-# INLINE join1 #-}


-- | The meet of a non-empty collection of meet-semilattice elements.
meet1 :: Foldable1 f => Lattice a => f a -> a
meet1 = meet1 id

-- | Fold over a non-empty collection using the multiplicative operation of a semiring.
--
-- As the collection is non-empty this does not require a distinct multiplicative unit:
--
-- >>> meet1 Just $ 1 :| [2..5 :: Int]
-- Just 120
-- >>> meet1 First $ 1 :| [2..(5 :: Int)]
-- First {getFirst = 15}
-- >>> meet1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Just 11}
--
meet1 :: Foldable1 f => Lattice a => (b -> a) -> f b -> a
meet1 f = foldMap1 f
{-# INLINE meet1 #-}
-}
