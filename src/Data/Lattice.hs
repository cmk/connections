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
  -- ** SemilatticeL
  , type SemilatticeL
  , bottom
  , (\/)
  , glb
  , join
  -- ** SemilatticeR
  , type SemilatticeR
  , top
  , (/\)
  , lub
  , meet
  -- * Heyting algebras
  , Biheyting
  , Heyting(..)
  -- ** HeytingL
  , type HeytingL
  , (\\)
  , non
  , boundary
  , equivL
  , regularL
  , heytingL
  , booleanL
  -- ** HeytingR
  , type HeytingR
  , (//)
  , neg
  , middle
  , equivR
  , regularR
  , heytingR
  , booleanR
  -- * Boolean algebras
  , Boolean(..)
) where

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

-- | Lattices.
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
type Lattice a = (SemilatticeL a, SemilatticeR a)

-- | A convenience alias for a join semilattice.
type SemilatticeL = Semilattice 'L

-- | A convenience alias for a meet semilattice.
type SemilatticeR = Semilattice 'R

--class (Bounded k a, Directed k a) => Semilattice k a where
-- \( x \wedge (\vee_i y_i) \leq \vee_i (x \wedge y_i) \)

class Bounded k a => Semilattice k a where

    --lattice :: Conn k (Open k a) a
    --lattice = ConnL (foldr (\/) minimal) upper
   
    --TODO: g should be injecting upper/lower sets of a, not just a
    lattice :: Conn k (Logic a) a
    default lattice :: (Bounded 'L a, Bounded 'R a) => Conn k (Logic a) a
    lattice = Conn (foldr (\/) minimal) pure (foldr (/\) maximal)

-- | The minimal element of a lattice.
--
-- > bottom \/ x = x
-- > bottom /\ x = bottom
--
bottom :: SemilatticeL a => a
bottom = join $ logic (const id)

-- | Take the lattice supremum of a collection.
-- 
join :: (SemilatticeL a, Foldable f) => f a -> a
join = lowerL lattice . forwards

-- | The maximal element of a lattice.
--
top :: SemilatticeR a => a
top = meet $ logic (const id)

-- | Take the lattice infimum of a collection.
-- 
meet :: (SemilatticeR a, Foldable f) => f a -> a
meet = upperR lattice . forwards

-- | Obtain an 'Logic' using a 'Data.Foldable.foldr'.
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
type Biheyting a = (HeytingL a, HeytingR a)

-- | A convenience alias for a < https://ncatlab.org/nlab/show/co-Heyting+algebra co-Heyting algebra >.
--
type HeytingL = Heyting 'L

-- | A convenience alias for a Heyting algebra.
--
type HeytingR = Heyting 'R

-- | A Heyting algebra is a bounded, distributive lattice equipped with an implication operation.
--
-- /Heyting 'L/:
-- 
-- Co-implication to /a/ is the lower adjoint of disjunction with /a/:
--
-- > x \\ a <= y <=> x <= y \/ a
--
-- Note that co-Heyting algebras needn't obey the law of non-contradiction:
--
-- > EQ /\ non EQ = EQ /\ GT \\ EQ = EQ /\ GT = EQ /= LT
--
-- See < https://ncatlab.org/nlab/show/co-Heyting+algebra >
--
-- /Heyting 'R/:
--
-- Implication from /a/ is the upper adjoint of conjunction with /a/:
-- 
-- > x <= a // y <=> a /\ x <= y
--
-- Similarly, Heyting algebras needn't obey the law of the excluded middle:
--
-- > EQ \/ neg EQ = EQ \/ EQ // LT = EQ \/ LT = EQ /= GT
--
-- See < https://ncatlab.org/nlab/show/Heyting+algebra >
--
class Lattice a => Heyting k a where
    
    -- | The defining connection of a (co-)Heyting algebra.
    --
    -- /Laws/:
    --
    -- > heyting @'L a = ConnL (\\ a) (\/ a) 
    -- > heyting @'R a = ConnR (a /\) (a //)
    --
    heyting :: a -> Conn k a a



infixl 8 \\

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
-- For many collections (e.g. 'Data.Set.Set') '\\' coincides with the native 'Data.Set.\\' operator.
--
-- >>> :set -XOverloadedLists
-- >>> [GT,EQ] Set.\\ [LT]
-- fromList [EQ,GT]
-- >>> [GT,EQ] \\ [LT]
-- fromList [EQ,GT]
-- 
(\\) :: HeytingL a => a -> a -> a
(\\) = flip $ lowerL . heyting

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
non :: HeytingL a => a -> a
non x = top \\ x

-- | The co-Heyting < https://ncatlab.org/nlab/show/co-Heyting+boundary boundary > operator.    
--
-- > x = boundary x \/ (non . non) x
-- > boundary (x /\ y) = (boundary x /\ y) \/ (x /\ boundary y)  -- (Leibniz rule)
-- > boundary (x \/ y) \/ boundary (x /\ y) = boundary x \/ boundary y
--
boundary :: HeytingL a => a -> a
boundary x = x /\ non x

-- | Intuitionistic co-equivalence.
--
equivL :: HeytingL a => a -> a -> a
equivL x y = (x \\ y) \/ (y \\ x)

-- | Check that /x/ is a < https://ncatlab.org/nlab/show/regular+element co-regular element >.
--
regularL :: HeytingL a => a -> Bool
regularL x = x == (non . non) x

-- | An adjunction between a co-Heyting algebra and its Boolean sub-algebra.
--
-- Double negation is a join-preserving comonad.
--
booleanL :: HeytingL a => Conn 'L a a
booleanL =
  let 
    inj x = if regularL x then x else top

  in
    ConnL inj (non . non)

-- | Default constructor for a co-Heyting algebra.
--
heytingL :: Lattice a => (a -> a -> a) -> a -> ConnL a a
heytingL f a = ConnL (`f` a) (\/ a)

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
-- >>> False // False
-- True
-- >>> False // True
-- True
-- >>> True // False
-- False
-- >>> True // True
-- True
--
(//) :: HeytingR a => a -> a -> a
(//) x = upperR $ heyting x

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
neg :: HeytingR a => a -> a
neg x = x // bottom

-- | The Heyting (< https://ncatlab.org/nlab/show/excluded+middle not necessarily excluded>) middle operator.
--
middle :: HeytingR a => a -> a
middle x = x \/ neg x

-- | Intuitionistic equivalence.
--
-- When /a=Bool/ this is 'if-and-only-if'.
--
equivR :: HeytingR a => a -> a -> a
equivR x y = (x // y) /\ (y // x)

-- | Check that /x/ is a < https://ncatlab.org/nlab/show/regular+element regular element >.
--
regularR :: HeytingR a => a -> Bool
regularR x = x == (neg . neg) x

-- | An adjunction between a Heyting algebra and its Boolean sub-algebra.
--
-- Double negation is a meet-preserving monad.
--
booleanR :: HeytingR a => Conn 'R a a
booleanR = 
  let
    inj x = if regularR x then x else bottom

  in 
    ConnR (neg . neg) inj

-- | Default constructor for a Heyting algebra.
--
heytingR :: Lattice a => (a -> a -> a) -> a -> ConnR a a
heytingR f a = ConnR (a /\) (f a)

-------------------------------------------------------------------------------
-- Boolean algebras
-------------------------------------------------------------------------------


-- | < https://ncatlab.org/nlab/show/Boolean+algebra Boolean algebras >.
--
-- A Boolean algebra is a Bi-Heyting algebra which negation satisfies the law of
-- excluded middle:
--
-- > x \/ neg x = top
-- > x /\ non x = bottom 
-- > neg (neg x) = x
-- > non (non x) = x
-- > x <= y => neg y <= neg x
--
class Biheyting a => Boolean a where

    -- |
    -- > boolean :: ConnL a a = booleanL
    -- > boolean :: ConnR a a = booleanR
    --
    boolean :: Trip a a
    boolean = Conn (neg . neg) id (non . non)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

latticeL :: Bounded 'L a => ConnL (Logic a) a
latticeL = ConnL (foldr (\/) minimal) pure

latticeR :: Bounded 'R a => ConnR (Logic a) a
latticeR = ConnR pure (foldr (/\) maximal)

impliesL :: (Total a, P.Bounded a) => a -> a -> a
impliesL x y = if y < x then x else P.minBound

impliesR :: (Total a, P.Bounded a) => a -> a -> a
impliesR x y = if x > y then y else P.maxBound

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


instance Boolean ()
instance Boolean Bool

-------------------------------------------------------------------------------
-- Instances: sum types
-------------------------------------------------------------------------------


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

-- |
-- Subdirectly irreducible Heyting algebra.
instance Heyting 'R a => Heyting 'R (Lowered a) where
  heyting = heytingR f where

    (Left a)  `f` (Left b) | a <= b    = top
                           | otherwise = Left (a // b)
    (Right _) `f` a                    = a
    _         `f` (Right _)            = top

instance Heyting 'R a => Heyting 'R (Lifted a) where
  heyting = heytingR f where
    f (Right a) (Right b) = Right (a // b)
    f (Left _)   _        = Right top
    f _         (Left _)  = bottom

instance Heyting 'R a => Heyting 'R (Maybe a) where
  heyting = heytingR f where
    f (Just a) (Just b)   = Just (a // b)
    f Nothing  _          = Just top
    f _        Nothing    = Nothing

--instance Semilattice k a => Semilattice k (Extended a)
instance Heyting 'R a => Heyting 'R (Extended a) where
  heyting = heytingR f where

    Extended a `f` Extended b | a <= b    = Top
                              | otherwise = Extended (a // b)
    Top        `f` a          = a
    _          `f` Top        = Top
    Bottom     `f` _          = Top
    _          `f` Bottom     = Bottom


-------------------------------------------------------------------------------
-- Instances: product types
-------------------------------------------------------------------------------

instance (Lattice a, Lattice b) => Semilattice k (a, b)

instance (Heyting k a, Heyting k b) => Heyting k (a, b) where
  heyting (a,b) = heyting a `strong` heyting b

instance (Boolean a, Boolean b) => Boolean (a, b)

-------------------------------------------------------------------------------
-- Instances: function types
-------------------------------------------------------------------------------

instance (U.Finite a, Lattice b) => Semilattice k (a -> b)
 
instance (U.Finite a, Biheyting b) => Heyting 'L (a -> b) where
  heyting = heytingL $ liftA2 (\\)

instance (U.Finite a, Biheyting b) => Heyting 'R (a -> b) where
  heyting = heytingR $ liftA2 (//)

instance (U.Finite a, Boolean b) => Boolean (a -> b)

deriving via (a -> a) instance (U.Finite a, Lattice a) => Semilattice k (Endo a)
deriving via (a -> a) instance (U.Finite a, Biheyting a) => Heyting 'L (Endo a)
deriving via (a -> a) instance (U.Finite a, Biheyting a) => Heyting 'R (Endo a)
instance (U.Finite a, Boolean a) => Boolean (Endo a)

deriving via (a -> b) instance (U.Finite a, Lattice b) => Semilattice k (Op b a)
deriving via (a -> b) instance (U.Finite a, Biheyting b) => Heyting 'L (Op b a)
deriving via (a -> b) instance (U.Finite a, Biheyting b) => Heyting 'R (Op b a)
instance (U.Finite a, Boolean b) => Boolean (Op b a)

deriving via (Op Bool a) instance (U.Finite a) => Semilattice k (Predicate a)
deriving via (Op Bool a) instance (U.Finite a) => Heyting 'L (Predicate a)
deriving via (Op Bool a) instance (U.Finite a) => Heyting 'R (Predicate a)
instance (U.Finite a) => Boolean (Predicate a)

-------------------------------------------------------------------------------
-- Instances: collections
-------------------------------------------------------------------------------

instance (Total a) => Semilattice 'L (Set.Set a) where lattice = latticeL
instance (Total a, U.Finite a) => Semilattice 'R (Set.Set a) where lattice = latticeR

instance Semilattice k IntSet.IntSet

instance (Total a, Semilattice 'L b) => Semilattice 'L (Map.Map a b) where lattice = latticeL
instance (Total a, U.Finite a, Semilattice 'R b) => Semilattice 'R (Map.Map a b) where lattice = latticeR

instance (Semilattice 'L a) => Semilattice 'L (IntMap.IntMap a) where lattice = latticeL
instance (Semilattice 'R a) => Semilattice 'R (IntMap.IntMap a) where lattice = latticeR


instance (Total a, U.Finite a) => Heyting 'L (Set.Set a) where
  heyting = heytingL (Set.\\)

instance (Total a, U.Finite a) => Heyting 'R (Set.Set a) where
  heyting = heytingR $ \x y -> non x \/ y

instance Heyting 'L IntSet.IntSet where
  heyting = heytingL (IntSet.\\)

instance Heyting 'R IntSet.IntSet where
  heyting = heytingR $ \x y -> non x \/ y

instance (Total a, U.Finite a) => Boolean (Set.Set a)
instance Boolean IntSet.IntSet

{- TODO pick an instance either key-aware or no
instance (Total a, U.Finite a, Lattice b) => Heyting 'L (Map.Map a b) where
  heyting = heytingL (Map.\\)

instance (Total a, U.Finite a, Heyting 'R b) => Heyting 'R (Map.Map a b) where

  heyting = heytingR $ \a b ->
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
-}

