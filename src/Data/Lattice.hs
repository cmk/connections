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
    Semilattice
  , Lattice
  , (\/)
  , (/\)
  , glb
  , lub
  -- * Bounded lattices
  , Bounded 
  , bottom
  , join
  , joins
  , top
  , meet
  , meets
  -- * Heyting algebras
  , Biheyting
  , Heyting(..)
  , (//)
  , neg
  , middle
  , equivL
  , heytingL
  , (\\)
  , non
  , boundary
  , equivR
  , heytingR
) where

import safe Control.Category ((>>>))
import safe Control.Applicative
import safe Data.Bool hiding (not)
import safe Data.Connection.Conn
import safe Data.Connection.Class
import safe Data.Either
import safe Data.Foldable
import safe Data.Order
--import safe Data.Order.Extended
import safe Data.Order.Syntax
import safe Data.Int
import safe Data.Maybe
import safe Data.Word
import safe GHC.TypeNats
--import safe Numeric.Natural
import safe Prelude hiding (Ord(..),Bounded)
--import safe qualified Data.IntMap as IntMap
--import safe qualified Data.IntSet as IntSet
--import safe qualified Data.Map as Map
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
type Lattice a = (Semilattice 'L a, Semilattice 'R a)

{-
class Order a => Semilattice k a where

    forked :: Conn k (a, a) a

instance (Eq a, Connection k (a,a) a) => Semilattice k a where

    forked = conn
-}

-- | Greatest lower bound operator.
--
-- > glb x x y = x
-- > glb x y z = glb z x y
-- > glb x x y = x
-- > glb x y z = glb x z y
-- > glb (glb x w y) w z = glb x w (glb y w z)
--
-- >>> glb 1.0 9.0 7.0
-- 7.0
-- >>> glb 1.0 9.0 (0.0 / 0.0)
-- 9.0
-- >>> glb (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: Set Int
-- fromList [3,5]
--
glb :: Lattice a => a -> a -> a -> a
glb x y z = (x \/ y) /\ (y \/ z) /\ (z \/ x)

-- | Least upper bound operator.
--
-- The order dual of 'glb'.
--
-- >>> lub 1.0 9.0 7.0
-- 7.0
-- >>> lub 1.0 9.0 (0.0 / 0.0)
-- 1.0
--
lub :: Lattice a => a -> a -> a -> a
lub x y z = (x /\ y) \/ (y /\ z) \/ (z /\ x)


    -- | Greatest lower bound operator.
    --
    -- > glb x x y = x
    -- > glb x y z = glb z x y
    -- > glb x x y = x
    -- > glb x y z = glb x z y
    -- > glb (glb x w y) w z = glb x w (glb y w z)
    --
    -- >>> glb 1.0 9.0 7.0
    -- 7.0
    -- >>> glb 1.0 9.0 (0.0 / 0.0)
    -- 9.0
    -- >>> glb (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: Set Int
    -- fromList [3,5]
    --
    glb :: a -> a -> a -> a
    glb x y z = (x \/ y) /\ (y \/ z) /\ (z \/ x)

    -- | Least upper bound operator.
    --
    -- The order dual of 'glb'.
    --
    -- >>> lub 1.0 9.0 7.0
    -- 7.0
    -- >>> lub 1.0 9.0 (0.0 / 0.0)
    -- 1.0
    --
    lub :: a -> a -> a -> a
    lub x y z = (x /\ y) \/ (y /\ z) \/ (z /\ x)


-------------------------------------------------------------------------------
-- Bounded lattices
-------------------------------------------------------------------------------


-- | Bounded lattices.
--
-- A bounded lattice is a lattice with two neutral elements wrt join and meet
-- operations:
--
-- @
-- x '\/' 'bottom' = x
-- x '/\' 'top' = x
-- 'glb' 'bottom' x 'top' = x
-- @
--
-- The least and greatest elements of a lattice /a/ are given by the unique
-- upper and lower adjoints to the function /a -> ()/.
--
-- See < https://en.wikipedia.org/wiki/Lattice_(order)#Bounded_lattice >.
--
type Bounded k a = (Semilattice k a, Extremal k a)


{-
class Semilattice k a => Bounded k a where

    bounded :: Conn k () a

instance (Semilattice k a, Extremal k a) => Bounded k a where

    bounded = conn
-}

-- | The lower bound of a lower-bounded lattice.
--
-- > bottom \/ x = x
-- > bottom /\ x = bottom
-- > bottom = lowerL bounded ()
--
bottom :: Bounded 'L a => a
bottom = minimal

-- | The upper bound of an upper-bounded lattice.
--
-- > top /\ x = x
-- > top \/ x = top
-- > top = upperR bounded ()
--
top :: Bounded 'R a => a
top = maximal

-- | Fold over a collection using the semigroup operation of a meet semilattice.
-- 
join :: (Bounded 'L a, Foldable f) => f a -> a
join = joins id

-- >>> joins Just [1..5 :: Int]
-- Just 5
joins :: (Bounded 'L a, Foldable f) => (b -> a) -> f b -> a
joins f = foldl' (\x y -> x \/ f y) bottom
{-# INLINE joins #-}

-- | Fold over a collection using the semigroup operation of a meet semilattice.
--
meet :: (Bounded 'R a, Foldable f) => f a -> a
meet = meets id

-- >>> meets Just [1..5 :: Int]
-- Just 1
meets :: (Bounded 'R a, Foldable f) => (b -> a) -> f b -> a
meets f = foldl' (\x y -> x /\ f y) top
{-# INLINE meets #-}

-------------------------------------------------------------------------------
-- Heyting algebras
-------------------------------------------------------------------------------

-- | A < https://ncatlab.org/nlab/show/co-Heyting+algebra bi-Heyting algebra >.
--
type Biheyting a = (Heyting 'L a, Heyting 'R a)

-- | A Heyting algebra is a bounded, distributive lattice equipped with an implication operation.
--
-- /Heyting Laws/:
--
-- > x <= (y // z) <=> x /\ y <= z
-- > (x // y) <= (x // y \/ z)
-- > (x \/ z // y) <= (x // y)
--
-- /Co-Heyting laws/:
--
-- > x >= (y \\ z) <=> x \/ y >= z
-- > (x \\ y) >= (x \\ y /\ z)
-- > (x /\ z \\ y) >= (x \\ y)
--
-- Note that Heyting algebras needn't obey the law of the excluded middle:
--
-- > EQ \/ neg EQ = EQ \/ (EQ // LT) = EQ \/ LT = EQ /= GT
--
-- See < https://ncatlab.org/nlab/show/Heyting+algebra >
--
class Bounded k a => Heyting k a where
    
    -- | The defining connection of a Heyting algebra.
    --
    -- Implication from /a/ is the upper adjoint of conjunction with /a/.
    -- Co-implication from /a/ is the lower adjoint of disjunction with /a/.
    --
    heyting :: a -> Conn k a a

infixr 8 // -- same as ^

-- | Logical implication.
--
-- /Laws/:
--
-- > x // x = top
-- > x /\ (x // y) = x /\ y
-- > x // (y /\ z) = (x // y) /\ (x // z)
-- > y <= (x // y)
-- > x <= y <=> x // y == top
-- > (x /\ y) <= z <=> x <= (y // z)
-- > (x /\ y) // z = x // (y // z)
-- > y /\ (x // y)  = y
-- > (x // x \/ y) <= y
-- > y <= (x // x /\ y)
-- > x <= y => (z // x) <= (z // y)
-- > x <= y => (x // z) <= (y // z)
--
(//) :: Heyting 'L a => a -> a -> a
(//) = lowerL . heyting

-- | Logical negation.
--
-- @ 'neg' x = x '//' 'bottom' @
--
-- /Laws/:
--
-- > neg (x \/ y) <= neg x
-- > x /\ neg x = bottom
-- > x <= neg (neg x)
-- > neg (neg (neg x)) = neg x
-- > neg bottom = top
-- > neg top = bottom
-- > neg (x \/ y) = neg x /\ neg y
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
equivL :: Biheyting a => a -> a -> a
equivL x y = (x // y) /\ (y // x)

-- | Default constructor for a Heyting algebra.
--
heytingL :: (Eq a, Connection 'L (a, a) a) => (a -> a -> a) -> a -> ConnL a a
heytingL f a = ConnL (f a) (\/ a)

infixr 8 \\ -- same as ^

-- | Logical co-implication.
--
-- /Laws/:
--
-- > x \\ x = bottom
-- > x \/ (x // y) = x \/ y
-- > x \\ (y \/ z) = (x \\ y) \/ (x \\ z)
-- > y >= (x \\ y)
-- > x <= y <=> x \\ y == bottom
-- > (x \/ y) >= z <=> x >= (y \\ z)
-- > (x \/ y) \\ z = x \\ (y \\ z)
-- > y \/ (x \\ y) = y
-- > (x \\ x /\ y) >= y
-- > y >= (x \\ x \/ y)
-- > x >= y => (z \\ x) >= (z \\ y)
-- > x >= y => (x \\ z) >= (y \\ z)
--
(\\) :: Heyting 'R a => a -> a -> a
(\\) = upperR . heyting

-- | Logical < https://ncatlab.org/nlab/show/co-Heyting+negation co-negation >.
--
-- @ 'non' x = 'top' '\\' x @
--
-- /Laws/:
--
-- > non (x /\ y) <= non x
-- > x \/ non x = top
-- > x >= non (non x)
-- > non (non (non x)) = non x
-- > non top = bottom
-- > non bottom = top
-- > non (x /\ y) = non x \/ non y
-- > non (non (x /\ non x)) = bottom
--
non :: Heyting 'R a => a -> a
non x = top \\ x

-- | The co-Heyting < https://ncatlab.org/nlab/show/co-Heyting+boundary boundary > operator.    
--
-- > x = boundary x \/ (non . non) x
-- > boundary (a /\ b) = (boundary a /\ b) \/ (a /\ boundary b)  -- (Leibniz rule)
-- > boundary (a \/ b) \/ boundary (a /\ b) = boundary a \/ boundary b
--
boundary :: Heyting 'R a => a -> a
boundary x = x /\ non x

-- | Intuitionistic co-equivalence.
--
equivR :: Biheyting a => a -> a -> a
equivR x y = (x \\ y) \/ (y \\ x)

-- | Default constructor for a co-Heyting algebra.
--
heytingR :: (Eq a, Connection 'R (a, a) a) => (a -> a -> a) -> a -> ConnR a a
heytingR f a = ConnR (a /\) (f a)

-- 
-- x '//' x           = 'top'
-- x '/\' (x '//' y)  = x '/\' y
-- y '/\' (x '//' y)  = y
-- x '//' (y '//' z) = (x '/\' y) '//' z
-- x '//' (y '/\' z)  = (x '//' y) '/\' (x '//' z)
-- 'neg' (x '/\' y)    = 'neg' (x '\/' y)
-- 'neg' (x '\/' y)    = 'neg' x '/\' 'neg' y
-- (x '//' y) '\/' x '<=' y
-- y '<=' (x '//' x '/\' y)
-- x '<=' y => (z '//' x) '<=' (z '//' y)
-- x '<=' y => (x '//' z) '<=' (y '//' z)
-- x '<=' y <=> x '//' y '==' 'top'
-- x '/\' y '<=' z <=> x '<=' (y '//' z) <=> y '<=' (x '//' z)
-- 
--

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------


impliesL :: (Total a, P.Bounded a) => a -> a -> a
impliesL x y = if x > y then y else P.maxBound

impliesR :: (Total a, P.Bounded a) => a -> a -> a
impliesR x y = if x < y then y else P.minBound

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

instance (Triple (a, a) a, Triple () a, Heyting 'L a) => Heyting 'L (Maybe a) where
  heyting = heytingL f where
    f (Just a) (Just b) = Just (a // b)
    f Nothing  _        = Just top
    f _        Nothing  = Nothing

instance (U.Finite a, Triple (b, b) b, Triple () b, Heyting 'L b) => Heyting 'L (a -> b) where
  heyting = heytingL $ liftA2 (//)

instance (U.Finite a, Triple (b, b) b, Triple () b, Heyting 'R b) => Heyting 'R (a -> b) where
  heyting = heytingR $ liftA2 (\\)

instance (Total a, U.Finite a) => Heyting 'L (Set.Set a) where
  heyting = heytingL Set.difference
  --neg xs = Set.fromList [ x | x <- universeF, Set.negMember x xs]


{-

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------


instance Heyting a => Heyting (Extended a) where
  Extended a // Extended b | a <= b    = Top
                            | otherwise = Extended (a // b)
  Top        // a          = a
  _          // Top        = Top
  Bottom     // _          = Top
  _          // Bottom     = Bottom

deriving via (a -> a) instance (Finite a, Heyting a) => Heyting (Endo a)
deriving via (a -> b) instance (Finite a, Heyting b) => Heyting (Op b a)
deriving via (Op Bool a) instance (Finite a) => Heyting (Predicate a)


{-
  x <=> y = Set.fromList
      [ z
      | z <- universeF
      , Set.member z x <=> Set.member z y
      ]
instance (Total k, Finite k, Heyting a) => Heyting (Map.Map k a) where

impliesMap a b = Map.union x y where
        x = Map.merge
          Map.dropMissing                    -- drop if an element is missing in @b@
          (Map.mapMissing (\_ _ -> top))     -- put @top@ if an element is missing in @a@
          (Map.zipMatched (\_ -> (`implies`))) -- merge  matching elements with @`implies`@
          a b

        y = Map.fromList [(k, top) | k <- universeF, not (Map.member k a), not (Map.member k b) ]
          -- for elements which are not in a, nor in b add
          -- a @top@ key

-- TODO: compare performance
impliesMap a b =
  Map.intersection (`implies`) a b
    `Map.union` Map.map (const top) (Map.difference b a)
    `Map.union` Map.fromList [(k, top) | k <- universeF, not (Map.member k a), not (Map.member k b)]
-}
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
