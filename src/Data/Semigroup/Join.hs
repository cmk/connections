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

module Data.Semigroup.Join (
  -- * Constraint kinds
    type (-)
  , type Semilattice
  , type LatticeLaw
  , type BoundedLaw
  -- * Join semilattices
  , bottom
  , (\/)
  , join
  , joinWith
  , join1
  , joinWith1
  , joinLe
  , joinGe
  , pcompareJoin
  , Join(..)
  -- * Meet semilattices
  , top
  , (/\)
  , meet
  , meetWith
  , meet1
  , meetWith1
  , meetLe
  , meetGe
  , pcompareMeet
  , Meet(..)
  -- * DerivingVia
  , F1(..)
  , F2(..)
  , N5Min(..)
  , N5Max(..)
) where

import safe Control.Applicative
import safe Data.Bool hiding (not)
import safe Data.Either
import safe Data.Foldable
import safe Data.Functor.Apply
import safe Data.Functor.Compose
import safe Data.Functor.Identity
import safe Data.Functor.Contravariant
import safe Data.Int
import safe Data.Kind
import safe Data.Maybe
import safe Data.Order
import safe Data.Semigroup
import safe Data.Semigroup.Foldable
import safe Data.Universe.Class (Finite(..))
import safe Data.Word
import safe GHC.Generics (Generic)
import safe GHC.Real (Ratio(..))
import safe Numeric.Natural
import safe Prelude hiding (Ord(..), Eq(..), Bounded, not)
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set

-- | Hyphenation operator.
type ((g :: Type -> Type) - (f :: Type -> Constraint)) a = f (g a)

type Semilattice = Semigroup

type LatticeLaw a = ((Join-Semilattice) a, (Meet-Semilattice) a)

type BoundedLaw a = ((Join-Monoid) a, (Meet-Monoid) a)

-------------------------------------------------------------------------------
-- Join semilattices
-------------------------------------------------------------------------------

-- | A commutative 'Semilattice' under '\/'.
newtype Join a = Join { getJoin :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Join where
  pure = Join
  Join f <*> Join a = Join (f a)

instance (Eq a, Semigroup (Join a)) => Preorder (Join a) where
  x <~ y = x <> y == y
  x >~ y = x <> y == x

bottom :: (Join-Monoid) a => a
bottom = getJoin mempty
{-# INLINE bottom #-}

infixr 5 \/

-- | Join operation on a semilattice.
--
-- >>> (> (0::Int)) ∧ ((< 10) \/ (== 15)) $ 10
-- False
--
-- >>> IntSet.fromList [1..5] ∧ IntSet.fromList [2..5]
-- fromList [2,3,4,5]
(\/) :: (Join-Semilattice) a => a -> a -> a
a \/ b = getJoin (Join a <> Join b)
{-# INLINE (\/) #-}

-- @ 'join' :: 'Lattice' a => 'Minimal' a => 'Set' a -> a @
--
join :: Foldable f => (Join-Monoid) a => f a -> a
join = joinWith id

-- | The join of a list of join-semilattice elements (of length at least top)
join1 :: Foldable1 f => (Join-Semilattice) a => f a -> a
join1 = joinWith1 id

-- >>> joinWith Just [1..5 :: Int]
-- Just 5
-- >>> joinWith N5 [1,5,0/0]
-- N5 {fromN5 = Infinity}
-- >>> joinWith MaxMin $ [IntSet.fromList [1..5], IntSet.fromList [2..4]]
-- MaxMin {unMaxMin = fromList [2,3,4]}
joinWith :: Foldable t => (Join-Monoid) a => (b -> a) -> t b -> a
joinWith f = foldl' (\x y -> x \/ f y) bottom
{-# INLINE joinWith #-}

-- | Fold over a non-empty collection using the join operation of an arbitrary join semilattice.
--
joinWith1 :: Foldable1 t => (Join-Semilattice) a => (b -> a) -> t b -> a
joinWith1 f = getJoin . foldMap1 (Join . f)
{-# INLINE joinWith1 #-}

infix 4 `joinLe`
-- | The partial ordering induced by the join-semilattice structure.
--
--
-- Normally when /a/ implements 'Ord' we should have:
-- @ 'joinLe' x y = x '<=' y @
--
joinLe :: Eq a => (Join-Semilattice) a => a -> a -> Bool
joinLe x y = y == x \/ y

infix 4 `joinGe`
-- | The partial ordering induced by the join-semilattice structure.
--
-- Normally when /a/ implements 'Ord' we should have:
-- @ 'joinGe' x y = x '>=' y @
--
joinGe :: Eq a => (Join-Semilattice) a => a -> a -> Bool
joinGe x y = x == x \/ y

-- | Partial version of 'Data.Ord.compare'.
--
-- Normally when /a/ implements 'Preorder' we should have:
-- @ 'pcompareJoin' x y = 'pcompare' x y @
--
pcompareJoin :: Eq a => (Join-Semilattice) a => a -> a -> Maybe Ordering
pcompareJoin x y
  | x == y = Just EQ
  | joinLe x y && x /= y = Just LT
  | joinGe x y && x /= y = Just GT
  | otherwise = Nothing

-------------------------------------------------------------------------------
-- Meet semilattices
-------------------------------------------------------------------------------

newtype Meet a = Meet { getMeet :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Meet where
    pure = Meet
    Meet f <*> Meet a = Meet (f a)

instance (Eq a, Semigroup (Meet a)) => Preorder (Meet a) where
  x <~ y = x <> y == x
  x >~ y = x <> y == y

top :: (Meet-Monoid) a => a
top = getMeet mempty
{-# INLINE top #-}

infixr 6 /\ -- comment for the parser

-- | Meet operation on a semilattice.
--
-- >>> (> (0::Int)) /\ ((< 10) ∨ (== 15)) $ 15
-- True
--
(/\) :: (Meet-Semilattice) a => a -> a -> a
a /\ b = getMeet (Meet a <> Meet b)
{-# INLINE (/\) #-}

meet :: Foldable f => (Meet-Monoid) a => f a -> a
meet = meetWith id

-- | The meet of a non-empty collection of meet-semilattice elements.
meet1 :: Foldable1 f => (Meet-Semilattice) a => f a -> a
meet1 = meetWith1 id

-- | Fold over a collection using the multiplicative operation of an arbitrary semiring.
-- 
-- @
-- 'meet' f = 'Data.foldr'' ((*) . f) 'top'
-- @
--
--
-- >>> meetWith Just [1..5 :: Int]
-- Just 1
-- >>> meetWith N5 [1,5,0/0]
-- N5 {fromN5 = -Infinity}
meetWith :: Foldable f => (Meet-Monoid) a => (b -> a) -> f b -> a
meetWith f = foldl' (\x y -> x /\ f y) top
{-# INLINE meetWith #-}

-- | Fold over a non-empty collection using the multiplicative operation of a semiring.
--
-- As the collection is non-empty this does not require a distinct multiplicative unit:
--
-- >>> meetWith1 Just $ 1 :| [2..5 :: Int]
-- Just 120
-- >>> meetWith1 First $ 1 :| [2..(5 :: Int)]
-- First {getFirst = 15}
-- >>> meetWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Just 11}
--
meetWith1 :: Foldable1 f => (Meet-Semilattice) a => (b -> a) -> f b -> a
meetWith1 f = getMeet . foldMap1 (Meet . f)
{-# INLINE meetWith1 #-}

infix 4 `meetLe`
-- | The partial ordering induced by the meet-semilattice structure.
--
-- Normally when /a/ implements 'Preorder' we should have:
-- @ 'meetLe' x y = x '<~' y @
--
meetLe :: Eq a => (Meet-Semilattice) a => a -> a -> Bool
meetLe x y = x == x /\ y

infix 4 `meetGe`
-- | The partial ordering induced by the meet-semilattice structure.
--
-- Normally when /a/ implements 'Preorder' we should have:
-- @ 'meetGe' x y = x '>~' y @
--
meetGe :: Eq a => (Meet-Semilattice) a => a -> a -> Bool
meetGe x y = y == x /\ y

-- | Partial version of 'Data.Ord.compare'.
--
-- Normally when /a/ implements 'Preorder' we should have:
-- @ 'pcompareJoin' x y = 'pcompare' x y @
--
pcompareMeet :: Eq a => (Meet-Semilattice) a => a -> a -> Maybe Ordering
pcompareMeet x y
  | x == y = Just EQ
  | meetLe x y && x /= y = Just LT
  | meetGe x y && x /= y = Just GT
  | otherwise = Nothing

---------------------------------------------------------------------
-- DerivingVia
---------------------------------------------------------------------

newtype F1 (f :: Type -> Type) a = F1 (f a) deriving stock (Eq, Ord, Show, Functor)

instance (Applicative f, Semigroup a) => Semigroup (F1 f a) where
  F1 x <> F1 y = F1 $ (<>) <$> x <*> y 

instance (Applicative f, Monoid a) => Monoid (F1 f a) where
  mempty = F1 $ pure mempty


newtype F2 (f :: Type -> Type) (g :: Type -> Type) a = F2 (f (g a)) deriving stock (Eq, Ord, Show, Functor)
deriving via (Compose (f :: Type -> Type) (g :: Type -> Type)) instance (Applicative f, Applicative g) => Applicative (F2 f g) 

instance (Applicative f, Applicative g, Semigroup a) => Semigroup (F2 f g a) where
  (<>) = liftA2 (<>)

instance (Applicative f, Applicative g, Monoid a) => Monoid (F2 f g a) where
  mempty = pure mempty


newtype N5Min a = N5Min a deriving stock (Eq, Ord, Show, Functor)
  deriving Applicative via Identity

instance (Preorder a, Fractional a) => Semigroup (N5Min a) where
  (<>) = liftA2 $ \x y -> maybe (-1 / 0) (bool y x . (<= EQ)) (pcompare x y)

instance (Preorder a, Fractional a) => Monoid (N5Min a) where
  mempty = N5Min $ 1/0


newtype N5Max a = N5Max a deriving stock (Eq, Ord, Show, Functor)
  deriving Applicative via Identity

instance (Preorder a, Fractional a) => Semigroup (N5Max a) where
  (<>) = liftA2 $ \x y -> maybe (1 / 0) (bool y x . (>= EQ)) (pcompare x y)

instance (Preorder a, Fractional a) => Monoid (N5Max a) where
  mempty = N5Max $ -1/0

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------


-- compare with Sign dioid
joinOrdering :: Ordering -> Ordering -> Ordering
joinOrdering LT x = x
joinOrdering x LT = x
joinOrdering EQ GT = GT
joinOrdering EQ _  = EQ
joinOrdering GT _  = GT

meetOrdering :: Ordering -> Ordering -> Ordering
meetOrdering LT _ = LT
meetOrdering _ LT = LT
meetOrdering EQ _  = EQ
meetOrdering _ EQ  = EQ
meetOrdering GT GT = GT

instance Semigroup (Join Ordering) where
  (<>) = liftA2 joinOrdering
  {-# INLINE (<>) #-}

instance Monoid (Join Ordering) where
  mempty = pure LT
  {-# INLINE mempty #-}

instance Semigroup (Meet Ordering) where
  (<>) = liftA2 meetOrdering
  {-# INLINE (<>) #-}

instance Monoid (Meet Ordering) where
  mempty = pure GT
  {-# INLINE mempty #-}

deriving via (F1 Join (Max ())) instance Semigroup (Join ())
deriving via (F1 Join (Max ())) instance Monoid (Join ())
deriving via (F1 Meet (Min ())) instance Semigroup (Meet ())
deriving via (F1 Meet (Min ())) instance Monoid (Meet ())

deriving via (F1 Join Any) instance Semigroup (Join Bool)
deriving via (F1 Join Any) instance Monoid (Join Bool)
deriving via (F1 Meet All) instance Semigroup (Meet Bool)
deriving via (F1 Meet All) instance Monoid (Meet Bool)

deriving via (F1 Join (Max Word8)) instance Semigroup (Join Word8)
deriving via (F1 Join (Max Word8)) instance Monoid (Join Word8)
deriving via (F1 Meet (Min Word8)) instance Semigroup (Meet Word8)
deriving via (F1 Meet (Min Word8)) instance Monoid (Meet Word8)

deriving via (F1 Join (Max Word16)) instance Semigroup (Join Word16)
deriving via (F1 Join (Max Word16)) instance Monoid (Join Word16)
deriving via (F1 Meet (Min Word16)) instance Semigroup (Meet Word16)
deriving via (F1 Meet (Min Word16)) instance Monoid (Meet Word16)

deriving via (F1 Join (Max Word32)) instance Semigroup (Join Word32)
deriving via (F1 Join (Max Word32)) instance Monoid (Join Word32)
deriving via (F1 Meet (Min Word32)) instance Semigroup (Meet Word32)
deriving via (F1 Meet (Min Word32)) instance Monoid (Meet Word32)

deriving via (F1 Join (Max Word64)) instance Semigroup (Join Word64)
deriving via (F1 Join (Max Word64)) instance Monoid (Join Word64)
deriving via (F1 Meet (Min Word64)) instance Semigroup (Meet Word64)
deriving via (F1 Meet (Min Word64)) instance Monoid (Meet Word64)

deriving via (F1 Join (Max Word)) instance Semigroup (Join Word)
deriving via (F1 Join (Max Word)) instance Monoid (Join Word)
deriving via (F1 Meet (Min Word)) instance Semigroup (Meet Word)
deriving via (F1 Meet (Min Word)) instance Monoid (Meet Word)

deriving via (F1 Join (Max Natural)) instance Semigroup (Join Natural)
deriving via (F1 Meet (Min Natural)) instance Semigroup (Meet Natural)
instance Monoid (Join Natural) where mempty = Join 0

deriving via (F1 Join (Max Int8)) instance Semigroup (Join Int8)
deriving via (F1 Join (Max Int8)) instance Monoid (Join Int8)
deriving via (F1 Meet (Min Int8)) instance Semigroup (Meet Int8)
deriving via (F1 Meet (Min Int8)) instance Monoid (Meet Int8)

deriving via (F1 Join (Max Int16)) instance Semigroup (Join Int16)
deriving via (F1 Join (Max Int16)) instance Monoid (Join Int16)
deriving via (F1 Meet (Min Int16)) instance Semigroup (Meet Int16)
deriving via (F1 Meet (Min Int16)) instance Monoid (Meet Int16)

deriving via (F1 Join (Max Int32)) instance Semigroup (Join Int32)
deriving via (F1 Join (Max Int32)) instance Monoid (Join Int32)
deriving via (F1 Meet (Min Int32)) instance Semigroup (Meet Int32)
deriving via (F1 Meet (Min Int32)) instance Monoid (Meet Int32)

deriving via (F1 Join (Max Int64)) instance Semigroup (Join Int64)
deriving via (F1 Join (Max Int64)) instance Monoid (Join Int64)
deriving via (F1 Meet (Min Int64)) instance Semigroup (Meet Int64)
deriving via (F1 Meet (Min Int64)) instance Monoid (Meet Int64)

deriving via (F1 Join (Max Int)) instance Semigroup (Join Int)
deriving via (F1 Join (Max Int)) instance Monoid (Join Int)
deriving via (F1 Meet (Min Int)) instance Semigroup (Meet Int)
deriving via (F1 Meet (Min Int)) instance Monoid (Meet Int)

deriving via (F1 Join (Max Integer)) instance Semigroup (Join Integer)
deriving via (F1 Meet (Min Integer)) instance Semigroup (Meet Integer)

deriving via (F1 Join (N5Max Float)) instance Semigroup (Join Float)
deriving via (F1 Join (N5Max Float)) instance Monoid (Join Float)
deriving via (F1 Meet (N5Min Float)) instance Semigroup (Meet Float)
deriving via (F1 Meet (N5Min Float)) instance Monoid (Meet Float)

deriving via (F1 Join (N5Max Double)) instance Semigroup (Join Double)
deriving via (F1 Join (N5Max Double)) instance Monoid (Join Double)
deriving via (F1 Meet (N5Min Double)) instance Semigroup (Meet Double)
deriving via (F1 Meet (N5Min Double)) instance Monoid (Meet Double)

deriving via (F1 Join (N5Max (Ratio Integer))) instance Semigroup (Join (Ratio Integer))
-- write by hand to guard against div-by-zero exceptions
instance Monoid (Join (Ratio Integer)) where mempty = Join $ -1 :% 0
deriving via (F1 Meet (N5Min (Ratio Integer))) instance Semigroup (Meet (Ratio Integer))
instance Monoid (Meet (Ratio Integer)) where mempty = Meet $ 1 :% 0

deriving via (F1 Join (N5Max (Ratio Natural))) instance Semigroup (Join (Ratio Natural))
instance Monoid (Join (Ratio Natural)) where mempty = Join $ 0 :% 1
deriving via (F1 Meet (N5Min (Ratio Natural))) instance Semigroup (Meet (Ratio Natural))
instance Monoid (Meet (Ratio Natural)) where mempty = Meet $ 1 :% 0

deriving via (F2 Meet Down (Join a)) instance Semigroup (Join a) => Semigroup (Meet (Down a))
deriving via (F2 Meet Down (Join a)) instance Monoid (Join a) => Monoid (Meet (Down a))
deriving via (F2 Join Down (Meet a)) instance Semigroup (Meet a) => Semigroup (Join (Down a))
deriving via (F2 Join Down (Meet a)) instance Monoid (Meet a) => Monoid (Join (Down a))

deriving via (F1 Join (a -> a)) instance Semigroup a => Semigroup (Join (Endo a))
deriving via (F1 Join (a -> a)) instance Monoid a => Monoid (Join (Endo a))
deriving via (F1 Meet (Endo a)) instance Semigroup a => Semigroup (Meet (Endo a))
deriving via (F1 Meet (Endo a)) instance Monoid a => Monoid (Meet (Endo a))

deriving via (F1 Join (r -> Join a)) instance Semigroup (Join a) => Semigroup (Join (r -> a))
deriving via (F1 Join (r -> Join a)) instance Monoid (Join a) => Monoid (Join (r -> a))
deriving via (F1 Meet (r -> Meet a)) instance Semigroup (Meet a) => Semigroup (Meet (r -> a))
deriving via (F1 Meet (r -> Meet a)) instance Monoid (Meet a) => Monoid (Meet (r -> a))

-- TODO: check semimodules paper this may not be the instance you want
deriving via (b -> Join a) instance Semigroup (Join a) => Semigroup (Join (Op a b))
deriving via (b -> Join a) instance Monoid (Join a) => Monoid (Join (Op a b))
deriving via (b -> Meet a) instance Semigroup (Meet a) => Semigroup (Meet (Op a b))
deriving via (b -> Meet a) instance Monoid (Meet a) => Monoid (Meet (Op a b))

deriving via (Op (Join Bool) a) instance Semigroup (Join (Predicate a))
deriving via (Op (Join Bool) a) instance Monoid (Join (Predicate a))
deriving via (Op (Meet Bool) a) instance Semigroup (Meet (Predicate a))
deriving via (Op (Meet Bool) a) instance Monoid (Meet (Predicate a))

deriving via (F1 Join (Maybe (Join a))) instance Semigroup (Join a) => Semigroup (Join (Maybe a))
deriving via (F1 Join (Maybe (Join a))) instance Semigroup (Join a) => Monoid (Join (Maybe a))
deriving via (F2 Meet Maybe (Meet a)) instance Semigroup (Meet a) => Semigroup (Meet (Maybe a))
deriving via (F2 Meet Maybe (Meet a)) instance Monoid (Meet a) => Monoid (Meet (Maybe a))

instance (Semigroup (Join a), Semigroup (Join b)) => Semigroup (Join (Either a b)) where
  (<>) = liftA2 joinEither

joinEither (Right x) (Right y) = Right (x \/ y)
joinEither u@(Right _) _ = u
joinEither _ u@(Right _) = u
joinEither (Left x) (Left y) = Left (x \/ y)

instance (Monoid (Join a), Semigroup (Join b)) => Monoid (Join (Either a b)) where
  mempty = pure $ Left bottom

instance (Semigroup (Meet a), Semigroup (Meet b)) => Semigroup (Meet (Either a b)) where
  (<>) = liftA2 meetEither

meetEither (Left x) (Left y) = Left (x /\ y)
meetEither l@(Left _) _ = l
meetEither _ l@(Left _) = l
meetEither (Right x) (Right y) = Right (x /\ y)

instance (Semigroup (Meet a), Monoid (Meet b)) => Monoid (Meet (Either a b)) where
  mempty = pure $ Right top

instance (Semigroup (Join a), Semigroup (Join b)) => Semigroup (Join (a, b)) where
  Join (x1, y1) <> Join (x2, y2) = Join (x1 \/ x2, y1 \/ y2)

instance (Semigroup (Meet a), Semigroup (Meet b)) => Semigroup (Meet (a, b)) where
  Meet (x1, y1) <> Meet (x2, y2) = Meet (x1 /\ x2, y1 /\ y2)

instance (Monoid (Join a), Monoid (Join b)) => Monoid (Join (a, b)) where
  mempty = Join (bottom, bottom)

instance (Monoid (Meet a), Monoid (Meet b)) => Monoid (Meet (a, b)) where
  mempty = Meet (top, top)

instance TotalOrder a => Semigroup (Join (Set.Set a)) where
  (<>) = liftA2 Set.union 

instance TotalOrder a => Monoid (Join (Set.Set a)) where
  mempty = Join Set.empty

instance TotalOrder a => Semigroup (Meet (Set.Set a)) where
  (<>) = liftA2 Set.intersection 

instance (TotalOrder a, Finite a) => Monoid (Meet (Set.Set a)) where
  mempty = Meet $ Set.fromList universeF

instance (TotalOrder k, Semigroup (Join a)) => Semigroup (Join (Map.Map k a)) where
  (<>) = liftA2 (Map.unionWith (\/))

instance Semigroup (Join a) => Semigroup (Join (IntMap.IntMap a)) where
  (<>) = liftA2 (IntMap.unionWith (\/))

instance Semigroup (Join IntSet.IntSet) where
  (<>) = liftA2 IntSet.union 

instance Monoid (Join IntSet.IntSet) where
  mempty = Join IntSet.empty

instance Semigroup (Join a) => Monoid (Join (IntMap.IntMap a)) where
  mempty = Join IntMap.empty

instance (TotalOrder k, Semigroup (Join a)) => Monoid (Join (Map.Map k a)) where
  mempty = Join Map.empty

instance (TotalOrder k, Semigroup (Meet a)) => Semigroup (Meet (Map.Map k a)) where
  (<>) = liftA2 (Map.intersectionWith (/\))

instance (TotalOrder k, Finite k, Monoid (Meet a)) => Monoid (Meet (Map.Map k a)) where
  mempty = pure $ Map.fromList (universeF `zip` repeat top)

instance Semigroup (Meet a) => Semigroup (Meet (IntMap.IntMap a)) where
  (<>) = liftA2 (IntMap.intersectionWith (/\))

instance Monoid (Meet a) => Monoid (Meet (IntMap.IntMap a)) where
  mempty = pure $ IntMap.fromList (universeF `zip` repeat top)

instance Semigroup (Meet IntSet.IntSet) where
  (<>) = liftA2 IntSet.intersection 

instance Monoid (Meet IntSet.IntSet) where
  mempty = Meet $ IntSet.fromList universeF

{-
instance (TotalOrder k, (Meet-Monoid) k, (Meet-Monoid) a) => Monoid (Meet (Map.Map k a)) where
  mempty = Meet $ Map.singleton top top

instance (Meet-Monoid) a => Monoid (Meet (IntMap.IntMap a)) where
  mempty = Meet $ IntMap.singleton 0 top --TODO check

instance Monoid a => Semiring (Seq.Seq a) where
  (*) = liftA2 (<>)
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ Seq.singleton mempty

instance (TotalOrder k, Monoid k, Monoid a) => Semiring (Map.Map k a) where
  xs * ys = foldMap (flip Map.map xs . (<>)) ys
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ Map.singleton mempty mempty

instance Monoid a => Semiring (IntMap.IntMap a) where
  xs * ys = foldMap (flip IntMap.map xs . (<>)) ys
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ IntMap.singleton 0 mempty
-}


{-

instance (Join-Semigroup) (Max a) => Semigroup (Additive (Max a)) where
  (<>) = liftA2 (\/)

instance (Join-Monoid) (Max a) => Monoid (Additive (Max a)) where
  mempty = pure bottom

-- workaround for poorly specified entailment: instance (TotalOrder a, Bounded a) => Monoid (Max a)
instance (Minimal a, Semigroup (Max a)) => Monoid (Join (Max a)) where
  mempty = pure $ Max minimal

instance (Join-Semigroup) a => Semigroup (Join (Dual a)) where
  (<>) = liftA2 . liftA2 $ flip (\/)

instance (Join-Monoid) a => Monoid (Join (Dual a)) where
  mempty = pure . pure $ bottom


instance (Join-Semigroup) a => Semigroup (Join (Down a)) where
  (<>) = liftA2 . liftA2 $ (\/) 

instance (Join-Monoid) a => Monoid (Join (Down a)) where
  --Join (Down a) <> Join (Down b)
  mempty = pure . pure $ bottom

instance Semigroup (Max a) => Semigroup (Join (Max a)) where
  (<>) = liftA2 (<>)

-- MinPlus Predioid
-- >>> Min 1  `mul`  Min 2 :: Min Int
-- Min {getMin = 3}
instance (Join-Semigroup) a => Semigroup (Multiplicative (Min a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 (\/) a b

-- MinPlus Dioid
instance (Join-Monoid) a => Monoid (Multiplicative (Min a)) where
  mempty = Multiplicative $ pure bottom

--instance ((Meet-Semigroup) a, Maximal a) => Monoid (Meet a) where
--  mempty = Meet maximal

-- >>> Min 1 /\ Min 2 :: Min Int
-- Min {getMin = 1}
instance Semigroup (Min a) => Semigroup (Meet (Min a)) where
  (<>) = liftA2 (<>)

instance (Meet-Semigroup) (Min a) => Semigroup (Additive (Min a)) where
  (<>) = liftA2 (/\) 

instance (Meet-Monoid) (Min a) => Monoid (Additive (Min a)) where
  mempty = pure top

-- workaround for poorly specified entailment: instance (TotalOrder a, Bounded a) => Monoid (Min a)
-- >>> bottom :: Min Natural
-- Min {getMin = 0}
instance (Maximal a, Semigroup (Min a)) => Monoid (Meet (Min a)) where
  mempty = pure $ Min maximal

-- MaxTimes Predioid

instance (Meet-Semigroup) a => Semigroup (Meet (Max a)) where
  Meet a <> Meet b = Meet $ liftA2 (/\) a b

-- MaxTimes Dioid
instance (Meet-Monoid) a => Monoid (Meet (Max a)) where
  mempty = Meet $ pure top




-}

