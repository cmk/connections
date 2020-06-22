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

module Data.Order (
  -- * Preorders
    Preorder(..)
  , pcomparing
  -- * Iterators
  , until
  , while
  , fixed
  -- * DerivingVia
  , Total(..) 
  -- * Re-exports
  , Ordering(..)
  , Down(..)
  , Positive
) where

import safe Control.Applicative
import safe Control.Monad.Trans.Select
import safe Control.Monad.Trans.Cont
import safe Data.Bool
import safe Data.Complex
import safe Data.Either
import safe Data.Foldable (foldl')
import safe Data.Functor.Apply
import safe Data.Functor.Identity
import safe Data.Functor.Contravariant
import safe Data.Functor.Rep 
import safe Data.Int
import safe Data.List.NonEmpty
import safe Data.Maybe
import safe Data.Ord (Down(..))
import safe Data.Semigroup
import safe Data.Semigroup.Foldable
import safe Data.Universe.Class (Finite(..))
import safe Data.Word
import safe GHC.Real
import safe Numeric.Natural
import safe Prelude hiding (Ord(..), Bounded, until)
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set
import safe qualified Data.Ord as Ord
import safe qualified Data.Eq as Eq

-------------------------------------------------------------------------------
-- Preorders
-------------------------------------------------------------------------------

-- | A < https://en.wikipedia.org/wiki/Preorder preorder > on /a/.
--
-- A preorder relation '<~' must satisfy the following two axioms:
--
-- \( \forall x: x \leq x \) (reflexivity)
-- 
-- \( \forall a, b, c: ((a \leq b) \wedge (b \leq c)) \Rightarrow (a \leq c) \) (transitivity)
--
-- If additionally we have:
--
-- \( \forall a, b: (a \leq b) \Leftrightarrow \neg (b \leq a) \) (anti-symmetry)
--
-- then /a/ is a partial order and we may define an 'Eq' instance such that the
-- following holds:
--
-- @
-- x '~~' y = x '==' y
-- x '<~' y = x '<' y '||' x '==' y
-- @
--
-- Minimal complete definition: either 'pcompare' or '<~'. Using 'pcompare' can
-- be more efficient for complex types.
--
class Preorder a where
    {-# MINIMAL (<~) | pcompare #-} 

    infix 4 <~, >~, <, >, ?~, ~~, /~, `pcompare`, `pmax`, `pmin`

    -- | Non-strict partial order relation on /a/.
    --
    -- Is /x/ less than or equal to /y/?
    --
    -- '<~' is reflexive, anti-symmetric, and transitive.
    --
    -- > x <~ y = x < y || x ~~ y
    -- > x <~ y = maybe False (<~ EQ) (pcompare x y)
    --
    -- for all /x/, /y/ in /a/.
    --
    (<~) :: a -> a -> Bool
    x <~ y = maybe False (Ord.<= EQ) (pcompare x y)

    -- | Converse non-strict partial order relation on /a/.
    --
    -- Is /x/ greater than or equal to /y/?
    --
    -- '>~' is reflexive, anti-symmetric, and transitive.
    --
    -- > x >~ y = x > y || x ~~ y
    -- > x >~ y = maybe False (>~ EQ) (pcompare x y)
    --
    -- for all /x/, /y/ in /a/.
    --
    (>~) :: a -> a -> Bool
    (>~) = flip (<~)

    -- | Strict partial order relation on /a/.
    --
    -- Is /x/ less than /y/?
    --
    -- '<' is irreflexive, asymmetric, and transitive.
    --
    -- > x < y = x <~ y && not (y <~ x)
    -- > x < y = maybe False (< EQ) (pcompare x y)
    --
    -- When '<~' is antisymmetric then /a/ is a partial 
    -- order and we have:
    -- 
    -- > x < y = x <~ y && x /~ y
    --
    -- for all /x/, /y/ in /a/.
    --
    (<) :: a -> a -> Bool
    x < y = maybe False (Ord.< EQ) (pcompare x y)

    -- | Converse strict partial order relation on /a/.
    --
    -- Is /x/ greater than /y/?
    --
    -- '>' is irreflexive, asymmetric, and transitive.
    --
    -- > x > y = x >~ y && not (y >~ x)
    -- > x > y = maybe False (> EQ) (pcompare x y)
    -- 
    -- When '<~' is antisymmetric then /a/ is a partial 
    -- order and we have:
    -- 
    -- > x > y = x >~ y && x /~ y
    --
    -- for all /x/, /y/ in /a/.
    --
    (>) :: a -> a -> Bool
    (>) = flip (<)

    -- | Comparability relation on /a/. 
    --
    -- Are /x/ and /y/ comparable?
    --
    -- '?~' is reflexive, symmetric, and transitive.
    --
    -- If /a/ implements 'Ord' then we should have @x ?~ y = True@.
    --
    (?~) :: a -> a -> Bool
    x ?~ y = maybe False (const True) (pcompare x y)
    
    -- | Equivalence relation on /a/.
    --
    -- Are /x/ and /y/ equivalent?
    --
    -- '~~' is reflexive, symmetric, and transitive.
    --
    -- > x ~~ y = x <~ y && y <~ x
    -- > x ~~ y = maybe False (~~ EQ) (pcompare x y)
    --
    -- Use this as a lawful substitute for '==' when comparing
    -- floats, doubles, or rationals.
    --
    (~~) :: a -> a -> Bool
    x ~~ y = maybe False (Eq.== EQ) (pcompare x y)

    -- | Negation of '~~'.
    --
    -- Are /x/ and /y/ not equivalent?
    --
    (/~) :: a -> a -> Bool
    x /~ y = not $ x ~~ y
    
    -- | Similarity relation on /a/. 
    --
    -- Are /x/ and /y/ either equivalent or incomparable?
    --
    -- 'similar' is reflexive and symmetric, but not necessarily transitive.
    --
    -- Note this is only equivalent to '==' in a total order:
    --
    -- > similar (0/0 :: Float) 5 = True
    --
    -- If /a/ implements 'Ord' then we should have @('~~') = 'similar' = ('==')@.
    --
    similar :: a -> a -> Bool
    similar x y = maybe True (Eq.== EQ) (pcompare x y)

    -- | A partial version of 'Data.Ord.compare'.
    --
    -- > x <  y = maybe False (<  EQ) $ pcompare x y
    -- > x >  y = maybe False (>  EQ) $ pcompare x y
    -- > x <~ y = maybe False (<~ EQ) $ pcompare x y
    -- > x >~ y = maybe False (>~ EQ) $ pcompare x y
    -- > x ~~ y = maybe False (~~ EQ) $ pcompare x y
    -- > x ?~ y = maybe False (const True) $ pcompare x y
    -- > similar x y = maybe True (~~ EQ) $ pcompare x y
    -- 
    -- If /a/ implements 'Ord' then we should have @'pcompare' x y = 'Just' '$' 'compare' x y@.
    --
    pcompare :: a -> a -> Maybe Ordering
    pcompare x y 
      | x <~ y    = Just $ if y <~ x then EQ else LT
      | y <~ x    = Just GT
      | otherwise = Nothing

    -- | A partial version of 'Data.Ord.max'. 
    --
    -- Returns the left-hand argument in the case of equality.
    --
    pmax :: a -> a -> Maybe a
    pmax x y = do
      o <- pcompare x y
      case o of
        GT -> Just x
        EQ -> Just x
        LT -> Just y

    -- | A partial version of 'Data.Ord.min'. 
    --
    -- Returns the left-hand argument in the case of equality.
    --
    pmin :: a -> a -> Maybe a
    pmin x y = do
      o <- pcompare x y
      case o of
        GT -> Just y
        EQ -> Just x
        LT -> Just x

-- | A partial version of 'Data.Order.Total.comparing'.
--
-- > pcomparing p x y = pcompare (p x) (p y)
--
-- The partial application /pcomparing f/ induces a lawful preorder for 
-- any total function /f/.
--
pcomparing :: Preorder a => (b -> a) -> b -> b -> Maybe Ordering
pcomparing p x y = pcompare (p x) (p y)

-------------------------------------------------------------------------------
-- Iterators
-------------------------------------------------------------------------------

{-# INLINE until #-}
until :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
until pre rel f seed = go seed
  where go x | x' `rel` x = x
             | pre x = x
             | otherwise = go x'
          where x' = f x

{-# INLINE while #-}
while :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
while pre rel f seed = go seed
  where go x | x' `rel` x = x
             | not (pre x') = x
             | otherwise = go x'
          where x' = f x

-- | Greatest (resp. least) fixed point of a monitone (resp. antitone) function. 
--
-- Does not check that the function is monitone (resp. antitone).
--
-- See also < http://en.wikipedia.org/wiki/Kleene_fixed-point_theorem >.
--
{-# INLINE fixed #-}
fixed :: (a -> a -> Bool) -> (a -> a) -> a -> a
fixed = while (\_ -> True)

---------------------------------------------------------------------
-- DerivingVia
---------------------------------------------------------------------

newtype Total a = Total { getTotal :: a } deriving stock (Eq.Eq, Ord.Ord, Show, Functor)
  deriving Applicative via Identity

instance Ord.Ord a => Preorder (Total a) where
  x <~ y = getTotal $ liftA2 (Ord.<=) x y
  x >~ y = getTotal $ liftA2 (Ord.>=) x y
  pcompare x y = Just . getTotal $ liftA2 Ord.compare x y

deriving via (Total ()) instance Preorder ()
deriving via (Total Bool) instance Preorder Bool
deriving via (Total Ordering) instance Preorder Ordering
deriving via (Total Char) instance Preorder Char
deriving via (Total Word) instance Preorder Word
deriving via (Total Word8) instance Preorder Word8
deriving via (Total Word16) instance Preorder Word16
deriving via (Total Word32) instance Preorder Word32
deriving via (Total Word64) instance Preorder Word64
deriving via (Total Natural) instance Preorder Natural
deriving via (Total Int) instance Preorder Int
deriving via (Total Int8) instance Preorder Int8
deriving via (Total Int16) instance Preorder Int16
deriving via (Total Int32) instance Preorder Int32
deriving via (Total Int64) instance Preorder Int64
deriving via (Total Integer) instance Preorder Integer

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

-- N5 lattice ordering: NInf <= NaN <= PInf
n5 :: (Ord.Ord a, Fractional a) => a -> a -> Bool
n5 x y | x Eq./= x && y Eq./= y = True
       | x Eq./= x = y == 1/0
       | y Eq./= y = x == -1/0
       | otherwise = x Ord.<= y

instance Preorder Float where
  (<~) = n5

instance Preorder Double where
  (<~) = n5

-- N5 lattice ordering: NInf <= NaN <= PInf
{-
pinf = 1 :% 0
ninf = (-1) :% 0
anan = 0 :% 0

λ> pcompareRat anan pinf
Just LT
λ> pcompareRat pinf anan
Just GT
λ> pcompareRat anan anan
Just EQ
λ> pcompareRat anan (3 :% 5)
Nothing
-}
pcompareRat :: Rational -> Rational -> Maybe Ordering
pcompareRat (0:%0) (x:%0) = Just $ Ord.compare 0 x
pcompareRat (x:%0) (0:%0) = Just $ Ord.compare x 0
pcompareRat (x:%0) (y:%0) = Just $ Ord.compare (signum x) (signum y)
pcompareRat (0:%0) _ = Nothing
pcompareRat _ (0:%0) = Nothing
pcompareRat _ (x:%0) = Just $ Ord.compare 0 x -- guard against div-by-zero exceptions
pcompareRat (x:%0) _ = Just $ Ord.compare x 0
pcompareRat x y = Just $ Ord.compare x y

-- | Positive rationals, extended with an absorbing zero.
--
-- 'Positive' is the canonical < https://en.wikipedia.org/wiki/Semifield#Examples semifield >.
--
type Positive = Ratio Natural

-- N5 lattice comparison
pcomparePos :: Positive -> Positive -> Maybe Ordering
pcomparePos (0:%0) (x:%0) = Just $ Ord.compare 0 x
pcomparePos (x:%0) (0:%0) = Just $ Ord.compare x 0
pcomparePos (_:%0) (_:%0) = Just EQ -- all non-nan infs are equal
pcomparePos (0:%0) (0:%_) = Just $ GT
pcomparePos (0:%_) (0:%0) = Just $ LT
pcomparePos (0:%0) _ = Nothing
pcomparePos _ (0:%0) = Nothing
pcomparePos (x:%y) (x':%y') = Just $ Ord.compare (x*y') (x'*y)

instance Preorder Rational where
  pcompare = pcompareRat

instance Preorder Positive where
  pcompare = pcomparePos

instance (Preorder a, Num a) => Preorder (Complex a) where
  pcompare = pcomparing $ \(x :+ y) -> x^2 + y^2

instance Preorder a => Preorder (Down a) where
  (Down x) <~ (Down y) = y <~ x
  pcompare (Down x) (Down y) = pcompare y x

instance Preorder a => Preorder (Dual a) where
  (Dual x) <~ (Dual y) = y <~ x
  pcompare (Dual x) (Dual y) = pcompare y x

instance Preorder a => Preorder (Max a) where
  Max a <~ Max b = a <~ b

instance Preorder a => Preorder (Min a) where
  Min a <~ Min b = a <~ b

instance Preorder Any where
  Any x <~ Any y = x <~ y

instance Preorder All where
  All x <~ All y = y <~ x

instance Preorder a => Preorder (Identity a) where
  pcompare (Identity x) (Identity y) = pcompare x y

instance Preorder a => Preorder (Maybe a) where
  Nothing <~ _ = True
  Just{} <~ Nothing = False
  Just a <~ Just b = a <~ b

instance Preorder a => Preorder [a] where
  {-# SPECIALISE instance Preorder [Char] #-}
  [] <~ _     = True
  (_:_) <~ [] = False
  (x:xs) <~ (y:ys) = x <~ y && xs <~ ys

{-
  pcompare []     []     = Just EQ
  pcompare []     (_:_)  = Just LT
  pcompare (_:_)  []     = Just GT
  pcompare (x:xs) (y:ys) = case pcompare x y of
                              Just EQ -> pcompare xs ys
                              other   -> other
-}

instance Preorder a => Preorder (NonEmpty a) where
  (x :| xs) <~ (y :| ys) = x <~ y && xs <~ ys

instance (Preorder a, Preorder b) => Preorder (Either a b) where
  Right a <~ Right b  = a <~ b
  Right _ <~ _        = False

  Left a <~ Left b   = a <~ b
  Left _ <~ _        = True
 
instance (Preorder a, Preorder b) => Preorder (a, b) where 
  (a,b) <~ (i,j) = a <~ i && b <~ j

instance (Preorder a, Preorder b, Preorder c) => Preorder (a, b, c) where 
  (a,b,c) <~ (i,j,k) = a <~ i && b <~ j && c <~ k

instance (Preorder a, Preorder b, Preorder c, Preorder d) => Preorder (a, b, c, d) where 
  (a,b,c,d) <~ (i,j,k,l) = a <~ i && b <~ j && c <~ k && d <~ l

instance (Preorder a, Preorder b, Preorder c, Preorder d, Preorder e) => Preorder (a, b, c, d, e) where 
  (a,b,c,d,e) <~ (i,j,k,l,m) = a <~ i && b <~ j && c <~ k && d <~ l && e <~ m

instance (Foldable1 f, Representable f, Preorder a) => Preorder (Co f a) where
  Co f <~ Co g = and $ liftR2 (<~) f g

instance (Ord.Ord k, Preorder a) => Preorder (Map.Map k a) where
  (<~) = Map.isSubmapOfBy (<~)

instance Ord.Ord a => Preorder (Set.Set a) where
  (<~) = Set.isSubsetOf

instance Preorder a => Preorder (IntMap.IntMap a) where
  (<~) = IntMap.isSubmapOfBy (<~)

instance Preorder IntSet.IntSet where
  (<~) = IntSet.isSubsetOf

-- | TODO: short-circuiting version.
--
-- >>> const 3 <~ (const 4 :: Int8 -> Int8)
-- True
-- >>> const 3 <~ (id :: Int8 -> Int8)
-- False
instance (Finite a, Preorder b) => Preorder (a -> b) where
  pcompare f g = foldl' acc (Just EQ) [f x `pcompare` g x | x <- universeF]
    where acc old new = do
            m' <- new
            n' <- old
            case (m', n') of
              (x , EQ) -> Just x
              (EQ, y ) -> Just y
              (x , y ) -> if x == y then Just x else Nothing

instance (Finite a, Preorder a) => Preorder (Endo a) where
  pcompare (Endo f) (Endo g) = pcompare f g

instance (Finite a, Preorder b) => Preorder (Op b a) where
  --universe = coerce (universe :: [b -> a])
  --universe = map Op universe
  pcompare (Op f) (Op g) = pcompare f g

instance (Finite a) => Preorder (Predicate a) where
  --universe = map (Predicate . flip S.member) universe
  --universe = map Op universe
  pcompare (Predicate f) (Predicate g) = pcompare f g

-- |
-- >>> cont ($ 1) == (cont ($ 2) :: Cont Bool Int8)
-- False
-- >>> cont ($ 1) == (cont ($ 2) :: Cont () Int8)
-- True
instance (Ord.Ord a, Preorder a, Preorder r, Finite r) => Preorder (Cont r a) where
  (ContT x) <~ (ContT y) = x `contLe` y

instance (Ord.Ord a, Preorder a, Preorder r, Finite r) => Preorder (Select r a) where
  (SelectT x) <~ (SelectT y) = x `contLe` y

contLe :: forall a b c. (Finite b, Ord.Ord a, Preorder a, Preorder b, Preorder c) => ((a -> b) -> c) -> ((a -> b) -> c) -> Bool
contLe x y = if (universeF :: [b]) ~~ [] then True else point $ counter Map.empty
  where
    --point :: Preorder b => a -> Bool
    point ar = x ar <~ y ar

    --counter :: (Finite b, Ord.Ord a, Preorder c) => Map.Map a b -> a -> b
    counter acc a = case Map.lookup a acc of
      Just b -> b

      Nothing -> case [b | b <- universeF 
                         , let acc' = Map.insert a b acc
                               func a' | a' < a = counter acc a'
                                 | otherwise = counter acc' a'
                         , not . point $ func
                      ] of
                   (b:_) -> b
                   [] -> Prelude.head universeF -- Return a failed counter-example to be pruned by 'point'


{-
exm1, exm2, exm3 :: Cont Bool Integer
exm1 = cont $ \ib -> (ib 7 && ib 4) || ib 8
exm2 = cont $ \ib -> (ib 7 || ib 8) && (ib 4 || ib 8)
exm3 = cont $ \ib -> (ib 7 || ib 8) && ib 4

-- exm1 ~~ exm2 >~ exm3
ex1 = (exm1 ~~ exm2, exm1 ~~ exm3, exm2 ~~ exm3) --(True, False, False)
ex2 = (exm1 ~~ exm2, exm1 >~ exm3, exm2 >~ exm3) --(True, True, True)
ex3 = (exm1 ~~ exm2 \/ exm3) -- True

-- exm2 >~ exm3
-- λ> runCont exm2 diff
-- True
-- λ> runCont exm3 diff
-- False
diff :: Integer -> Bool
diff i = if i ~~ 7 || i ~~ 8 then True else False
-}
