{-# Language TypeFamilies        #-}
{-# Language TypeApplications    #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}
{-# Language DeriveFunctor       #-}
{-# Language DeriveGeneric       #-}
module Data.Connection.Type (
  -- * Conn
    Conn(..)
  , unit
  , counit
  , connl
  , connr
  , conn1l
  , conn1r
  , conn2l
  , conn2r
  , strong
  , choice
  , mapped
  -- * Trip
  , Trip(..)
  , tripl
  , tripr
  , unitl
  , unitr
  , counitl
  , counitr
  , floorOn
  , ceilingOn
  , strong'
  , choice'
  , mapped'
  -- * Iterators
  , until
  , while
  , fixed
  -- * Lattice Extensions
  , type Lifted
  , type Lowered
  , lifts
  , lifted
  , lowers
  , lowered
  , extends
  , liftMaybe
  , liftEitherL
  , liftEitherR
  , liftExtended
) where

import safe Control.Category (Category)
import safe Data.Bifunctor (bimap)
import safe Data.Lattice
import safe Data.Semigroup.Join (eq)
import safe Prelude hiding (Ord(..), Bounded, until)
import safe qualified Control.Category as C


-- | A Galois connection between two monotone functions.
--
-- A Galois connection between /f/ and /g/, written \(f \dashv g \)
-- is an adjunction in the category of preorders.
--
-- Each side of the connection may be defined in terms of the other:
-- 
--  \( g(x) = \sup \{y \in E \mid f(y) \leq x \} \)
--
--  \( f(x) = \inf \{y \in E \mid g(y) \geq x \} \)
--
-- For further information see 'Data.Connection.Property' and <https://ncatlab.org/nlab/show/Galois+connection>.
--
-- /Caution/: Monotonicity is not checked.
--
data Conn a b = Conn (a -> b) (b -> a)

instance Category Conn where
  id = Conn id id
  Conn f' g' . Conn f g = Conn (f' . f) (g . g')

-- | Round trip through a connection.
--
-- > x <= unit x
--
unit :: Conn a b -> a -> a
unit c = conn1r c id

-- | Reverse round trip through a connection.
--
-- > counit x <= x
--
counit :: Conn a b -> b -> b
counit c = conn1l c id

-- | Extract the left side of a connection.
--
connl :: Conn a b -> a -> b
connl (Conn f _) = f

-- | Extract the right side of a connection.
--
connr :: Conn a b -> b -> a
connr (Conn _ g) = g

-- | Map over a connection from the left.
--
conn1l :: Conn a b -> (a -> a) -> b -> b
conn1l (Conn f g) h b = f $ h (g b)

-- | Map over a connection from the right.
--
conn1r :: Conn a b -> (b -> b) -> a -> a
conn1r (Conn f g) h a = g $ h (f a)

-- | Zip over a connection from the left.
--
conn2l :: Conn a b -> (a -> a -> a) -> b -> b -> b
conn2l (Conn f g) h b1 b2 = f $ h (g b1) (g b2)

-- | Zip over a connection from the right.
--
conn2r :: Conn a b -> (b -> b -> b) -> a -> a -> a
conn2r (Conn f g) h a1 a2 = g $ h (f a1) (f a2)

-- |
--
-- > (strong id) (ab >>> cd) = (strong id) ab >>> (strong id) cd
-- > (flip strong id) (ab >>> cd) = (flip strong id) ab >>> (flip strong id) cd
--
strong :: Conn a b -> Conn c d -> Conn (a, c) (b, d)
strong (Conn ab ba) (Conn cd dc) = Conn (bimap ab cd) (bimap ba dc)

-- |
--
-- > (choice id) (ab >>> cd) = (choice id) ab >>> (choice id) cd
-- > (flip choice id) (ab >>> cd) = (flip choice id) ab >>> (flip choice id) cd
--
choice :: Conn a b -> Conn c d -> Conn (Either a c) (Either b d)
choice (Conn ab ba) (Conn cd dc) = Conn f g where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)

mapped :: Functor f => Conn a b -> Conn (f a) (f b)
mapped (Conn f g) = Conn (fmap f) (fmap g)

--infixr 3 &&&
--(&&&) :: (Join-Semigroup) c => (Meet-Semigroup) c => Conn c a -> Conn c b -> Conn c (a, b)
--f &&& g = tripr forked >>> f `strong` g

---------------------------------------------------------------------
-- Triple connections
---------------------------------------------------------------------

-- | An adjoint triple of Galois connections.
--
-- An adjoint triple is a chain of connections of length 2:
--
-- \(f \dashv g \dashv h \) 
--
-- For further information see 'Data.Connection.Property' and <https://ncatlab.org/nlab/show/adjoint+triple>.
--
data Trip a b = Trip (a -> b) (b -> a) (a -> b)

instance Category Trip where
  id = Trip id id id
  Trip f' g' h' . Trip f g h = Trip (f' . f) (g . g') (h' . h)

tripl :: Trip a b -> Conn a b
tripl (Trip f g _) = Conn f g

tripr :: Trip a b -> Conn b a
tripr (Trip _ g h) = Conn g h

unitl :: Trip a b -> a -> a
unitl = unit . tripl

unitr :: Trip a b -> b -> b
unitr = unit . tripr

counitl :: Trip a b -> b -> b
counitl = counit . tripl

counitr :: Trip a b -> a -> a
counitr = counit . tripr

-- @ floorOn C.id == id @
floorOn :: Trip a b -> a -> b
floorOn = connr . tripr

-- @ ceilingOn C.id == id @
ceilingOn :: Trip a b -> a -> b
ceilingOn = connl . tripl

strong' :: Trip a b -> Trip c d -> Trip (a, c) (b, d)
strong' (Trip ab ba ab') (Trip cd dc cd') = Trip f g h where
  f = bimap ab cd 
  g = bimap ba dc
  h = bimap ab' cd'

choice' :: Trip a b -> Trip c d -> Trip (Either a c) (Either b d)
choice' (Trip ab ba ab') (Trip cd dc cd') = Trip f g h where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)
  h = either (Left . ab') (Right . cd')

mapped' :: Functor f => Trip a b -> Trip (f a) (f b)
mapped' (Trip f g h) = Trip (fmap f) (fmap g) (fmap h)

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

-------------------------------------------------------------------------------
-- Lattice extensions
-------------------------------------------------------------------------------

lifts :: (Join-Monoid) a => Eq a => (a -> b) -> a -> Lifted b
lifts = liftEitherL (eq bottom)

lifted :: (Join-Monoid) b => (a -> b) -> Lifted a -> b
lifted f = either (const bottom) f

lowers :: (Meet-Monoid) a => Eq a => (a -> b) -> a -> Lowered b
lowers = liftEitherR (eq top) 

lowered :: (Meet-Monoid) b => (a -> b) -> Lowered a -> b
lowered f = either f (const top)

extends :: Bounded b => (a -> b) -> Extended a -> b
extends f = extended bottom top f

liftMaybe :: (a -> Bool) -> (a -> b) -> a -> Maybe b
liftMaybe p f = g where
  g i | p i = Nothing
      | otherwise = Just $ f i

liftEitherL :: (a -> Bool) -> (a -> b) -> a -> Lifted b
liftEitherL p f = g where
  g i | p i = Left ()
      | otherwise = Right $ f i

liftEitherR :: (a -> Bool) -> (a -> b) -> a -> Lowered b
liftEitherR p f = g where
  g i | p i = Right ()
      | otherwise = Left $ f i

liftExtended :: (a -> Bool) -> (a -> Bool) -> (a -> b) -> a -> Extended b
liftExtended p q f = g where
  g i | p i = Bottom
      | q i = Top
      | otherwise = Extended $ f i
