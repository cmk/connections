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
  -- * Trip
  , Trip(..)
  , tripl
  , tripr
  , unitl
  , unitr
  , counitl
  , counitr
  -- ** Connections
  , dual
  , strong
  , strong'
  , choice
  , choice'
  , mapped
  , mapped'
  , stackl
  , stackr
  -- * Iterators
  , until
  , while
  , fixed
) where

import safe Control.Category (Category)
import safe Data.Bifunctor (bimap)
import safe Data.Functor.Identity
import safe Data.Functor.Rep
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Order.Interval
import safe Data.Semigroup.Foldable
import safe Data.Lattice
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
-- > x <~ unit x
--
unit :: Conn a b -> a -> a
unit c = conn1r c id

-- | Reverse round trip through a connection.
--
-- > counit x <~ x
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

---------------------------------------------------------------------
-- Trip
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

-- |
--
-- >>> compare P.pi $ unitl f64f32 P.pi
-- LT
--
unitl :: Trip a b -> a -> a
unitl = unit . tripl

-- |
--
-- >>> compare P.pi $ counitr f64f32 P.pi
-- GT
--
unitr :: Trip a b -> b -> b
unitr = unit . tripr

counitl :: Trip a b -> b -> b
counitl = counit . tripl

counitr :: Trip a b -> a -> a
counitr = counit . tripr

---------------------------------------------------------------------
-- Connections
---------------------------------------------------------------------

dual :: Conn a b -> Conn (Down b) (Down a)
dual (Conn f g) = Conn (\(Down x) -> Down $ g x) (\(Down x) -> Down $ f x)

-- |
--
-- > (strong id) (ab >>> cd) = (strong id) ab >>> (strong id) cd
-- > (flip strong id) (ab >>> cd) = (flip strong id) ab >>> (flip strong id) cd
--
strong :: Conn a b -> Conn c d -> Conn (a, c) (b, d)
strong (Conn ab ba) (Conn cd dc) = Conn (bimap ab cd) (bimap ba dc)

strong' :: Trip a b -> Trip c d -> Trip (a, c) (b, d)
strong' (Trip ab ba ab') (Trip cd dc cd') = Trip f g h where
  f = bimap ab cd 
  g = bimap ba dc
  h = bimap ab' cd'

-- |
--
-- > (choice id) (ab >>> cd) = (choice id) ab >>> (choice id) cd
-- > (flip choice id) (ab >>> cd) = (flip choice id) ab >>> (flip choice id) cd
--
choice :: Conn a b -> Conn c d -> Conn (Either a c) (Either b d)
choice (Conn ab ba) (Conn cd dc) = Conn f g where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)

choice' :: Trip a b -> Trip c d -> Trip (Either a c) (Either b d)
choice' (Trip ab ba ab') (Trip cd dc cd') = Trip f g h where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)
  h = either (Left . ab') (Right . cd')

mapped :: Functor f => Conn a b -> Conn (f a) (f b)
mapped (Conn f g) = Conn (fmap f) (fmap g)

mapped' :: Functor f => Trip a b -> Trip (f a) (f b)
mapped' (Trip f g h) = Trip (fmap f) (fmap g) (fmap h)

stackr :: Bounded a => Trip (Maybe b) (Either a b)
stackr = Trip f g h where
  f = maybe (Left bottom) Right
  g = either (const Nothing) Just
  h = maybe (Left top) Right

stackl :: Bounded b => Trip (Maybe a) (Either a b)
stackl = Trip f g h where
  f = maybe (Right bottom) Left
  g = either Just (const Nothing)
  h = maybe (Right top) Left

--infixr 3 &&&
--(&&&) :: Lattice c => Conn c a -> Conn c b -> Conn c (a, b)
--f &&& g = tripr forked >>> f `strong` g
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
