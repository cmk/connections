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
  , connl
  , connr
  , connl1
  , connr1
  , connl2
  , connr2
  , unit
  , counit
  , (|||)
  , (&&&)
  -- * Trip
  , Trip(..)
  , tripl
  , tripr
  , unit'
  , counit'
  -- ** Connections
  , dual
  , liftl
  , liftr
  , joined
  , forked
  , strong
  , strong'
  , choice
  , choice'
  , mapped
  , mapped'
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
connl1 :: Conn a b -> (a -> a) -> b -> b
connl1 (Conn f g) h b = f $ h (g b)

-- | Map over a connection from the right.
--
connr1 :: Conn a b -> (b -> b) -> a -> a
connr1 (Conn f g) h a = g $ h (f a)

-- | Zip over a connection from the left.
--
connl2 :: Conn a b -> (a -> a -> a) -> b -> b -> b
connl2 (Conn f g) h b1 b2 = f $ h (g b1) (g b2)

-- | Zip over a connection from the right.
--
connr2 :: Conn a b -> (b -> b -> b) -> a -> a -> a
connr2 (Conn f g) h a1 a2 = g $ h (f a1) (f a2)

-- | Round trip through a connection.
--
-- > x <~ unit x
--
unit :: Conn a b -> a -> a
unit c = connr1 c id

-- | Reverse round trip through a connection.
--
-- > counit x <~ x
--
counit :: Conn a b -> b -> b
counit c = connl1 c id

infixr 3 |||

(|||) :: Conn c a -> Conn c b -> Conn c (Either a b)
f ||| g = tripl joined C.>>> f `choice` g

infixr 3 &&&

(&&&) :: Lattice c => Conn c a -> Conn c b -> Conn c (a, b)
f &&& g = tripr forked C.>>> f `strong` g

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

-- | Extract the first half of a triple.
--
-- > (connr . tripr) t x < (connl . tripl) t x
--
tripl :: Trip a b -> Conn a b
tripl (Trip f g _) = Conn f g

-- | Extract the second half of a triple.
--
tripr :: Trip a b -> Conn b a
tripr (Trip _ g h) = Conn g h

-- | Return the lesser of the two representations bracketing /a/.
--
-- >>> compare P.pi $ unit' f64f32 P.pi
-- LT
--
unit' :: Trip a b -> a -> a
unit' = unit . tripl

-- | Return the greater of the two representations bracketing /a/.
--
-- >>> compare P.pi $ counit' f64f32 P.pi
-- GT
--
counit' :: Trip a b -> a -> a
counit' = counit . tripr

---------------------------------------------------------------------
-- Connections
---------------------------------------------------------------------

dual :: Conn a b -> Conn (Down b) (Down a)
dual (Conn f g) = Conn (\(Down x) -> Down $ g x) (\(Down x) -> Down $ f x)


liftl :: Bounded b => Trip (Maybe a) (Either a b)
liftl = Trip f g h where
  f = maybe (Right bottom) Left
  g = either Just (const Nothing)
  h = maybe (Right top) Left

liftr :: Bounded a => Trip (Maybe b) (Either a b)
liftr = Trip f g h where
  f = maybe (Left bottom) Right
  g = either (const Nothing) Just
  h = maybe (Left top) Right

joined :: Trip a (Either a a)
joined = Trip Left (either id id) Right

forked :: Lattice a => Trip (a, a) a
forked = Trip (uncurry (\/)) (\x -> (x,x)) (uncurry (/\))

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
