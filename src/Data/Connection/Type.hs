{-# Language TypeFamilies        #-}
{-# Language TypeApplications    #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}
{-# Language DeriveFunctor       #-}
{-# Language DeriveGeneric       #-}
{-# Language DataKinds           #-}
{-# Language ViewPatterns        #-}
{-# Language PatternSynonyms     #-}
module Data.Connection.Type {- (
  -- * Conn
    Conn()
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
) -}
where

import safe Control.Arrow
import safe Control.Category (Category)
import safe Data.Bifunctor (bimap)
import safe Data.Functor.Identity
import safe Data.Functor.Rep
import safe Data.Lattice
import safe Data.Order
import safe Data.Semigroup.Foldable
import safe Prelude hiding (Ord(..), Bounded, until)
import safe qualified Control.Category as C

data Kan = L | R

type ConnL = Conn L

type ConnR = Conn R

data Conn (k :: Kan) a b = Conn (a -> (b , b)) (b -> a)

instance Category (Conn k) where
  id = Conn (id &&& id) id

  Conn f1 g1 . Conn f2 g2 = Conn ((fst.f1).(fst.f2) &&& (snd.f1).(snd.f2)) (g2 . g1)


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
-- For further information see 'Data.Connection.Property' and <https://ncatlab.org/nlab/show/Conn+connection>.
--
-- /Caution/: Monotonicity is not checked.
--



-- | A view pattern for a 'Connl'.
--
-- /Caution/: /Conn f g/ must obey \(f \dashv g \). This condition is not checked.
--
pattern ConnL :: (a -> b) -> (b -> a) -> ConnL a b
pattern ConnL f g <- (connl &&& connr -> (f, g)) where ConnL f g = connl f g

{-
-- | Construct a Galois connection between two monotone functions.
--
-- /Caution/: /conn f g/ must obey \(f \dashv g \). This condition is not checked.
--
conn :: (a -> b) -> (b -> a) -> Conn a b
conn f g = Conn (f &&& f) g

-- | Extract the left side of a connection.
--
connl :: Conn a b -> a -> b
connl (Conn f _) = snd . f -- ???

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
type Trip = Conn Triple

-- /Caution/: /Trip f g h/ must obey \(f \dashv g \dashv h \). This condition is not checked.
--
pattern Trip :: (a -> b) -> (b -> a) -> (a -> b) -> Conn n a b
pattern Trip f1 g f2 <- (ebd &&& clg &&& flr -> (g,(f1,f2))) where Trip f1 g f2 = trip f1 g f2

-- connl . tripr
ebd (Conn _ g) = g
-- connl . tripl 
clg (Conn f _) = fst . f
-- connr . tripr   
flr (Conn f _) = snd . f 

-- | Extract the ceiling and floor functions from a 'Trip'.
--
-- > fst . range t a <~ snd . range t a
--
-- λ> range (bounded @Ordering) ()
-- (LT,GT)
-- 
range :: Trip a b -> a -> (b, b)
range (Conn f _) = (snd &&& fst) . f

-- /Caution/: /trip f g h/ must obey \(f \dashv g \dashv h \). This condition is not checked.
--
trip :: (a -> b) -> (b -> a) -> (a -> b) -> Conn n a b
trip f1 g f2 = Conn (f1 &&& f2) g

-- | Extract the first half of a triple.
--
-- > (connr . tripr) t x < (connl . tripl) t x
--
tripl :: Trip a b -> Conn a b
tripl (Conn f g) = Conn (snd.f) g

-- | Extract the second half of a triple.
--
tripr :: Trip a b -> Conn b a
tripr (Conn f g) = Conn g (fst.f)

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

bounded :: Bounded a => Conn n () a
bounded = Conn (const top &&& const bottom) (const ())

{-
instance LowerBounded a => Connection () a where
  connection = Conn (const bottom) (const ())

instance UpperBounded a => Connection a () where
  connection = Conn (const ()) (const top)

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

instance LowerBounded a => Connection () a where
  connection = Conn (const bottom) (const ())

instance UpperBounded a => Connection a () where
  connection = Conn (const ()) (const top)
-}


forked :: Lattice a => Conn n (a, a) a
forked = Conn (uncurry (\/) &&& uncurry (/\)) (\x -> (x,x))

joined :: Conn n a (Either a a)
joined = Conn (Left &&& Right) (either id id)

infixr 4 /|\

(/|\) :: Lattice c => Conn n a c -> Conn n b c -> Conn n (a, b) c
f /|\ g = f `strong` g C.>>> forked

infixr 3 \|/

(\|/) :: Conn n c a -> Conn n c b -> Conn n c (Either a b)
f \|/ g = joined C.>>> f `choice` g

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
strong :: Conn n a b -> Conn n c d -> Conn n (a, c) (b, d)
strong (Conn ab ba) (Conn cd dc) = Conn f g where
  f = bimap (fst.ab) (fst.cd) &&& bimap (snd.ab) (snd.cd)
  g = bimap ba dc

-- |
--
-- > (choice id) (ab >>> cd) = (choice id) ab >>> (choice id) cd
-- > (flip choice id) (ab >>> cd) = (flip choice id) ab >>> (flip choice id) cd
--
choice :: Conn n a b -> Conn n c d -> Conn n (Either a c) (Either b d)
choice (Conn ab ba) (Conn cd dc) = Conn f g where
  f = either (Left . fst.ab) (Right . fst.cd) &&& either (Left . snd.ab) (Right . snd.cd)
  g = either (Left . ba) (Right . dc)

mapped :: Functor f => Conn n a b -> Conn n (f a) (f b)
mapped (Conn f g) = Conn (fmap (fst.f) &&& fmap (snd.f)) (fmap g)
-}
