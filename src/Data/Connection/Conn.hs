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
{-# Language RankNTypes          #-}
module Data.Connection.Conn (
  -- * Conn
    Kan(..)
  , Conn()
  , embed
  -- ** Trip
  , type Trip
  , pattern Conn
  , trip
  , range
  -- ** ConnL
  , type ConnL
  , pattern ConnL
  , swapL
  , downL
  , unitL
  , counitL
  , lowerL
  , lowerL1
  , lowerL2
  , upperL1
  , upperL2
  -- ** ConnR
  , type ConnR
  , pattern ConnR
  , swapR
  , downR
  , unitR
  , counitR
  , upperR
  , upperR1
  , upperR2
  , lowerR1
  , lowerR2
  -- * Connections
  , choice
  , strong
  , fmapped
) where

import safe Control.Arrow
import safe Control.Category (Category)
import safe Data.Bifunctor (bimap)
import safe Data.Order
import safe Prelude hiding (Ord(..), Bounded)
import safe qualified Control.Category as C

-- | A data kind distinguishing the chirality of a Kan extension.
--
-- Here it serves to distinguish the directionality of a preorder:
--
-- * /L/-tagged types are 'upwards-directed'
--
-- * /R/-tagged types are 'downwards-directed'
--
data Kan = L | R

-- | An < https://ncatlab.org/nlab/show/adjoint+string adjoint string > of Galois connections of length 2 or 3.
--
data Conn (k :: Kan) a b = Conn_ (a -> (b , b)) (b -> a)

instance Category (Conn k) where
  id = Conn_ (id &&& id) id

  Conn_ f1 g1 . Conn_ f2 g2 = Conn_ ((fst.f1).(fst.f2) &&& (snd.f1).(snd.f2)) (g2 . g1)

-- | Obtain the center of a /Trip/, upper half of a /ConnL/, or the lower half of a /ConnR/.
--
embed :: Conn k a b -> b -> a
embed (Conn_ _ g) = g

-- Internal floor function. When \(f \dashv g \dashv h \) this is h.
_1 :: Conn k a b -> a -> b
_1 (Conn_ f _) = fst . f

-- Internal ceiling function. When \(f \dashv g \dashv h \) this is f.
_2 :: Conn k a b -> a -> b
_2 (Conn_ f _) = snd . f

---------------------------------------------------------------------
-- Trip
---------------------------------------------------------------------

-- | An <https://ncatlab.org/nlab/show/adjoint+triple adjoint triple> of Galois connections.
--
-- An adjoint triple is a chain of connections of length 3:
--
-- \(f \dashv g \dashv h \) 
--
-- For detailed properties see 'Data.Connection.Property'.
--
type Trip a b = forall k. Conn k a b

-- | A view pattern for an arbitrary (left or right) 'Conn'.
--
-- /Caution/: /Conn f g h/ must obey \(f \dashv g \dashv h\). This condition is not checked.
--
-- For detailed properties see 'Data.Connection.Property'.
--
pattern Conn :: (a -> b) -> (b -> a) -> (a -> b) -> Conn k a b
pattern Conn f g h <- (embed &&& _1 &&& _2 -> (g, (h, f)))
  where Conn f g h = Conn_ (h &&& f) g
{-# COMPLETE Conn #-}

-- | Obtain a /forall k. Conn k/ from an adjoint triple of monotone functions.
--
-- /Caution/: @Conn f g h@ must obey \(f \dashv g \dashv h\). This condition is not checked.
--
trip :: (a -> b) -> (b -> a) -> (a -> b) -> Trip a b
trip f g h = Conn_ (h &&& f) g

-- | Obtain the lower and upper functions from a 'Trip'.
--
-- > range c = upperR c &&& lowerL c
--
-- >>> range f64f32 pi
-- (3.1415925,3.1415927)
-- >>> range f64f32 (0/0)
-- (NaN,NaN)
--
range :: Trip a b -> a -> (b, b)
range c = upperR c &&& lowerL c 

---------------------------------------------------------------------
-- ConnL
---------------------------------------------------------------------

-- | A <https://ncatlab.org/nlab/show/Galois+connection Galois connection> between two monotone functions.
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
-- For further information see 'Data.Connection.Property'.
--
-- /Caution/: Monotonicity is not checked.
--
type ConnL = Conn 'L

-- | A view pattern for a 'ConnL'.
--
-- /Caution/: /ConnL f g/ must obey \(f \dashv g \). This condition is not checked.
--
pattern ConnL :: (a -> b) -> (b -> a) -> ConnL a b
pattern ConnL f g <- (_2 &&& embed -> (f, g)) where ConnL f g = Conn_ (f &&& f) g
{-# COMPLETE ConnL #-}

-- | Witness to the symmetry between 'ConnL' and 'ConnR'.
--
-- > swapL . swapR = id
-- > swapR . swapL = id
--
swapL :: ConnR a b -> ConnL b a
swapL (ConnR f g) = ConnL f g

-- | Convert an arbitrary 'Conn' to an inverted 'ConnL'.
--
-- >>> unitL (downL $ conn @_ @() @Ordering) (Down LT)
-- Down LT
-- >>> unitL (downL $ conn @_ @() @Ordering) (Down GT)
-- Down LT
--
downL :: ConnL a b -> ConnL (Down b) (Down a)
downL (ConnL f g) = ConnL (\(Down x) -> Down $ g x) (\(Down x) -> Down $ f x)

-- | Round trip through a connection.
--
-- > unitL c = upperL1 c id = embed c . lowerL c
-- > x <= unitL c x
-- 
-- >>> compare pi $ unitL f64f32 pi
-- LT
--
unitL :: ConnL a b -> a -> a
unitL c = upperL1 c id

-- | Reverse round trip through a connection.
--
-- > x >= counitL c x
--
-- >>> counitL (conn @_ @() @Ordering) LT
-- LT
-- >>> counitL (conn @_ @() @Ordering) GT
-- LT
--
counitL :: ConnL a b -> b -> b
counitL c = lowerL1 c id

-- | Extract the lower half of a 'Trip' or 'ConnL'.
--
-- When /a/ and /b/ are lattices we have:
--
-- > lowerL c (x1 \/ a2) = lowerL c x1 \/ lowerL c x2
--
-- This is the adjoint functor theorem for preorders.
--
-- >>> upperR f64f32 pi
-- 3.1415925
-- >>> lowerL f64f32 pi
-- 3.1415927
--
lowerL :: ConnL a b -> a -> b
lowerL (ConnL f _) = f

-- | Map over a connection from the left.
--
lowerL1 :: ConnL a b -> (a -> a) -> b -> b
lowerL1 (ConnL f g) h b = f $ h (g b)

-- | Zip over a connection from the left.
--
lowerL2 :: ConnL a b -> (a -> a -> a) -> b -> b -> b
lowerL2 (ConnL f g) h b1 b2 = f $ h (g b1) (g b2)

-- | Map over a connection from the left.
--
upperL1 :: ConnL a b -> (b -> b) -> a -> a
upperL1 (ConnL f g) h a = g $ h (f a)

-- | Zip over a connection from the left.
--
upperL2 :: ConnL a b -> (b -> b -> b) -> a -> a -> a
upperL2 (ConnL f g) h a1 a2 = g $ h (f a1) (f a2)

---------------------------------------------------------------------
-- ConnR
---------------------------------------------------------------------

-- | A Galois connection between two monotone functions.
--
-- 'ConnR' is the mirror image of 'ConnL':
--
-- > swapR :: ConnL a b -> ConnR b a
--
-- If you only require one connection there is no particular reason to
-- use one version over the other.
--
-- However some use cases (e.g. rounding) require an adjoint triple
-- of connections (i.e. a 'Trip') that can lower into a standard
-- connection in either of two ways.
--
type ConnR = Conn 'R

-- | A view pattern for a 'ConnR'.
--
-- /Caution/: /ConnR f g/ must obey \(f \dashv g \). This condition is not checked.
--
pattern ConnR :: (b -> a) -> (a -> b) -> ConnR a b
pattern ConnR f g <- (embed &&& _1 -> (f, g)) where ConnR f g = Conn_ (g &&& g) f
{-# COMPLETE ConnR #-}

-- | Convert an arbitrary 'Conn' to an inverted 'ConnR'.
--
-- >>> counitR (downR $ conn @_ @() @Ordering) (Down LT)
-- Down GT
-- >>> counitR (downR $ conn @_ @() @Ordering) (Down GT)
-- Down GT
--
downR :: ConnR a b -> ConnR (Down b) (Down a)
downR (ConnR f g) = ConnR (\(Down x) -> Down $ g x) (\(Down x) -> Down $ f x)

-- | Witness to the symmetry between 'ConnL' and 'ConnR'.
--
-- > swapL . swapR = id
-- > swapR . swapL = id
--
swapR :: ConnL a b -> ConnR b a
swapR (ConnL f g) = ConnR f g

-- | Round trip through a connection.
--
-- > unitR c = upperR1 c id = upperR c . embed c
-- > x <= unitR c x
--
-- >>> unitR (conn @_ @() @Ordering) LT
-- GT
-- >>> unitR (conn @_ @() @Ordering) GT
-- GT
--
unitR :: ConnR a b -> b -> b
unitR c = upperR1 c id

-- | Reverse round trip through a connection.
--
-- > x >= counitR c x
--
-- >>> compare pi $ counitR f64f32 pi
-- GT
--
counitR :: ConnR a b -> a -> a
counitR c = lowerR1 c id

-- | Extract the upper half of a connection.
--
-- When /a/ and /b/ are lattices we have:
--
-- > upperR c (x1 /\ x2) = upperR c x1 /\ upperR c x2
--
-- This is the adjoint functor theorem for preorders.
--
-- >>> upperR f64f32 pi
-- 3.1415925
-- >>> lowerL f64f32 pi
-- 3.1415927
--
upperR :: ConnR a b -> a -> b
upperR (ConnR _ g) = g

-- | Map over a connection from the left.
--
upperR1 :: ConnR a b -> (a -> a) -> b -> b
upperR1 (ConnR f g) h b = g $ h (f b)

-- | Zip over a connection from the left.
--
upperR2 :: ConnR a b -> (a -> a -> a) -> b -> b -> b
upperR2 (ConnR f g) h b1 b2 = g $ h (f b1) (f b2)

-- | Map over a connection from the right.
--
lowerR1 :: ConnR a b -> (b -> b) -> a -> a
lowerR1 (ConnR f g) h a = f $ h (g a)

-- | Zip over a connection from the right.
--
lowerR2 :: ConnR a b -> (b -> b -> b) -> a -> a -> a
lowerR2 (ConnR f g) h a1 a2 = f $ h (g a1) (g a2)

---------------------------------------------------------------------
-- Connections
---------------------------------------------------------------------

-- | Lift two 'Conn's into a 'Conn' on the <https://en.wikibooks.org/wiki/Category_Theory/Categories_of_ordered_sets coproduct order>
--
-- > (choice id) (ab >>> cd) = (choice id) ab >>> (choice id) cd
-- > (flip choice id) (ab >>> cd) = (flip choice id) ab >>> (flip choice id) cd
--
choice :: Conn k a b -> Conn k c d -> Conn k (Either a c) (Either b d)
choice (Conn ab ba ab') (Conn cd dc cd') = Conn f g h where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)
  h = either (Left . ab') (Right . cd')

-- | Lift two 'Conn's into a 'Conn' on the <https://en.wikibooks.org/wiki/Order_Theory/Preordered_classes_and_poclasses#product_order product order>
--
-- > (strong id) (ab >>> cd) = (strong id) ab >>> (strong id) cd
-- > (flip strong id) (ab >>> cd) = (flip strong id) ab >>> (flip strong id) cd
--
strong :: Conn k a b -> Conn k c d -> Conn k (a, c) (b, d)
strong (Conn ab ba ab') (Conn cd dc cd') = Conn f g h where
  f = bimap ab cd 
  g = bimap ba dc
  h = bimap ab' cd'

-- | Lift a 'Conn' into a functor.
--
-- /Caution/: This function will result in an invalid connection
-- if the functor alters the internal preorder (i.e. 'Data.Ord.Down').
--
fmapped :: Functor f => Conn k a b -> Conn k (f a) (f b)
fmapped (Conn f g h) = Conn (fmap f) (fmap g) (fmap h)
