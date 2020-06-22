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
  , Trip
  , pattern Conn
  , trip
  , range
  -- ** ConnL
  , ConnL
  , pattern ConnL
  , lft
  , lft'
  , swapL
  , unitL
  , counitL
  , lowerL
  , lowerL1
  , lowerL2
  , upperL1
  , upperL2
  -- ** ConnR
  , ConnR
  , pattern ConnR
  , rgt
  , rgt'
  , swapR
  , unitR
  , counitR
  , upperR
  , upperR1
  , upperR2
  , lowerR1
  , lowerR2
  -- * Connections
  , bounded
  , (\|/)
  , (/|\)
  , joined
  , forked
  , choice
  , strong
  , fmapped
) where

import safe Control.Arrow
import safe Control.Category (Category, (>>>))
import safe Data.Bifunctor (bimap)
import safe Data.Functor.Identity
import safe Data.Functor.Rep
import safe Data.Lattice
import safe Data.Order
import safe Data.Semigroup.Foldable
import safe Prelude hiding (Ord(..), Bounded, range, until)
import safe qualified Control.Category as C

-- | A data kind distinguishing the chirality of a Kan extension.
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

---------------------------------------------------------------------
-- Trip
---------------------------------------------------------------------

-- | An <https://ncatlab.org/nlab/show/adjoint+triple adjoint triple> of Galois connections.
--
-- An  adjoint triple is a chain of connections of length 3:
--
-- \(f \dashv g \dashv h \) 
--
-- For detailed properties see 'Data.Connection.Property'.
--
type Trip a b = forall k. Conn k a b

-- | A view pattern for a 'Trip'.
--
-- /Caution/: /Conn f1 g f2/ must obey \(f1 \dashv g \dashv f2\). This condition is not checked.
--
-- For detailed properties see 'Data.Connection.Property'.
--
pattern Conn :: (a -> b) -> (b -> a) -> (a -> b) -> Conn k a b
pattern Conn f1 g f2 <- (embed &&& _2 &&& _1 -> (g,(f1,f2)))
  where Conn f1 g f2 = Conn_ (f2 &&& f1) g
{-# COMPLETE Conn #-}

-- | Obtain a /forall k. Conn k/ from an adjoint triple of monotone functions.
--
-- /Caution/: @Conn f g h@ must obey \(f \dashv g \dashv h\). This condition is not checked.
--
trip :: (a -> b) -> (b -> a) -> (a -> b) -> Trip a b
trip f1 g f2 = Conn_ (f2 &&& f1) g

-- | Obtain the lower and upper functions from a 'Trip'.
--
-- > range c = upperR c &&& lowerL c
--
-- >>> range (bounded @Ordering) ()
-- (LT,GT)
-- >>> range f64f32 pi
-- (3.1415925,3.1415927)
--
range :: Trip a b -> a -> (b, b)
range c = _1 c &&& _2 c 

_1 :: Conn k a b -> a -> b
_1 (Conn_ f _) = fst . f

_2 :: Conn k a b -> a -> b
_2 (Conn_ f _) = snd . f

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
pattern ConnL f g <- (lowerL &&& embed -> (f, g)) where ConnL f g = Conn_ (f &&& f) g
{-# COMPLETE ConnL #-}

-- | Convert an arbitrary 'Conn' to a 'ConnL'.
--
lft :: Conn k a b -> ConnL a b
lft (Conn_ f g) = ConnL (snd.f) g

-- | Convert an arbitrary 'Conn' to an inverted 'ConnL'.
--
-- >>> unitL (lft' $ bounded @Ordering) (Down LT)
-- Down LT
-- >>> unitL (lft' $ bounded @Ordering) (Down EQ)
-- Down LT
-- >>> unitL (lft' $ bounded @Ordering) (Down GT)
-- Down LT
--
lft' :: Conn k a b -> ConnL (Down b) (Down a)
lft' (Conn_ f g) = ConnL (\(Down x) -> Down $ g x) (\(Down x) -> Down $ (snd.f) x)

-- | Witness to the symmetry between 'ConnL' and 'ConnR'.
--
-- > swapL . swapR = id
-- > swapR . swapL = id
--
swapL :: ConnR a b -> ConnL b a
swapL (ConnR f g) = ConnL f g

-- | Round trip through a connection.
--
-- > unitL c = upperL1 c id = embed c . lowerL c
--
-- > x <~ unitL c x
-- 
-- >>> compare pi $ unitL f64f32 pi
-- LT
--
unitL :: ConnL a b -> a -> a
unitL c = upperL1 c id

-- | Reverse round trip through a connection.
--
-- > x >~ counitL c x
--
-- >>> counitL (bounded @Ordering) LT
-- GT
-- >>> counitL (bounded @Ordering) EQ
-- GT
-- >>> counitL (bounded @Ordering) GT
-- GT
--
counitL :: ConnL a b -> b -> b
counitL c = lowerL1 c id

-- | Extract the lower half of a 'Trip' or 'ConnL'.
--
-- > upperR c x <~ lowerL c x
--
-- >>> upperR (bounded @Ordering) ()
-- LT
-- >>> lowerL (bounded @Ordering) ()
-- GT
--
lowerL :: ConnL a b -> a -> b
lowerL (Conn_ f _) = snd . f

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
pattern ConnR f g <- (embed &&& upperR -> (f, g)) where ConnR f g = Conn_ (g &&& g) f
{-# COMPLETE ConnR #-}

-- | Convert an arbitrary 'Conn' to a 'ConnR'.
--
rgt :: Conn k a b -> ConnR a b
rgt (Conn_ f g) = ConnR g (fst.f)

-- | Convert an arbitrary 'Conn' to an inverted 'ConnR'.
--
-- >>> counitR (rgt' $ bounded @Ordering) (Down LT)
-- Down GT
-- >>> counitR (rgt' $ bounded @Ordering) (Down EQ)
-- Down GT
-- >>> counitR (rgt' $ bounded @Ordering) (Down GT)
-- Down GT
--
rgt' :: Conn k a b -> ConnR (Down b) (Down a)
rgt' (Conn_ f g) = ConnR (\(Down x) -> Down $ (fst.f) x) (\(Down x) -> Down $ g x)

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
--
-- > x <~ unitR c x
--
-- >>> unitR (bounded @Ordering) LT
-- LT
-- >>> unitR (bounded @Ordering) EQ
-- LT
-- >>> unitR (bounded @Ordering) GT
-- LT
--
unitR :: ConnR a b -> b -> b
unitR c = upperR1 c id

-- | Reverse round trip through a connection.
--
-- > x >~ counitR c x
--
-- >>> compare pi $ counitR f64f32 pi
-- GT
--
counitR :: ConnR a b -> a -> a
counitR c = lowerR1 c id

-- | Extract the upper half of a Connection.
--
upperR :: ConnR a b -> a -> b
upperR (Conn_ f _) = fst . f

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

-- | Every bounded preorder admits a pair of connections with a single-object preorder.
--
-- >>> upperR (bounded @Ordering) ()
-- LT
-- >>> lowerL (bounded @Ordering) ()
-- GT
-- 
bounded :: Bounded a => Conn k () a
bounded = Conn (const top) (const ()) (const bottom)

infixr 3 \|/

-- | A preorder variant of 'Control.Arrow.|||'.
--
(\|/) :: Conn k c a -> Conn k c b -> Conn k c (Either a b)
f \|/ g = joined >>> f `choice` g

infixr 4 /|\

-- | A preorder variant of 'Control.Arrow.&&&'.
--
(/|\) :: Lattice c => Conn k a c -> Conn k b c -> Conn k (a, b) c
f /|\ g = f `strong` g >>> forked

joined :: Conn k a (Either a a)
joined = Conn Left (either id id) Right

forked :: Lattice a => Conn k (a, a) a
forked = Conn (uncurry (\/)) (\x -> (x,x)) (uncurry (/\))

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
fmapped :: Functor f => Conn k a b -> Conn k (f a) (f b)
fmapped (Conn f g h) = Conn (fmap f) (fmap g) (fmap h)

{-

forked :: Lattice a => Conn k (a, a) a
forked = Conn (uncurry (\/) &&& uncurry (/\)) (\x -> (x,x))

joined :: Conn k a (Either a a)
joined = Conn (Left &&& Right) (either id id)


-- |
--
-- > (strong id) (ab >>> cd) = (strong id) ab >>> (strong id) cd
-- > (flip strong id) (ab >>> cd) = (flip strong id) ab >>> (flip strong id) cd
--
strong :: Conn k a b -> Conn k c d -> Conn k (a, c) (b, d)
strong (Conn_ ab ba) (Conn_ cd dc) = Conn_ f g where
  f = bimap (fst.ab) (fst.cd) &&& bimap (snd.ab) (snd.cd)
  g = bimap ba dc

-- |
--
-- > (choice id) (ab >>> cd) = (choice id) ab >>> (choice id) cd
-- > (flip choice id) (ab >>> cd) = (flip choice id) ab >>> (flip choice id) cd
--
choice :: Conn k a b -> Conn k c d -> Conn k (Either a c) (Either b d)
choice (Conn_ ab ba) (Conn_ cd dc) = Conn_ f g where
  f = either (Left . fst.ab) (Right . fst.cd) &&& either (Left . snd.ab) (Right . snd.cd)
  g = either (Left . ba) (Right . dc)

fmapped :: Functor f => Conn k a b -> Conn k (f a) (f b)
fmapped (Conn_ f g) = Conn_ (fmap (fst.f) &&& fmap (snd.f)) (fmap g)
-}

{-
-- | Lift two 'Conn's into a 'Conn' on the <https://en.wikibooks.org/wiki/Category_Theory/Categories_of_ordered_sets coproduct order>
--
-- > (choice id) (ab >>> cd) = (choice id) ab >>> (choice id) cd
-- > (flip choice id) (ab >>> cd) = (flip choice id) ab >>> (flip choice id) cd
--
choice :: Trip a b -> Trip c d -> Conn k (Either a c) (Either b d)
choice (Conn ab ba ab') (Conn cd dc cd') = Conn f g h where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)
  h = either (Left . ab') (Right . cd')

-- | Lift two 'Conn's into a 'Conn' on the <https://en.wikibooks.org/wiki/Order_Theory/Preordered_classes_and_poclasses#product_order product order>
--
-- > (strong id) (ab >>> cd) = (strong id) ab >>> (strong id) cd
-- > (flip strong id) (ab >>> cd) = (flip strong id) ab >>> (flip strong id) cd
--
strong :: Trip a b -> Trip c d -> Conn k (a, c) (b, d)
strong (Conn ab ba ab') (Conn cd dc cd') = Conn f g h where
  f = bimap ab cd 
  g = bimap ba dc
  h = bimap ab' cd'

-- | Lift a 'Conn' into a functor.
--

-- | Lift a 'Conn' into a functor.
--
fmapped :: Functor f => Conn k a b -> Conn k (f a) (f b)
fmapped (Conn f g h) = Conn (fmap f) (fmap g) (fmap h)
-}

{-

instance LowerBounded a => Connection () a where
  connection = Conn (const bottom) (const ())

instance UpperBounded a => Connection a () where
  connection = Conn (const ()) (const top)

liftl :: Bounded b => Conn k (Maybe a) (Either a b)
liftl = Conn k f g h where
  f = maybe (Right bottom) Left
  g = either Just (const Nothing)
  h = maybe (Right top) Left

liftr :: Bounded a => Conn k (Maybe b) (Either a b)
liftr = Conn k f g h where
  f = maybe (Left bottom) Right
  g = either (const Nothing) Just
  h = maybe (Left top) Right

-}
