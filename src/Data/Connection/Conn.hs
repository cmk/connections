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
    Kan(..)
  -- * Conn
  , Conn()
  , pattern Conn
  , (>>>)
  , (<<<)
  , embed
  , range
  , identity
  -- * Connection k
  , type ConnK
  , half
  , midpoint
  , roundWith
  , roundWith1
  , roundWith2
  , truncateWith
  , truncateWith1
  , truncateWith2
  -- * Connection L
  , type ConnL
  , pattern ConnL
  , swapL
  , counit
  , upper
  , upper1
  , upper2
  , filterWith
  , ceilingWith
  , ceilingWith1
  , ceilingWith2
  -- * Connection R
  , type ConnR
  , pattern ConnR
  , swapR
  , unit
  , lower
  , lower1
  , lower2
  , idealWith
  , floorWith
  , floorWith1
  , floorWith2
  -- * Combinators
  , choice
  , strong
  , set
  , intSet
  --, map
  --, intMap
  -- * Down
  , upL
  , downL
  , upR
  , downR
) where

import safe Control.Arrow
import safe Control.Category (Category, (>>>), (<<<))
import safe Data.Bifunctor (bimap)
import safe Data.Order
import safe Prelude hiding (Ord(..))
import safe qualified Control.Category as C
import safe Data.Set (Set)
import safe Data.IntSet (IntSet)
import safe qualified Data.Set as Set
import safe qualified Data.IntSet as IntSet

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Int
-- >>> import Prelude hiding (Ord(..), Bounded, fromInteger, fromRational, RealFrac(..))
-- >>> import qualified Prelude as P
-- >>> :load Data.Connection


-- | A data kind distinguishing the chirality of a Kan extension.
--
-- Here it serves to distinguish the directionality of a preorder:
--
-- * /L/-tagged types are 'upwards-directed' (e.g. 'minimal', 'upper', 'ceiling', 'join')
--
-- * /R/-tagged types are 'downwards-directed' (e.g. 'maximal', 'lower', 'floor', 'meet')
--
data Kan = L | R

-- | An < https://ncatlab.org/nlab/show/adjoint+string adjoint string > of Galois connections of length 2 or 3.
--
data Conn (k :: Kan) a b = Conn_ (a -> (b , b)) (b -> a)

-- | Obtain a /Conn/ from an adjoint triple of monotone functions.
--
--  This is a view pattern for an arbitrary 'Conn'. When applied to a 'ConnL'
--  or 'ConnR', the two functions of type @a -> b@ returned will be identical.
--
--  /Caution/: /Conn f g h/ must obey \(f \dashv g \dashv h\). This condition is not checked.
--
--  For detailed properties see 'Data.Connection.Property'.
--
pattern Conn :: (a -> b) -> (b -> a) -> (a -> b) -> Conn k a b
pattern Conn f g h <- (embed &&& _1 &&& _2 -> (g, (h, f))) where Conn f g h = Conn_ (h &&& f) g
{-# COMPLETE Conn #-}

-- Internal floor function. When \(f \dashv g \dashv h \) this is h.
_1 :: Conn k a b -> a -> b
_1 (Conn_ f _) = fst . f

-- Internal ceiling function. When \(f \dashv g \dashv h \) this is f.
_2 :: Conn k a b -> a -> b
_2 (Conn_ f _) = snd . f

-- | Obtain the center of a /ConnK/, upper half of a /ConnL/, or the lower half of a /ConnR/.
--
embed :: Conn k a b -> b -> a
embed (Conn_ _ g) = g

-- | Obtain the lower and upper functions from a 'ConnK'.
--
-- > range c = floorWith c &&& ceilingWith c
--
-- >>> range f64f32 pi
-- (3.1415925,3.1415927)
-- >>> range f64f32 (0/0)
-- (NaN,NaN)
--
range :: Conn k a b -> a -> (b, b)
range (Conn_ f _) = f

-- | The identity 'Conn'.
--
identity :: Conn k a a
identity = Conn_ (id &&& id) id

instance Category (Conn k) where
  id = identity

  Conn_ f1 g1 . Conn_ f2 g2 = Conn_ ((fst.f1).(fst.f2) &&& (snd.f1).(snd.f2)) (g2 . g1)

---------------------------------------------------------------------
-- ConnK
---------------------------------------------------------------------

-- | An <https://ncatlab.org/nlab/show/adjoint+triple adjoint triple> of Galois connections.
--
-- An adjoint triple is a chain of connections of length 3:
--
-- \(f \dashv g \dashv h \) 
--
-- For detailed properties see 'Data.Connection.Property'.
--
type ConnK a b = forall k. Conn k a b

-- | Determine which half of the interval between 2 representations of /a/ a particular value lies.
-- 
-- @ 'half' t x = 'pcompare' (x - 'lower' t x) ('upper' t x - x) @
--
half :: (Num a, Preorder a) => ConnK a b -> a -> Maybe Ordering
half t x = pcompare (x - lower t x) (upper t x - x) 

-- | Return the midpoint of the interval containing x.
--
-- >>> midpoint f32i08 4.3
-- 4.5
-- >>> midpoint f64i08 4.3
-- 4.5
-- >>> pi - midpoint f64f32 pi
-- 3.1786509424591713e-8
--
-- >>> maybe False (~~ EQ) $ half f64f32 (midpoint f64f32 pi)
-- True
--
midpoint :: Fractional a => ConnK a b -> a -> a
midpoint t x = lower t x / 2 + upper t x / 2

-- | Return the nearest value to x.
--
-- > roundWith identity = id
-- 
-- If x lies halfway between two finite values, then return the value
-- with the larger absolute value (i.e. round away from zero).
--
-- See <https://en.wikipedia.org/wiki/Rounding>.
--
roundWith :: forall a b. (Num a, Preorder a) => ConnK a b -> a -> b
roundWith c x = case pcompare halfR halfL of
  Just GT -> ceilingWith c x
  Just LT -> floorWith c x
  _       -> truncateWith c x

  where
    halfR = x - lower c x -- dist from lower bound

    halfL = upper c x - x -- dist from upper bound

-- | Lift a unary function over a 'ConnK'.
--
-- Results are rounded to the nearest value with ties away from 0.
--
roundWith1 :: (Num a, Preorder a) => ConnK a b -> (a -> a) -> b -> b
roundWith1 c f x = roundWith c $ f (g x) where Conn _ g _ = c
{-# INLINE roundWith1 #-}

-- | Lift a binary function over a 'ConnK'.
--
-- Results are rounded to the nearest value with ties away from 0.
--
-- >>> f x y = (x + y) - x 
-- >>> maxOdd32 = 1.6777215e7
-- >>> maxOdd64 = 9.007199254740991e15
-- >>> f maxOdd32 2.0 :: Float
-- 1.0
-- >>> round2 @Rational @Float f maxOdd32 2.0
-- 2.0
-- >>> f maxOdd64 2.0 :: Double
-- 1.0
-- >>> round2 @Rational @Double f maxOdd64 2.0
-- 2.0
--
roundWith2 :: (Num a, Preorder a) => ConnK a b -> (a -> a -> a) -> b -> b -> b
roundWith2 c f x y = roundWith c $ f (g x) (g y) where Conn _ g _ = c
{-# INLINE roundWith2 #-}

-- | Truncate towards zero.
--
-- > truncateWith identity = id
--
truncateWith :: (Num a, Preorder a) => ConnK a b -> a -> b
truncateWith c x = if x >~ 0 then floorWith c x else ceilingWith c x

-- | Lift a unary function over a 'ConnK'.
--
-- Results are truncated towards zero.
--
-- > truncateWith identity = id
--
truncateWith1 :: (Num a, Preorder a) => ConnK a b -> (a -> a) -> b -> b
truncateWith1 c f x = truncateWith c $ f (g x) where Conn _ g _ = c
{-# INLINE truncateWith1 #-}

truncateWith2 :: (Num a, Preorder a) => ConnK a b -> (a -> a -> a) -> b -> b -> b
truncateWith2 c f x y = truncateWith c $ f (g x) (g y) where Conn _ g _ = c
{-# INLINE truncateWith2 #-}

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

-- | Reverse round trip through a 'ConnK' or 'ConnL'.
--
-- > x >~ counit c x
--
-- >>> counit (conn @_ @() @Ordering) LT
-- LT
-- >>> counit (conn @_ @() @Ordering) GT
-- LT
--
counit :: ConnL a b -> b -> b
counit c = ceilingWith1 c id

-- | Round trip through a 'ConnK' or 'ConnL'.
--
-- > upper c = upper1 c id = embed c . ceilingWith c
-- > x <= upper c x
-- 
-- >>> compare pi $ upper f64f32 pi
-- LT
--
upper :: ConnL a b -> a -> a
upper c = upper1 c id

-- | Map over a 'ConnK' or 'ConnL' from the right.
--
upper1 :: ConnL a b -> (b -> b) -> a -> a
upper1 (ConnL f g) h a = g $ h (f a)

-- | Zip over a 'ConnK' or 'ConnL' from the right.
--
upper2 :: ConnL a b -> (b -> b -> b) -> a -> a -> a
upper2 (ConnL f g) h a1 a2 = g $ h (f a1) (f a2)

-- | Obtain the principal filter in /B/ generated by an element of /A/.
--
-- A subset /B/ of a lattice is an filter if and only if it is an upper set 
-- that is closed under finite meets, i.e., it is nonempty and for all 
-- /x/, /y/ in /B/, the element @x `meet` y@ is also in /b/.
--
-- /filterWith/ and /idealWith/ commute with /Down/:
--
-- > filterWith c a b <=> idealWith c (Down a) (Down b)
--
-- > filterWith c (Down a) (Down b) <=> idealWith c a b
--
-- /filterWith c a/ is upward-closed for all /a/:
--
-- > a <= b1 && b1 <= b2 => a <= b2
--
-- > a1 <= b && inf a2 <= b => ceiling a1 `meet` ceiling a2 <= b
--
-- See <https://en.wikipedia.org/wiki/Filter_(mathematics)>
--
filterWith :: Preorder b => ConnL a b -> a -> b -> Bool
filterWith c a b = ceilingWith c a <~ b

-- | Extract the left half of a 'ConnK' or 'ConnL'.
--
--
-- >>> floorWith f64f32 pi
-- 3.1415925
-- >>> ceilingWith f64f32 pi
-- 3.1415927
--
ceilingWith :: ConnL a b -> a -> b
ceilingWith (ConnL f _) = f

-- | Map over a 'ConnK' or 'ConnL' from the left.
--
ceilingWith1 :: ConnL a b -> (a -> a) -> b -> b
ceilingWith1 (ConnL f g) h b = f $ h (g b)

-- | Zip over a 'ConnK' or 'ConnL' from the left.
--
ceilingWith2 :: ConnL a b -> (a -> a -> a) -> b -> b -> b
ceilingWith2 (ConnL f g) h b1 b2 = f $ h (g b1) (g b2)

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
-- of connections (i.e. a 'ConnK') that can lower into a standard
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

-- | Witness to the symmetry between 'ConnL' and 'ConnR'.
--
-- > swapL . swapR = id
-- > swapR . swapL = id
--
swapR :: ConnL a b -> ConnR b a
swapR (ConnL f g) = ConnR f g

-- | Round trip through a 'ConnK' or 'ConnR'.
--
-- > x <~ unit c x
-- > unit c = floorWith1 c id = floorWith c . embed c
--
-- >>> unit (conn @_ @() @Ordering) LT
-- GT
-- >>> unit (conn @_ @() @Ordering) GT
-- GT
--
unit :: ConnR a b -> b -> b
unit c = floorWith1 c id

-- | Reverse round trip through a 'ConnK' or 'ConnR'.
--
-- > x >~ lower c x
--
-- >>> compare pi $ lower f64f32 pi
-- GT
--
lower :: ConnR a b -> a -> a
lower c = lower1 c id

-- | Map over a 'ConnK' or 'ConnR' from the left.
--
lower1 :: ConnR a b -> (b -> b) -> a -> a
lower1 (ConnR f g) h a = f $ h (g a)

-- | Zip over a 'ConnK' or 'ConnR' from the left.
--
lower2 :: ConnR a b -> (b -> b -> b) -> a -> a -> a
lower2 (ConnR f g) h a1 a2 = f $ h (g a1) (g a2)

-- | Obtain the principal ideal in /B/ generated by an element of /A/.
--
-- A subset /B/ of a lattice is an ideal if and only if it is a lower set 
-- that is closed under finite joins, i.e., it is nonempty and for all 
-- /x/, /y/ in /B/, the element /x `join` y/ is also in /B/.
--
-- /idealWith c a/ is downward-closed for all /a/:
--
-- > a >= b1 && b1 >= b2 => a >= b2
--
-- > a1 >= b && a2 >= b => floor a1 `join` floor a2 >= b
--
-- See <https://en.wikipedia.org/wiki/Ideal_(order_theory)>
--
idealWith :: Preorder b => ConnR a b -> a -> b -> Bool
idealWith c a b = b <~ floorWith c a

-- | Extract the right half of a 'ConnK' or 'ConnR'
--
-- This is the adjoint functor theorem for preorders.
--
-- >>> floorWith f64f32 pi
-- 3.1415925
-- >>> ceilingWith f64f32 pi
-- 3.1415927
--
floorWith :: ConnR a b -> a -> b
floorWith (ConnR _ g) = g

-- | Map over a 'ConnK' or 'ConnR' from the right.
--
floorWith1 :: ConnR a b -> (a -> a) -> b -> b
floorWith1 (ConnR f g) h b = g $ h (f b)

-- | Zip over a 'ConnK' or 'ConnR' from the right.
--
floorWith2 :: ConnR a b -> (a -> a -> a) -> b -> b -> b
floorWith2 (ConnR f g) h b1 b2 = g $ h (f b1) (f b2)

---------------------------------------------------------------------
-- Combinators
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

fork :: a -> (a, a)
fork x = (x, x)

set :: Total a => Conn k (Set a, Set a) (Set a)
set = Conn (uncurry Set.union) fork (uncurry Set.intersection)

intSet :: Conn k (IntSet, IntSet) IntSet
intSet = Conn (uncurry IntSet.union) fork (uncurry IntSet.intersection)

-- | Convert an inverted 'ConnL' to a 'ConnL'.
--
-- > upL . downL = downL . upL = id
--
upL :: ConnL (Down a) (Down b) -> ConnL b a
upL (ConnL f g) = ConnL g' f' where
  f' x = let (Down y) = f (Down x) in y
  g' x = let (Down y) = g (Down x) in y

-- | Convert a 'ConnL' to an inverted 'ConnL'.
--
-- >>> upper (downL $ conn @_ @() @Ordering) (Down LT)
-- Down LT
-- >>> upper (downL $ conn @_ @() @Ordering) (Down GT)
-- Down LT
--
downL :: ConnL a b -> ConnL (Down b) (Down a)
downL (ConnL f g) = ConnL (\(Down x) -> Down $ g x) (\(Down x) -> Down $ f x)

-- | Convert an inverted 'ConnR' to a 'ConnR'.
--
-- > upR . downR = downR . upR = id
--
upR :: ConnR (Down a) (Down b) -> ConnR b a
upR (ConnR f g) = ConnR g' f' where
  f' x = let (Down y) = f (Down x) in y
  g' x = let (Down y) = g (Down x) in y

-- | Convert a 'ConnR' to an inverted 'ConnR'.
--
-- >>> lower (downR $ conn @_ @() @Ordering) (Down LT)
-- Down GT
-- >>> lower (downR $ conn @_ @() @Ordering) (Down GT)
-- Down GT
--
downR :: ConnR a b -> ConnR (Down b) (Down a)
downR (ConnR f g) = ConnR (\(Down x) -> Down $ g x) (\(Down x) -> Down $ f x)
