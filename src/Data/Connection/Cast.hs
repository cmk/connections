{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Connection.Cast (
    -- * Cast
    Side (..),
    Cast (),
    (>>>),
    (<<<),
    mapped,
    choice,
    select,
    strong,
    divide,
    bounded,
    ordered,
    identity,

    -- * Cast 'L
    pattern CastL,
    swapL,
    upper,
    upper1,
    upper2,
    ceiling,
    ceiling1,
    ceiling2,
    maximize,

    -- * Cast 'R
    pattern CastR,
    swapR,
    lower,
    lower1,
    lower2,
    floor,
    floor1,
    floor2,
    minimize,

    -- * Cast k
    pattern Cast,
    inner,
    outer,
    half,
    midpoint,
    round,
    round1,
    round2,
    truncate,
    truncate1,
    truncate2,
    median,

    -- * Down
    upL,
    upR,
    downL,
    downR,
    filterL,
    filterR,

    -- * Extended
    Lifted,
    Lowered,
    Extended (..),
    extended,
    extend,
) where

import safe Control.Arrow ((&&&))
import safe Control.Category (Category, (<<<), (>>>))
import safe qualified Control.Category as C
import safe Data.Bifunctor (bimap)
import safe Data.ExtendedReal
import safe Data.Order
import safe Data.Order.Syntax
import safe Prelude hiding (Ord (..), ceiling, floor, round, truncate)

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Int
-- >>> import Data.Ord (Down(..))
-- >>> import Data.Ratio ((%))
-- >>> import GHC.Real (Ratio(..))
-- >>> :load Data.Connection

-- | A data kind distinguishing links in a < https://ncatlab.org/nlab/show/adjoint+string chain > of Galois connections of length 2 or 3.
--
-- * /L/-tagged types are increasing (e.g. 'Data.Connection.Cast.ceiling', 'Data.Connection.Cast.maximize')
--
-- * /R/-tagged types are decreasing (e.g. 'Data.Connection.Cast.floor', 'Data.Connection.Cast.minimize')
--
--  If a connection is existentialized over this value (i.e. has type /forall k. Cast k a b/) then it can
--  provide either of two functions /f, h :: a -> b/.
--
--  This is useful because it enables rounding, truncation, medians, etc. 
--
data Side = L | R

-- | A < https://ncatlab.org/nlab/show/adjoint+string chain > of Galois connections of length 2 or 3.
--
-- Connections have many nice properties wrt numerical conversion:
--
-- >>> inner ratf32 (1 / 8)    -- eighths are exactly representable in a float
-- 1 % 8
-- >>> outer ratf32 (1 % 8)
-- (0.125,0.125)
-- >>> inner ratf32 (1 / 7)    -- sevenths are not
-- 9586981 % 67108864
-- >>> outer ratf32 (1 % 7)
-- (0.14285713,0.14285715)
--
-- Another example avoiding loss-of-precision:
--
-- >>> f x y = (x + y) - x
-- >>> maxOdd32 = 1.6777215e7
-- >>> f maxOdd32 2.0 :: Float
-- 1.0
-- >>> round2 f64f32 f maxOdd32 2.0
-- 2.0
data Cast (k :: Side) a b = Cast_ (a -> (b, b)) (b -> a)

instance Category (Cast k) where
    id = identity
    {-# INLINE id #-}

    Cast_ f1 g1 . Cast_ f2 g2 = Cast_ ((fst . f1) . (fst . f2) &&& (snd . f1) . (snd . f2)) (g2 . g1)
    {-# INLINE (.) #-}

-- Internal floor function. When \(f \dashv g \dashv h \) this is h.
_1 :: Cast k a b -> a -> b
_1 (Cast_ f _) = fst . f
{-# INLINE _1 #-}

-- Internal ceiling function. When \(f \dashv g \dashv h \) this is f.
_2 :: Cast k a b -> a -> b
_2 (Cast_ f _) = snd . f
{-# INLINE _2 #-}

-- | Lift a 'Cast' into a functor.
--
-- /Caution/: This function will result in an invalid connection
-- if the functor alters the internal preorder (e.g. 'Data.Ord.Down').
mapped :: Functor f => Cast k a b -> Cast k (f a) (f b)
mapped (Cast f g h) = Cast (fmap f) (fmap g) (fmap h)
{-# INLINE mapped #-}

-- | Lift two connections into a connection on the <https://en.wikibooks.org/wiki/Category_Theory/Categories_of_ordered_sets coproduct order>
--
-- > (choice id) (ab >>> cd) = (choice id) ab >>> (choice id) cd
-- > (flip choice id) (ab >>> cd) = (flip choice id) ab >>> (flip choice id) cd
choice :: Cast k a b -> Cast k c d -> Cast k (Either a c) (Either b d)
choice (Cast ab ba ab') (Cast cd dc cd') = Cast f g h
  where
    f = either (Left . ab) (Right . cd)
    g = either (Left . ba) (Right . dc)
    h = either (Left . ab') (Right . cd')
{-# INLINE choice #-}

infixr 3 `select`

-- | Lift two connections into a connection on the <https://en.wikibooks.org/wiki/Category_Theory/Categories_of_ordered_sets coproduct order>
select :: Cast k c a -> Cast k c b -> Cast k c (Either a b)
select f g = Cast Left (either id id) Right >>> f `choice` g

-- | Lift two connections into a connection on the <https://en.wikibooks.org/wiki/Order_Theory/Preordered_classes_and_poclasses#product_order product order>
--
-- > (strong id) (ab >>> cd) = (strong id) ab >>> (strong id) cd
-- > (flip strong id) (ab >>> cd) = (flip strong id) ab >>> (flip strong id) cd
strong :: Cast k a b -> Cast k c d -> Cast k (a, c) (b, d)
strong (Cast ab ba ab') (Cast cd dc cd') = Cast f g h
  where
    f = bimap ab cd
    g = bimap ba dc
    h = bimap ab' cd'
{-# INLINE strong #-}

infixr 4 `divide`

-- | Lift two connections into a connection on the <https://en.wikibooks.org/wiki/Order_Theory/Preordered_classes_and_poclasses#product_order product order>
divide :: Total c => Cast k a c -> Cast k b c -> Cast k (a, b) c
divide f g = f `strong` g >>> ordered
{-# INLINE divide #-}

-- | The defining connections of a bounded preorder.
bounded :: Bounded a => Cast k () a
bounded = Cast (const minBound) (const ()) (const maxBound)
{-# INLINE bounded #-}

-- | The defining connections of a total order.
--
-- >>> outer ordered (True, False)
-- (False,True)
ordered :: Total a => Cast k (a, a) a
ordered = Cast (uncurry max) (id &&& id) (uncurry min)
{-# INLINE ordered #-}

-- | The identity connection.
identity :: Cast k a a
identity = Cast_ (id &&& id) id
{-# INLINE identity #-}

---------------------------------------------------------------------
-- Cast 'L
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
-- /Caution/: /CastL f g/ must obey \(f \dashv g \). This condition is not checked.
--
-- For further information see 'Data.Connection.Property'.
pattern CastL :: (a -> b) -> (b -> a) -> Cast 'L a b
pattern CastL f g <- (_2 &&& upper -> (f, g)) where CastL f g = Cast_ (f &&& f) g

{-# COMPLETE CastL #-}

-- | Witness to the mirror symmetry between 'CastL' and 'CastR'.
--
-- > swapL . swapR = id
-- > swapR . swapL = id
swapL :: Cast 'R a b -> Cast 'L b a
swapL (CastR f g) = CastL f g
{-# INLINE swapL #-}

-- | Extract the upper adjoint of a 'Cast'.
upper :: Cast 'L a b -> b -> a
upper = inner
{-# INLINE upper #-}

-- | Map over a 'Cast' from the right.
--
-- This is the unit of the resulting monad:
--
-- > x <~ upper1 c id x
--
-- >>> compare pi $ upper1 f64f32 id pi
-- LT
upper1 :: Cast 'L a b -> (b -> b) -> a -> a
upper1 (CastL f g) h a = g $ h (f a)
{-# INLINE upper1 #-}

-- | Zip over a 'Cast' from the right.
upper2 :: Cast 'L a b -> (b -> b -> b) -> a -> a -> a
upper2 (CastL f g) h a1 a2 = g $ h (f a1) (f a2)
{-# INLINE upper2 #-}

-- | Extract the lower half of a 'Cast'.
--
-- > ceiling identity = id
-- > ceiling c (x \/ y) = ceiling c x \/ ceiling c y
--
-- The latter law is the adjoint functor theorem for preorders.
--
-- >>> Data.Connection.ceiling ratf32 (0 :% 0)
-- NaN
-- >>> Data.Connection.ceiling ratf32 (13 :% 10)
-- 1.3000001
-- >>> Data.Connection.ceiling f64f32 pi
-- 3.1415927
ceiling :: Cast 'L a b -> a -> b
ceiling (CastL f _) = f
{-# INLINE ceiling #-}

-- | Map over a 'Cast' from the left.
--
-- > ceiling1 identity = id
--
-- This is the counit of the resulting comonad:
--
-- > x >~ ceiling1 c id x
--
ceiling1 :: Cast 'L a b -> (a -> a) -> b -> b
ceiling1 (CastL f g) h b = f $ h (g b)
{-# INLINE ceiling1 #-}

-- | Zip over a 'Cast' from the left.
ceiling2 :: Cast 'L a b -> (a -> a -> a) -> b -> b -> b
ceiling2 (CastL f g) h b1 b2 = f $ h (g b1) (g b2)
{-# INLINE ceiling2 #-}

-- | Generalized maximum.
maximize :: Cast 'L (a, b) c -> a -> b -> c
maximize = curry . ceiling
{-# INLINE maximize #-}

---------------------------------------------------------------------
-- Cast 'R
---------------------------------------------------------------------

-- | A Galois connection between two monotone functions.
--
-- 'CastR' is the mirror image of 'CastL'.
--
-- If you only require one connection there is no particular reason to
-- use one version over the other. However many use cases (e.g. rounding)
-- require an adjoint triple of connections that can lower into a standard
-- connection in either of two ways.
--
-- /Caution/: /CastR f g/ must obey \(f \dashv g \). This condition is not checked.
--
-- For further information see 'Data.Connection.Property'.
pattern CastR :: (b -> a) -> (a -> b) -> Cast 'R a b
pattern CastR f g <- (lower &&& _1 -> (f, g)) where CastR f g = Cast_ (g &&& g) f

{-# COMPLETE CastR #-}

-- | Witness to the mirror symmetry between 'CastL' and 'CastR'.
--
-- > swapL . swapR = id
-- > swapR . swapL = id
swapR :: Cast 'L a b -> Cast 'R b a
swapR (CastL f g) = CastR f g
{-# INLINE swapR #-}

-- | Extract the lower adjoint of a 'Cast'.
lower :: Cast 'R a b -> b -> a
lower = inner
{-# INLINE lower #-}

-- | Map over a 'Cast' from the left.
--
-- This is the counit of the resulting comonad:
--
-- > x >~ lower1 c id x
--
-- >>> compare pi $ lower1 f64f32 id pi
-- GT
lower1 :: Cast 'R a b -> (b -> b) -> a -> a
lower1 (CastR f g) h a = f $ h (g a)
{-# INLINE lower1 #-}

-- | Zip over a 'Cast' from the left.
lower2 :: Cast 'R a b -> (b -> b -> b) -> a -> a -> a
lower2 (CastR f g) h a1 a2 = f $ h (g a1) (g a2)
{-# INLINE lower2 #-}

-- | Extract the upper half of a 'Cast'
--
-- > floor identity = id
-- > floor c (x /\ y) = floor c x /\ floor c y
--
-- The latter law is the adjoint functor theorem for preorders.
--
-- >>> Data.Connection.floor ratf32 (0 :% 0)
-- NaN
-- >>> Data.Connection.floor ratf32 (13 :% 10)
-- 1.3
-- >>> Data.Connection.floor f64f32 pi
-- 3.1415925
floor :: Cast 'R a b -> a -> b
floor (CastR _ g) = g
{-# INLINE floor #-}

-- | Map over a 'Cast' from the right.
--
-- > floor1 identity = id
--
-- This is the unit of the resulting monad:
--
-- > x <~ floor1 c id x
--
floor1 :: Cast 'R a b -> (a -> a) -> b -> b
floor1 (CastR f g) h b = g $ h (f b)
{-# INLINE floor1 #-}

-- | Zip over a 'Cast' from the right.
floor2 :: Cast 'R a b -> (a -> a -> a) -> b -> b -> b
floor2 (CastR f g) h b1 b2 = g $ h (f b1) (f b2)
{-# INLINE floor2 #-}

-- | Generalized minimum.
minimize :: Cast 'R (a, b) c -> a -> b -> c
minimize = curry . floor
{-# INLINE minimize #-}

---------------------------------------------------------------------
-- Cast k
---------------------------------------------------------------------

-- | An <https://ncatlab.org/nlab/show/adjoint+triple adjoint triple> of Galois connections.
--
-- An adjoint triple is a chain of connections of length 3:
--
-- \(f \dashv g \dashv h \)
--
-- When applied to a 'CastL' or 'CastR', the two functions of type @a -> b@ returned will be identical.
--
-- /Caution/: /Cast f g h/ must obey \(f \dashv g \dashv h\). This condition is not checked.
--
-- For detailed properties see 'Data.Connection.Property'.
pattern Cast :: (a -> b) -> (b -> a) -> (a -> b) -> Cast k a b
pattern Cast f g h <- (inner &&& _1 &&& _2 -> (g, (h, f))) where Cast f g h = Cast_ (h &&& f) g

{-# COMPLETE Cast #-}

-- | Extract the upper adjoint of a 'CastL', or lower adjoint of a 'CastR'.
--
-- When the connection is an adjoint triple the inner function is returned:
--
-- >>> inner ratf32 (1 / 8)    -- eighths are exactly representable in a float
-- 1 % 8
-- >>> inner ratf32 (1 / 7)    -- sevenths are not
-- 9586981 % 67108864
inner :: Cast k a b -> b -> a
inner (Cast_ _ g) = g
{-# INLINE inner #-}

-- | Extract the left and/or right adjoints of a connection.
--
-- When the connection is an adjoint triple the outer functions are returned:
--
-- > outer c = floor c &&& ceiling c
--
-- >>> outer ratf32 (1 % 8)    -- eighths are exactly representable in a float
-- (0.125,0.125)
-- >>> outer ratf32 (1 % 7)    -- sevenths are not
-- (0.14285713,0.14285715)
outer :: Cast k a b -> a -> (b, b)
outer (Cast_ f _) = f
{-# INLINE outer #-}

-- | Determine which half of the interval between 2 representations of /a/ a particular value lies.
--
-- @ 'half' c x = 'pcompare' (x - 'lower1' c 'id' x) ('upper1' c 'id' x - x) @
--
-- >>> maybe False (== EQ) $ half f64f32 (midpoint f64f32 pi)
-- True
half :: (Num a, Preorder a) => (forall k. Cast k a b) -> a -> Maybe Ordering
half c x = pcompare (x - lower1 c id x) (upper1 c id x - x)
{-# INLINE half #-}

-- | Return the midpoint of the interval containing x.
--
-- >>> pi - midpoint f64f32 pi
-- 3.1786509424591713e-8
midpoint :: Fractional a => (forall k. Cast k a b) -> a -> a
midpoint c x = lower1 c id x / 2 + upper1 c id x / 2
{-# INLINE midpoint #-}

-- | Return the nearest value to x.
--
-- > round identity = id
--
-- If x lies halfway between two finite values, then return the value
-- with the smaller absolute value (i.e. round towards from zero).
--
-- See <https://en.wikipedia.org/wiki/Rounding>.
round :: (Num a, Preorder a) => (forall k. Cast k a b) -> a -> b
round c x = case half c x of
    Just GT -> ceiling c x
    Just LT -> floor c x
    _ -> truncate c x
{-# INLINE round #-}

-- | Lift a unary function over an adjoint triple.
--
-- > round1 identity = id
--
-- Results are rounded to the nearest value with ties away from 0.
round1 :: (Num a, Preorder a) => (forall k. Cast k a b) -> (a -> a) -> b -> b
round1 c f x = round c $ f (inner c x)
{-# INLINE round1 #-}

-- | Lift a binary function over an adjoint triple.
--
-- > round2 identity = id
--
-- Results are rounded to the nearest value with ties away from 0.
--
-- Example avoiding loss-of-precision:
--
-- >>> f x y = (x + y) - x
-- >>> maxOdd32 = 1.6777215e7
-- >>> f maxOdd32 2.0 :: Float
-- 1.0
-- >>> round2 ratf32 f maxOdd32 2.0
-- 2.0
round2 :: (Num a, Preorder a) => (forall k. Cast k a b) -> (a -> a -> a) -> b -> b -> b
round2 c f x y = round c $ f (inner c x) (inner c y)
{-# INLINE round2 #-}

-- | Truncate towards zero.
--
-- > truncate identity = id
truncate :: (Num a, Preorder a) => (forall k. Cast k a b) -> a -> b
truncate c x = if x >~ 0 then floor c x else ceiling c x
{-# INLINE truncate #-}

-- | Lift a unary function over an adjoint triple.
--
-- > truncate1 identity = id
--
-- Results are truncated towards zero.
truncate1 :: (Num a, Preorder a) => (forall k. Cast k a b) -> (a -> a) -> b -> b
truncate1 c f x = truncate c $ f (inner c x)
{-# INLINE truncate1 #-}

-- | Lift a binary function over an adjoint triple.
--
-- > truncate2 identity = id
--
-- Results are truncated towards zero.
truncate2 :: (Num a, Preorder a) => (forall k. Cast k a b) -> (a -> a -> a) -> b -> b -> b
truncate2 c f x y = truncate c $ f (inner c x) (inner c y)
{-# INLINE truncate2 #-}

-- | Birkoff's < https://en.wikipedia.org/wiki/Median_algebra median > operator.
--
-- > median x x y = x
-- > median x y z = median z x y
-- > median x y z = median x z y
-- > median (median x w y) w z = median x w (median y w z)
--
-- >>> median f32f32 1.0 9.0 7.0
-- 7.0
-- >>> median f32f32 1.0 9.0 (0.0 / 0.0)
-- 9.0
median :: (forall k. Cast k (a, a) a) -> a -> a -> a -> a
median c x y z = (x `join` y) `meet` (y `join` z) `meet` (z `join` x)
  where
    join = maximize c
    meet = minimize c
{-# INLINE median #-}

---------------------------------------------------------------------
-- Down
---------------------------------------------------------------------

-- | Invert a 'Cast'.
--
-- > upL . downL = downL . upL = id
upL :: Cast 'L (Down a) (Down b) -> Cast 'L b a
upL (CastL f g) = CastL g' f'
  where
    f' x = let (Down y) = f (Down x) in y
    g' x = let (Down y) = g (Down x) in y
{-# INLINE upL #-}

-- | Invert a 'Cast'.
--
-- > upR . downR = downR . upR = id
upR :: Cast 'R (Down a) (Down b) -> Cast 'R b a
upR (CastR f g) = CastR g' f'
  where
    f' x = let (Down y) = f (Down x) in y
    g' x = let (Down y) = g (Down x) in y
{-# INLINE upR #-}

-- | Invert a 'Cast'.
--
-- >>> let counit = upper1 (downL $ bounded @Ordering) id
-- >>> counit (Down LT)
-- Down LT
-- >>> counit (Down GT)
-- Down LT
downL :: Cast 'L a b -> Cast 'L (Down b) (Down a)
downL (CastL f g) = CastL (\(Down x) -> Down $ g x) (\(Down x) -> Down $ f x)
{-# INLINE downL #-}

-- | Invert a 'Cast'.
--
-- >>> let unit = lower1 (downR $ bounded @Ordering) id
-- >>> unit (Down LT)
-- Down GT
-- >>> unit (Down GT)
-- Down GT
downR :: Cast 'R a b -> Cast 'R (Down b) (Down a)
downR (CastR f g) = CastR (\(Down x) -> Down $ g x) (\(Down x) -> Down $ f x)
{-# INLINE downR #-}

-- | Obtain the principal filter in /B/ generated by an element of /A/.
--
-- A subset /B/ of a lattice is an filter if and only if it is an upper set
-- that is closed under finite meets, i.e., it is nonempty and for all
-- /x/, /y/ in /B/, the element @meet c x y@ is also in /b/.
--
-- /filterL/ and /filterR/ commute with /Down/:
--
-- > filterL c a b <=> filterR c (Down a) (Down b)
--
-- > filterL c (Down a) (Down b) <=> filterR c a b
--
-- /filterL c a/ is upward-closed for all /a/:
--
-- > a <= b1 && b1 <= b2 => a <= b2
-- > a1 <= b && a2 <= b => minimize c (ceiling c a1) (ceiling c a2) <= b
--
-- See <https://en.wikipedia.org/wiki/Filter_(mathematics)>
filterL :: Preorder b => Cast 'L a b -> a -> b -> Bool
filterL c a b = ceiling c a <~ b
{-# INLINE filterL #-}

-- | Obtain the principal ideal in /B/ generated by an element of /A/.
--
-- A subset /B/ of a lattice is an ideal if and only if it is a lower set
-- that is closed under finite joins, i.e., it is nonempty and for all
-- /x/, /y/ in /B/, the element /join c x y/ is also in /B/.
--
-- /filterR c a/ is downward-closed for all /a/:
--
-- > a >= b1 && b1 >= b2 => a >= b2
--
-- > a1 >= b && a2 >= b => maximize c (floor c a1) (floor c a2) >= b
--
-- See <https://en.wikipedia.org/wiki/Ideal_(order_theory)>
filterR :: Preorder b => Cast 'R a b -> a -> b -> Bool
filterR c a b = b <~ floor c a
{-# INLINE filterR #-}

---------------------------------------------------------------------
-- Extended
---------------------------------------------------------------------

type Lifted = Either ()

type Lowered a = Either a ()

-- | Eliminate an 'Extended'.
{-# INLINE extended #-}
extended :: b -> b -> (a -> b) -> Extended a -> b
extended b _ _ NegInf = b
extended _ t _ PosInf = t
extended _ _ f (Finite x) = f x

{-# INLINE extend #-}
extend :: (a -> Bool) -> (a -> Bool) -> (a -> b) -> a -> Extended b
extend p q f = g
  where
    g i
        | p i = NegInf
        | q i = PosInf
        | otherwise = Finite $ f i
