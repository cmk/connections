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

module Data.Connection.Conn (
    -- * Conn
    Kan (..),
    Conn (),
    (>>>),
    (<<<),
    mapped,
    choice,
    select,
    strong,
    divide,
    ordered,
    bounded,
    identity,

    -- * Connection L
    ConnL,
    pattern ConnL,
    connL,
    upper,
    upper1,
    upper2,
    ceiling,
    ceiling1,
    ceiling2,
    maximize,

    -- * Connection R
    ConnR,
    pattern ConnR,
    connR,
    lower,
    lower1,
    lower2,
    floor,
    floor1,
    floor2,
    minimize,

    -- * Connection k
    pattern Conn,
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
    Down (..),

    -- * Extended
    Lifted,
    Lowered,
    Extended(..),
    extended,
    extend
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

-- | A data kind distinguishing the directionality of a Galois connection:
--
-- * /L/-tagged types are low / increasing (e.g. 'Data.Connection.Conn.ceiling', 'Data.Connection.Conn.maximize')
--
-- * /R/-tagged types are high / decreasing (e.g. 'Data.Connection.Conn.floor', 'Data.Connection.Conn.minimize')
data Kan = L | R

-- | A (chain of) Galois connections.
--
-- A [Galois connection](https://en.wikipedia.org/wiki/Galois_connection) between preorders P and Q
-- is a pair of monotone maps /f :: p -> q/ and /g :: q -> p/ such that:
--
-- > f x <= y iff x <= g y
--
-- We say that `f` is the left or right adjoint, and `g` is the right or left adjoint of the connection.
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
--
-- See the /README/ file for a slightly more in-depth introduction.
data Conn (k :: Kan) a b = Conn_ (a -> (b, b)) (b -> a)

instance Category (Conn k) where
    id = identity
    {-# INLINE id #-}

    Conn_ f1 g1 . Conn_ f2 g2 = Conn_ ((fst . f1) . (fst . f2) &&& (snd . f1) . (snd . f2)) (g2 . g1)
    {-# INLINE (.) #-}

-- Internal floor function. When \(f \dashv g \dashv h \) this is h.
_1 :: Conn k a b -> a -> b
_1 (Conn_ f _) = fst . f
{-# INLINE _1 #-}

-- Internal ceiling function. When \(f \dashv g \dashv h \) this is f.
_2 :: Conn k a b -> a -> b
_2 (Conn_ f _) = snd . f
{-# INLINE _2 #-}

-- | Lift a 'Conn' into a functor.
--
-- /Caution/: This function will result in an invalid connection
-- if the functor alters the internal preorder (e.g. 'Data.Ord.Down').
mapped :: Functor f => Conn k a b -> Conn k (f a) (f b)
mapped (Conn f g h) = Conn (fmap f) (fmap g) (fmap h)
{-# INLINE mapped #-}

-- | Lift two 'Conn's into a 'Conn' on the <https://en.wikibooks.org/wiki/Category_Theory/Categories_of_ordered_sets coproduct order>
--
-- > (choice id) (ab >>> cd) = (choice id) ab >>> (choice id) cd
-- > (flip choice id) (ab >>> cd) = (flip choice id) ab >>> (flip choice id) cd
choice :: Conn k a b -> Conn k c d -> Conn k (Either a c) (Either b d)
choice (Conn ab ba ab') (Conn cd dc cd') = Conn f g h
  where
    f = either (Left . ab) (Right . cd)
    g = either (Left . ba) (Right . dc)
    h = either (Left . ab') (Right . cd')
{-# INLINE choice #-}

infixr 3 `select`

-- | Lift two 'Conn's into a 'Conn' on the <https://en.wikibooks.org/wiki/Category_Theory/Categories_of_ordered_sets coproduct order>
--
select :: Conn k c a -> Conn k c b -> Conn k c (Either a b)
select f g = Conn Left (either id id) Right >>> f `choice` g

-- | Lift two 'Conn's into a 'Conn' on the <https://en.wikibooks.org/wiki/Order_Theory/Preordered_classes_and_poclasses#product_order product order>
--
-- > (strong id) (ab >>> cd) = (strong id) ab >>> (strong id) cd
-- > (flip strong id) (ab >>> cd) = (flip strong id) ab >>> (flip strong id) cd
strong :: Conn k a b -> Conn k c d -> Conn k (a, c) (b, d)
strong (Conn ab ba ab') (Conn cd dc cd') = Conn f g h
  where
    f = bimap ab cd
    g = bimap ba dc
    h = bimap ab' cd'
{-# INLINE strong #-}

infixr 4 `divide`

-- | Lift two 'Conn's into a 'Conn' on the <https://en.wikibooks.org/wiki/Order_Theory/Preordered_classes_and_poclasses#product_order product order>
--
divide :: Total c => Conn k a c -> Conn k b c -> Conn k (a, b) c
divide f g = f `strong` g >>> ordered

-- | The defining connections of a total order.
--
-- >>> outer ordered (True, False)
-- (False,True)
ordered :: Total a => Conn k (a, a) a
ordered = Conn (uncurry max) (id &&& id) (uncurry min)
{-# INLINE ordered #-}

-- | The defining connections of a bounded preorder.
--
bounded :: Bounded a => Conn k () a
bounded = Conn (const minBound) (const ()) (const maxBound)
{-# INLINE bounded #-}

-- | The identity 'Conn'.
identity :: Conn k a a
identity = Conn_ (id &&& id) id
{-# INLINE identity #-}

---------------------------------------------------------------------
-- Conn 'L
---------------------------------------------------------------------

type ConnL = Conn 'L

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
-- /Caution/: /ConnL f g/ must obey \(f \dashv g \). This condition is not checked.
--
-- For further information see 'Data.Connection.Property'.
pattern ConnL :: (a -> b) -> (b -> a) -> ConnL a b
pattern ConnL f g <- (_2 &&& upper -> (f, g)) where ConnL f g = Conn_ (f &&& f) g

{-# COMPLETE ConnL #-}

-- | Witness to the symmetry between 'ConnL' and 'ConnR'.
--
-- > connL . connR = id
-- > connR . connL = id
connL :: ConnR a b -> ConnL b a
connL (ConnR f g) = ConnL f g
{-# INLINE connL #-}

-- | Extract the upper adjoint of a 'ConnL'.
upper :: ConnL a b -> b -> a
upper = inner
{-# INLINE upper #-}

-- | Map over a 'ConnL' from the right.
--
-- This is the unit of the resulting monad:
--
-- > x <~ upper1 c id x
--
-- >>> compare pi $ upper1 f64f32 id pi
-- LT
upper1 :: ConnL a b -> (b -> b) -> a -> a
upper1 (ConnL f g) h a = g $ h (f a)
{-# INLINE upper1 #-}

-- | Zip over a 'ConnL' from the right.
upper2 :: ConnL a b -> (b -> b -> b) -> a -> a -> a
upper2 (ConnL f g) h a1 a2 = g $ h (f a1) (f a2)
{-# INLINE upper2 #-}

-- | Extract the lower half of a 'ConnL'.
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
ceiling :: ConnL a b -> a -> b
ceiling (ConnL f _) = f
{-# INLINE ceiling #-}

-- | Map over a 'ConnL' from the left.
--
-- This is the counit of the resulting comonad:
--
-- > x >~ ceiling1 c id x
--
-- >>> ceiling1 (conn @_ @() @Ordering) id LT
-- LT
-- >>> ceiling1 (conn @_ @() @Ordering) id GT
-- LT
ceiling1 :: ConnL a b -> (a -> a) -> b -> b
ceiling1 (ConnL f g) h b = f $ h (g b)
{-# INLINE ceiling1 #-}

-- | Zip over a 'ConnL' from the left.
ceiling2 :: ConnL a b -> (a -> a -> a) -> b -> b -> b
ceiling2 (ConnL f g) h b1 b2 = f $ h (g b1) (g b2)
{-# INLINE ceiling2 #-}

-- | Generalized maximum.
--
maximize :: ConnL (a, b) c -> a -> b -> c
maximize = curry . ceiling
{-# INLINE maximize #-}

---------------------------------------------------------------------
-- Conn 'R
---------------------------------------------------------------------

type ConnR = Conn 'R

-- | A Galois connection between two monotone functions.
--
-- 'ConnR' is the mirror image of 'ConnL':
--
-- > connR :: ConnL a b -> ConnR b a
--
-- If you only require one connection there is no particular reason to
-- use one version over the other. However some use cases (e.g. rounding)
-- require an adjoint triple of connections that can lower into a standard
-- connection in either of two ways.
--
-- /Caution/: /ConnR f g/ must obey \(f \dashv g \). This condition is not checked.
--
-- For further information see 'Data.Connection.Property'.
pattern ConnR :: (b -> a) -> (a -> b) -> ConnR a b
pattern ConnR f g <- (lower &&& _1 -> (f, g)) where ConnR f g = Conn_ (g &&& g) f

{-# COMPLETE ConnR #-}

-- | Witness to the symmetry between 'ConnL' and 'ConnR'.
--
-- > connL . connR = id
-- > connR . connL = id
connR :: ConnL a b -> ConnR b a
connR (ConnL f g) = ConnR f g
{-# INLINE connR #-}

-- | Extract the lower adjoint of a 'ConnR'.
lower :: ConnR a b -> b -> a
lower = inner
{-# INLINE lower #-}

-- | Map over a 'ConnR' from the left.
--
-- This is the counit of the resulting comonad:
--
-- > x >~ lower1 c id x
--
-- >>> compare pi $ lower1 f64f32 id pi
-- GT
lower1 :: ConnR a b -> (b -> b) -> a -> a
lower1 (ConnR f g) h a = f $ h (g a)
{-# INLINE lower1 #-}

-- | Zip over a 'ConnR' from the left.
lower2 :: ConnR a b -> (b -> b -> b) -> a -> a -> a
lower2 (ConnR f g) h a1 a2 = f $ h (g a1) (g a2)
{-# INLINE lower2 #-}

-- | Extract the upper half of a 'ConnR'
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
floor :: ConnR a b -> a -> b
floor (ConnR _ g) = g
{-# INLINE floor #-}

-- | Map over a 'ConnR' from the right.
--
-- This is the unit of the resulting monad:
--
-- > x <~ floor1 c id x
--
-- >>> floor1 (conn @_ @() @Ordering) id LT
-- GT
-- >>> floor1 (conn @_ @() @Ordering) id GT
-- GT
floor1 :: ConnR a b -> (a -> a) -> b -> b
floor1 (ConnR f g) h b = g $ h (f b)
{-# INLINE floor1 #-}

-- | Zip over a 'ConnR' from the right.
floor2 :: ConnR a b -> (a -> a -> a) -> b -> b -> b
floor2 (ConnR f g) h b1 b2 = g $ h (f b1) (f b2)
{-# INLINE floor2 #-}

-- | Generalized minimum.
--
minimize :: ConnR (a, b) c -> a -> b -> c
minimize = curry . floor
{-# INLINE minimize #-}

---------------------------------------------------------------------
-- Conn k
---------------------------------------------------------------------

-- | An <https://ncatlab.org/nlab/show/adjoint+triple adjoint triple> of Galois connections.
--
-- An adjoint triple is a chain of connections of length 3:
--
-- \(f \dashv g \dashv h \)
--
-- When applied to a 'ConnL' or 'ConnR', the two functions of type @a -> b@ returned will be identical.
--
-- /Caution/: /Conn f g h/ must obey \(f \dashv g \dashv h\). This condition is not checked.
--
-- For detailed properties see 'Data.Connection.Property'.
pattern Conn :: (a -> b) -> (b -> a) -> (a -> b) -> Conn k a b
pattern Conn f g h <- (inner &&& _1 &&& _2 -> (g, (h, f))) where Conn f g h = Conn_ (h &&& f) g

{-# COMPLETE Conn #-}

-- | Extract the upper adjoint of a 'ConnL', or lower adjoint of a 'ConnR'.
--
-- When the connection is an adjoint triple the inner function is returned:
--  
-- >>> inner ratf32 (1 / 8)    -- eighths are exactly representable in a float
-- 1 % 8
-- >>> inner ratf32 (1 / 7)    -- sevenths are not
-- 9586981 % 67108864
inner :: Conn k a b -> b -> a
inner (Conn_ _ g) = g
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
outer :: Conn k a b -> a -> (b, b)
outer (Conn_ f _) = f
{-# INLINE outer #-}

-- | Determine which half of the interval between 2 representations of /a/ a particular value lies.
--
-- @ 'half' c x = 'pcompare' (x - 'lower1' c 'id' x) ('upper1' c 'id' x - x) @
--
-- >>> maybe False (== EQ) $ half f64f32 (midpoint f64f32 pi)
-- True
half :: (Num a, Preorder a) => (forall k. Conn k a b) -> a -> Maybe Ordering
half c x = pcompare (x - lower1 c id x) (upper1 c id x - x)
{-# INLINE half #-}

-- | Return the midpoint of the interval containing x.
--
-- >>> pi - midpoint f64f32 pi
-- 3.1786509424591713e-8
midpoint :: Fractional a => (forall k. Conn k a b) -> a -> a
midpoint c x = lower1 c id x / 2 + upper1 c id x / 2
{-# INLINE midpoint #-}

-- | Return the nearest value to x.
--
-- > round identity = id
--
-- If x lies halfway between two finite values, then return the value
-- with the smaller absolute value (i.e. round away from zero).
--
-- See <https://en.wikipedia.org/wiki/Rounding>.
round :: (Num a, Preorder a) => (forall k. Conn k a b) -> a -> b
round c x = case half c x of
    Just GT -> ceiling c x
    Just LT -> floor c x
    _ -> if x >~ 0 then ceiling c x else floor c x
{-# INLINE round #-}

-- | Lift a unary function over an adjoint triple.
--
-- Results are rounded to the nearest value with ties away from 0.
round1 :: (Num a, Preorder a) => (forall k. Conn k a b) -> (a -> a) -> b -> b
round1 c f x = round c $ f (g x) where Conn _ g _ = c
{-# INLINE round1 #-}

-- | Lift a binary function over an adjoint triple.
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
round2 :: (Num a, Preorder a) => (forall k. Conn k a b) -> (a -> a -> a) -> b -> b -> b
round2 c f x y = round c $ f (g x) (g y) where Conn _ g _ = c
{-# INLINE round2 #-}

-- | Truncate towards zero.
--
-- > truncate identity = id
truncate :: (Num a, Preorder a) => (forall k. Conn k a b) -> a -> b
truncate c x = if x >~ 0 then floor c x else ceiling c x
{-# INLINE truncate #-}

-- | Lift a unary function over an adjoint triple.
--
-- Results are truncated towards zero.
--
-- > truncate1 identity = id
truncate1 :: (Num a, Preorder a) => (forall k. Conn k a b) -> (a -> a) -> b -> b
truncate1 c f x = truncate c $ f (g x) where Conn _ g _ = c
{-# INLINE truncate1 #-}

truncate2 :: (Num a, Preorder a) => (forall k. Conn k a b) -> (a -> a -> a) -> b -> b -> b
truncate2 c f x y = truncate c $ f (g x) (g y) where Conn _ g _ = c
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
median :: (forall k. Conn k (a, a) a) -> a -> a -> a -> a
median c x y z = (x `join` y) `meet` (y `join` z) `meet` (z `join` x)
  where
    join = maximize c
    meet = minimize c
{-# INLINE median #-}

---------------------------------------------------------------------
-- Down
---------------------------------------------------------------------

-- | Convert an inverted 'ConnL' to a 'ConnL'.
--
-- > upL . downL = downL . upL = id
upL :: ConnL (Down a) (Down b) -> ConnL b a
upL (ConnL f g) = ConnL g' f'
  where
    f' x = let (Down y) = f (Down x) in y
    g' x = let (Down y) = g (Down x) in y
{-# INLINE upL #-}

-- | Convert an inverted 'ConnR' to a 'ConnR'.
--
-- > upR . downR = downR . upR = id
upR :: ConnR (Down a) (Down b) -> ConnR b a
upR (ConnR f g) = ConnR g' f'
  where
    f' x = let (Down y) = f (Down x) in y
    g' x = let (Down y) = g (Down x) in y
{-# INLINE upR #-}

-- | Convert a 'ConnL' to an inverted 'ConnL'.
--
-- >>> let counit = upper1 (downL $ conn @_ @() @Ordering) id
-- >>> counit (Down LT)
-- Down LT
-- >>> counit (Down GT)
-- Down LT
downL :: ConnL a b -> ConnL (Down b) (Down a)
downL (ConnL f g) = ConnL (\(Down x) -> Down $ g x) (\(Down x) -> Down $ f x)
{-# INLINE downL #-}

-- | Convert a 'ConnR' to an inverted 'ConnR'.
--
-- >>> let unit = lower1 (downR $ conn @_ @() @Ordering) id
-- >>> unit (Down LT)
-- Down GT
-- >>> unit (Down GT)
-- Down GT
downR :: ConnR a b -> ConnR (Down b) (Down a)
downR (ConnR f g) = ConnR (\(Down x) -> Down $ g x) (\(Down x) -> Down $ f x)
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
-- > a1 <= b && a2 <= b => meet c (ceiling c a1) (ceiling c a2) <= b
--
-- See <https://en.wikipedia.org/wiki/Filter_(mathematics)>
filterL :: Preorder b => ConnL a b -> a -> b -> Bool
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
-- > a1 >= b && a2 >= b => join c (floor c a1) (floor c a2) >= b
--
-- See <https://en.wikipedia.org/wiki/Ideal_(order_theory)>
filterR :: Preorder b => ConnR a b -> a -> b -> Bool
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
