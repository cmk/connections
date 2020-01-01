{-# Language ConstraintKinds #-}

module Data.Dioid.Signed where

import Control.Applicative
import Control.Category ((>>>))
import Data.Bifunctor (first)
import Data.Connection hiding (first)
import Data.Connection.Float
import Data.Float
import Data.Ord (Down(..))
import Data.Prd
import Data.Prd.Nan
--import Data.Dioid
--import Data.Semigroup.Quantale
import Data.Semigroup.Additive
import Data.Semigroup.Multiplicative
import Data.Semiring
import Prelude hiding (Num(..))


{-
--p. 340
Semiring of Signed Numbers
With every real number a, we associate four signed numbers a+,a−,a◦anda? corresponding respectively to: 
a obtained as the limit
of a sequence of numbers > a (a+); 
of a sequence of numbers < a (a−); 
of a sequence of numbers all equal to a (a◦); 
of a sequence of numbers only convergent towards a (a?).
We define the addition⊕of two signed numbers (s, a) and (σ, b) as: (s, a)+(σ, b)=(s+σ, a+b)
and the multiplication by: (s, a) * (σ, b)= (signOf a * σ ̇+ signOf b * s ̇+ s*σ, a*b)

where ̇+and ̇×are addition and the multiplication of qualitative algebra (Sect. 4.5.3) 

One verifies that(R×S,⊕,⊗)is a semiring. 
It is not a dioid however, becausethe setR×S is not canonically ordered by⊕.

data Signed a = Signed Sign a
type RealField a = (Field a, Ord a)
instance RealField a => Semiring (Signed a)
-}

-- | 'Sign' is similar to 'Maybe Ordering', but has a distinct poset ordering:
--
-- @ 'Indeterminate' >= 'Positive' >= 'Zero'@ and
-- @ 'Indeterminate' >= 'Negative' >= 'Zero'@ 
--
-- Note that 'Positive' and 'Negative' are not comparable. 
--
--   * 'Positive' can be regarded as representing (0, +∞], 
--   * 'Negative' as representing [−∞, 0), 
--   * 'Indeterminate' as representing [−∞, +∞] v NaN, and 
--   * 'Zero' as representing the set {0}.
--
data Sign = Zero | Negative | Positive | Indeterminate deriving (Show, Eq)

signOf :: (Eq a, (Additive-Monoid) a, Prd a) => a -> Sign
signOf = maybe Indeterminate fromOrdering . sign

fromOrdering :: Ordering -> Sign
fromOrdering LT = Negative
fromOrdering EQ = Zero
fromOrdering GT = Positive

--fromSign :: Sign -> Maybe Ordering

instance Semigroup Sign where
    Positive <> Positive            = Positive
    Positive <> Negative            = Indeterminate
    Positive <> Zero                = Positive
    Positive <> Indeterminate       = Indeterminate

    Negative <> Positive            = Indeterminate
    Negative <> Negative            = Negative
    Negative <> Zero                = Negative
    Negative <> Indeterminate       = Indeterminate

    Zero <> a                       = a

    Indeterminate <> _              = Indeterminate

instance Monoid Sign where
    mempty = Zero

{-
⊕+−0?
++?+?
−?−−?
0+−0?
?????

⊗+−0?
++−0?
−−+0?
00000
???0?

instance Semiring Sign where
    Positive >< a = a

    Negative >< Positive            = Negative
    Negative >< Negative            = Positive
    Negative >< Zero                = Zero
    Negative >< Indeterminate       = Indeterminate

    Zero >< _                       = Zero

    --NB: measure theoretic zero
    Indeterminate >< Zero           = Zero
    Indeterminate >< _              = Indeterminate

    fromBoolean = fromBooleanDef Positive
-}

-- TODO if we dont use canonical ordering then we can define a
-- monotone map to floats
instance Prd Sign where
    Positive <~ Positive         = True
    Positive <~ Negative         = False
    Positive <~ Zero             = False
    Positive <~ Indeterminate    = True 

    Negative <~ Positive         = False
    Negative <~ Negative         = True
    Negative <~ Zero             = False
    Negative <~ Indeterminate    = True
    
    --Zero <~ Indeterminate        = False
    Zero <~ _                    = True

    Indeterminate <~ Indeterminate  = True
    Indeterminate <~ _              = False


instance Minimal Sign where
    minimal = Zero

instance Maximal Sign where
    maximal = Indeterminate


-- Signed
-- Signed is a floating point value with a magnitude-based partial order
-- within each sign, but the traditional order between signs.

-- Conn Signed (Nan (Either (Down Unsigned) Unsigned))

-- TODO rename to Split?
newtype Signed = Signed { unSigned :: Float }

f32sgn :: Conn Float Signed
f32sgn = Conn f g where
  f x | x == nInf = Signed $ -0
      | otherwise = Signed $ either (const 0) id $ split x

  g (Signed x) = either (const nInf) id $ split x


instance Show Signed where
    show (Signed x) = show x

instance Eq Signed where
    (Signed x) == (Signed y) | isNanf x && isNanf y = True 
                             | isNanf x || isNanf y = False
                             | otherwise = split x == split y -- 0 /= -0

instance Prd Signed where
    Signed x <~ Signed y | isNanf x && isNanf y = True
                         | isNanf x || isNanf y = False
                         | otherwise = (first Down $ split x) <~ (first Down $ split y)

    pcompare (Signed x) (Signed y) | isNanf x && isNanf y = Just EQ 
                                   | isNanf x || isNanf y = Nothing 
                                   | otherwise = pcompare (first Down $ split x) (first Down $ split y)


-- Canonical ordering semigroup
-- >>> Signed (-1) + Signed 3
-- 3.0
-- >>> Signed (-1) + Signed (-3)
-- -4.0
-- >>> Signed 1 + Signed 3
-- 4.0
instance Semigroup (Additive Signed) where
    (<>) = liftA2 $ \(Signed a) (Signed b) -> Signed . either id id $ split a + split b

instance Semigroup (Multiplicative Signed) where
    (<>) = liftA2 $ \(Signed a) (Signed b) -> Signed . either id id $ split a * split b

-- λ>  Signed (-1) * Signed (-3) --TODO is this a lawful presemiring?
-- 3.0
instance Presemiring Signed


{-
instance Index Signed where
    type Idx Signed = Nan (Either Word64 Word64)

tripr af32sgn >>> idx @Float

(tripr af32sgn >>> idx)
  :: Conn Signed (Data.Prd.NanPrd.Nan GHC.Word.Word64)
-}
