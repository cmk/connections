{-# Language ConstraintKinds #-}

module Data.Semilattice.Signed where

import Control.Applicative
import Control.Category ((>>>))
import Data.Bifunctor (first)
import Data.Connection hiding (first)
import Data.Connection.Float
import Data.Float
import Data.Semifield
import Data.Ord (Down(..))
import Data.Prd
import Data.Prd.Nan
--import Data.Dioid
--import Data.Semigroup.Quantale
import Data.Semigroup.Additive
import Data.Semigroup.Multiplicative
import Data.Semigroup.Join
import Data.Semigroup.Meet
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

-- Trip (Signed a) (Inf (Nan Ordering))
newtype Signed a = Signed { unSigned :: a } deriving Show

instance (Semiring a, Prd a) => Eq (Signed a) where
    (Signed x) == (Signed y) | indeterminate x && indeterminate y = True 
                             | indeterminate x || indeterminate y = False
                             | otherwise = x =~ y -- 0 /= -0

{-
s = Signed anan :: Signed Float
p = Signed pinf :: Signed Float
n = Signed ninf :: Signed Float
x = Signed 4.3
y = Signed (-4.3)

λ> s =~ s
True
λ> n <~ p
True
λ> n <~ s
True
λ> s <~ p
True
λ> s <~ (Signed 4)
False
λ> s ~~ (Signed 4)
True
-}
instance (Field a, Prd a) => Prd (Signed a) where
    Signed x <~ Signed y | indeterminate x && indeterminate y = True
                         | indeterminate x = y =~ pinf
                         | x =~ ninf = indeterminate y || x <~ y
                         | otherwise = x <~ y

{-
    pcompare (Signed x) (Signed y) | indeterminate x && indeterminate y = Just EQ 
                                   | indeterminate x || indeterminate y = Nothing 
                                   | otherwise = pcompare (first Down $ split x) (first Down $ split y)

type FieldLaw a = ((Additive-Group) a, (Multiplicative-Group) a)
-}

--instance Semifield a => Semifield (Signed a)

joinSigned :: (Semifield a, Prd a) => Signed a -> Signed a -> Signed a
joinSigned (Signed a) (Signed b) = Signed $ maybe pinf id $ pmax a b



{-
meetSigned :: Field a => Prd a => a -> a -> a 
meetSigned a b = maybe ninf id $ pmin a b

instance Field a => Semigroup (Join (Signed a)) where
  (<>) = liftA2 joinSigned

instance Field a => Monoid (Join (Signed a)) where
  mempty = Join (Signed ninf)

-- Split
-- Split is a floating point value with a magnitude-based partial order
-- within each sign, but the traditional order between signs.

-- Conn Split (Nan (Either (Down Unsigned) Unsigned))

newtype Split = Split { unSplit :: Float }

f32spl :: Conn Float Split
f32spl = Conn f g where
  f x | x == ninf = Split $ -0
      | otherwise = Split $ either (const 0) id $ split x

  g (Split x) = either (const ninf) id $ split x


instance Show Split where
    show (Split x) = show x

instance Eq Split where
    (Split x) == (Split y) | indeterminate x && indeterminate y = True 
                             | indeterminate x || indeterminate y = False
                             | otherwise = split x == split y -- 0 /= -0

instance Prd Split where
    Split x <~ Split y | indeterminate x && indeterminate y = True
                         | indeterminate x || indeterminate y = False
                         | otherwise = (first Down $ split x) <~ (first Down $ split y)

    pcompare (Split x) (Split y) | indeterminate x && indeterminate y = Just EQ 
                                   | indeterminate x || indeterminate y = Nothing 
                                   | otherwise = pcompare (first Down $ split x) (first Down $ split y)


-- Canonical ordering semigroup
-- >>> Split (-1) + Split 3
-- 3.0
-- >>> Split (-1) + Split (-3)
-- -4.0
-- >>> Split 1 + Split 3
-- 4.0
instance Semigroup (Additive Split) where
    (<>) = liftA2 $ \(Split a) (Split b) -> Split . either id id $ split a + split b

instance Semigroup (Multiplicative Split) where
    (<>) = liftA2 $ \(Split a) (Split b) -> Split . either id id $ split a * split b

-- λ>  Split (-1) * Split (-3) --TODO is this a lawful presemiring?
-- 3.0
instance Presemiring Split

-}

{-
instance Index Split where
    type Idx Split = Nan (Either Word64 Word64)

tripr af32sgn >>> idx @Float

(tripr af32sgn >>> idx)
  :: Conn Split (Data.Prd.NanPrd.Nan GHC.Word.Word64)
-}
