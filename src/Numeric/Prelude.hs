{-# LANGUAGE RebindableSyntax #-}
module Numeric.Prelude
  ( -- * Combinators
    id,
    (.),
    ($),
    ($!),
    (&),
    const,
    flip,
    on,
    seq,
    -- * Primitive types
    -- ** Bool
    Bool (..),
    bool,
    (&&),
    (||),
    not,
    otherwise,
    ifThenElse,
    -- ** Char
    Char,
    -- ** Int
    Integer,
    Int,
    Int8,
    Int16,
    Int32,
    Int64,
    -- ** Word
    Natural,
    Word,
    Word8,
    Word16,
    Word32,
    Word64,
    -- ** Rational
    Ratio(..),
    -- ** Floating
    Float,
    Double,
    fmod, floor, ceil, trunc, round,
    sqrt, cbrt, pow, log, exp, ldexp,
    pi, sin, cos, tan, 
    asin, acos, atan, atan2, 
    sinh, cosh, tanh, 
    asinh, acosh, atanh,
    -- * Numerical Typeclasses
    -- ** Eq
    Eq (..),
    -- ** Orders
    Prd (..),
    Ordering (..),
    min, max,
    compare,
    comparing,
    -- ** Connections
    TripRatio(..),
    ConnInteger(..),
    fromRational,
    fromInteger,
    floor16, ceil16, round16, trunc16,
    floor32, ceil32, round32, trunc32,
    -- ** Magmas
    Semigroup (..),
    Monoid (..),
    mreplicate,
    Magma(..), 
    Quasigroup,
    Loop,
    Group(..), 
    -- ** Semirings
    Semiring,
    Ring,
    (+), (-), (*), (^),
    zero, one,
    abs,
    negate,
    signum,
    sum,
    product,
    -- ** Semifields
    Semifield,
    Field,
    (/), (^^),
    pinf, ninf, anan,
    recip,
    -- * Data structures
    -- ** Either
    Either (..),
    either,
    -- ** Maybe
    Maybe (..),
    fromMaybe,
    maybe,
    -- ** Tuple
    fst,
    snd,
    curry,
    uncurry,
    -- * Algebraic structures
    -- ** Functor
    Functor (..),
    (<$>),
    ($>),
    void,
    -- ** Bifunctor
    Bifunctor (..),
    -- ** Applicative
    Applicative (..),
    (<**>),
    liftA3,
    -- ** Alternative
    Alternative (..),
    asum,
    -- ** Traversable
    Traversable (..),
    for,
    -- ** Monad
    Monad ((>>=), (>>), return),
    (=<<),
    forM,
    forM_,
    mapM_,
    when,
    -- ** MonadPlus
    MonadPlus (..),
    guard,
    msum,
    -- ** Foldable
    Foldable (foldMap, fold),
    foldl', foldr',
    for_,
    traverse_,
    -- ** Show
    Show (..),
    -- *** ShowS
    ShowS,
    showString,
  ) where

import Control.Applicative ((<**>), Alternative (..), Applicative (..), empty, liftA3)
import Control.Monad ((=<<), Monad (..), MonadPlus (..), forM, forM_, guard, mapM_, msum, when)
import Data.Bifunctor (Bifunctor (..), first, second)
import Data.Bool ((&&), Bool (..), bool, not, otherwise, (||))
import Data.Char (Char)
import Data.Connection.Int (ConnInteger(..), fromInteger)
import Data.Connection.Ratio (TripRatio(..), fromRational)
import Data.Connection.Round (floor16, ceil16, trunc16, round16, floor32, ceil32, trunc32, round32)
import Data.Either (Either (..), either)
import Data.Eq (Eq (..))
import Data.Float (fmod, floor, ceil, trunc, round, sqrt, cbrt, pow, log, exp, ldexp, sin, cos, tan
  , asin, acos, atan, atan2, sinh, cosh, tanh, asinh, acosh, atanh)
import Data.Foldable (Foldable (), asum, fold, foldMap, foldl', foldr', for_, traverse_)
import Data.Function (($), (&), (.), const, flip, id, on)
import Data.Functor (($>), (<$>), Functor (..), void)
import Data.Int (Int, Int16, Int32, Int64, Int8)
import Data.Maybe (Maybe (..), fromMaybe, maybe)
import Data.Monoid (Monoid (..))
import Data.Ord (Ordering (..), min, max, compare, comparing)
import Data.Prd (Prd (..))
import Data.Semifield (Semifield, Field, (/), (^^), anan, pinf, ninf, recip)
import Data.Semigroup (Semigroup (..))
import Data.Semiring (Semiring, Ring, (+), (-), (*), (^), zero, one, abs, negate, signum, sum, product)
import Data.Semiring (Magma(..), Quasigroup, Loop, Group(..), mreplicate)
import Data.Traversable (Traversable (..), for)
import Data.Tuple (curry, fst, snd, uncurry)
import Data.Word (Word, Word16, Word32, Word64, Word8)
import GHC.Real (Ratio(..))
import Numeric.Natural (Natural)
import Text.Show (Show (..), ShowS, showString)

import Prelude (($!), Double, Float, Integer, seq)

pi :: TripRatio Integer b => b
pi = 3.141592653589793238

-- Used in conjunction with RebindableSyntax.
ifThenElse :: Bool -> a -> a -> a
ifThenElse b x y = bool y x b
{-# INLINE ifThenElse #-}
