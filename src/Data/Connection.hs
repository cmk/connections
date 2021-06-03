{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Safe #-}
{-# OPTIONS_HADDOCK show-extensions #-}

-- |
--
-- This library provides connections between common types, combinators & accessors,
-- including lawful versions of 'floor', 'ceiling', 'round', and 'truncate'. There
-- is also a separately exported 'Data.Connection.Class.Connection' class, along
-- with lawful versions of 'Data.Connection.Class.fromInteger' and
-- 'Data.Connection.Class.fromRational', suitable for use with /-XRebindableSyntax/.
-- Lastly, there are 'Data.Lattice.Semilattice' and 'Data.Lattice.Algebra' classes
-- based on the same construction.
--
-- /connections/ is extensively tested, and it exports properties for use in testing
-- your own connections. See "Data.Connection.Property" and "Data.Lattice.Property".
-- In addition to the property tests there are several doctests scattered around,
-- these are runnable as a standalone executable. See the /doctest/ stanza in the
-- library's cabal file.
module Data.Connection (
   
    -- $example
    
    Side(..),
    
    -- * Types
    Cast,
    pattern Cast,
    pattern CastL,
    pattern CastR,
    swapL,
    swapR,

    -- * Combinators
    (>>>),
    (<<<),
    mapped,
    choice,
    select,
    strong,
    divide,
    
    -- * Accessors
    half,
    outer,
    inner,
    upper,
    upper1,
    upper2,
    lower,
    lower1,
    lower2,
    
    -- ** max/min
    maximize,
    minimize,
    midpoint,
    median,
    
    -- ** ceiling
    ceiling,
    ceiling1,
    ceiling2,
   
    -- ** floor
    floor,
    floor1,
    floor2,
   
    -- ** round
    round,
    round1,
    round2,
    
    -- ** truncate
    truncate,
    truncate1,
    truncate2,
    
    -- * Connections
    bounded,
    ordered,
    identity,
    
    -- ** Unsigned ints
    
    -- *** Word8
    i08w08,
    f32w08,
    f64w08,
    ratw08,

    -- *** Word16
    w08w16,
    i08w16,
    i16w16,
    f32w16,
    f64w16,
    ratw16,

    -- *** Word32
    w08w32,
    w16w32,
    i08w32,
    i16w32,
    i32w32,
    f32w32,
    f64w32,
    ratw32,

    -- *** Word64
    w08w64,
    w16w64,
    w32w64,
    i08w64,
    i16w64,
    i32w64,
    i64w64,
    ixxw64,
    f32w64,
    f64w64,
    ratw64,

    -- *** Word
    w08wxx,
    w16wxx,
    w32wxx,
    w64wxx,
    i08wxx,
    i16wxx,
    i32wxx,
    i64wxx,
    ixxwxx,
    f32wxx,
    f64wxx,
    ratwxx,

    -- *** Natural
    w08nat,
    w16nat,
    w32nat,
    w64nat,
    wxxnat,
    i08nat,
    i16nat,
    i32nat,
    i64nat,
    ixxnat,
    intnat,
    f32nat,
    f64nat,
    ratnat,
    
    -- ** Signed ints
    
    -- *** Int8
    f32i08,
    f64i08,
    rati08,
    
    -- *** Int16
    w08i16,
    i08i16,
    f32i16,
    f64i16,
    rati16,

    -- *** Int32
    w08i32,
    w16i32,
    i08i32,
    i16i32,
    f32i32,
    f64i32,
    rati32,

    -- *** Int64
    w08i64,
    w16i64,
    w32i64,
    i08i64,
    i16i64,
    i32i64,
    f32i64,
    f64i64,
    rati64,

    -- *** Int
    w08ixx,
    w16ixx,
    w32ixx,
    i08ixx,
    i16ixx,
    i32ixx,
    i64ixx,
    f32ixx,
    f64ixx,
    ratixx,
    sysixx,

    -- *** Integer
    w08int,
    w16int,
    w32int,
    w64int,
    wxxint,
    natint,
    i08int,
    i16int,
    i32int,
    i64int,
    ixxint,
    f00int,
    f32int,
    f64int,
    ratint,

    -- ** Rational
    ratrat,

    -- ** Floating point
 
    -- *** Float
    f32f32,
    f64f32,
    ratf32,

    -- *** Double
    f64f64,
    ratf64,
    
    -- ** Fixed point
    f32fix,
    f64fix,
    ratfix,

    -- *** Uni
    f01f00,
    f02f00,
    f03f00,
    f06f00,
    f09f00,
    f12f00,

    -- *** Deci
    f02f01,
    f03f01,
    f06f01,
    f09f01,
    f12f01,

    -- *** Centi
    f03f02,
    f06f02,
    f09f02,
    f12f02,

    -- *** Milli
    f06f03,
    f09f03,
    f12f03,

    -- *** Micro
    f09f06,
    f12f06,

    -- *** Nano
    f12f09,

    -- ** Time

    -- *** SystemTime
    f32sys,
    f64sys,
    f09sys,
    ratsys,

    -- * Extended
    extended,
    Extended (..),

) where

import safe Data.Connection.Cast
import safe Data.Connection.Fixed
import safe Data.Connection.Float
import safe Data.Connection.Int
import safe Data.Connection.Ratio
import safe Data.Connection.Time
import safe Data.Connection.Word

import safe Prelude hiding (ceiling, floor, round, truncate)


 
{- $example
 
 ==== What is a Galois connection?

 A [Galois connection](https://en.wikipedia.org/wiki/Galois_connection) is an 
 adjunction in the category of preorders: a pair of monotone maps /f :: p -> q/
 and /g :: q -> p/ between preorders /p/ and /q/, such that

 /f x <= y/ if and only if /x <= g y/

 We say that /f/ is the left or lower adjoint, and /g/ is the right or upper
 adjoint of the connection.

 For illustration, here is a simple example from
 [7 Sketches](https://math.mit.edu/~dspivak/teaching/sp18/7Sketches.pdf):

 <<img/example.png example>>

 Note that the two component functions are each monotonic:

 @ x1 'Data.Order.Syntax.<=' x2 implies f x1 'Data.Order.Syntax.<=' f x2 @

 and furthermore they are are interlocked (i.e. adjoint) in the specific way
 outlined above:

 @ f x 'Data.Order.Syntax.<=' y if and only if x 'Data.Order.Syntax.<=' g y @

 See the [README](https://github.com/cmk/connections/blob/master/README.md) for
 a more extensive overview.
-}
