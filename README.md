# connections

[![Build Status](https://travis-ci.com/cmk/connections.svg?branch=master)](https://travis-ci.com/cmk/connections)

This library provides an API for working with Galois connections on various common preorders.

Hosted on [Hackage](https://hackage.haskell.org/package/connections).

* [What is a connection?](#intro)
* [What can you do with them?](#what)
* [What's wrong with the numeric functions in `base`?](#base)



### What is a connection? <a name="intro"></a>

A [Galois connection](https://en.wikipedia.org/wiki/Galois_connection) between preorders P and Q is a pair of monotone maps `f :: p -> q` and `g :: q -> p` such that `f x <= y` if and only if `x <= g y`. We say that `f` is the left or lower adjoint, and `g` is the right or upper adjoint of the connection.

For example:

![](./example.png)

Connections are useful for performing lawful conversions between different types [among other things](#what). This library provides connections between common types, combinators & accessors, including lawful versions of [`floor`](https://hackage.haskell.org/package/connections/docs/Data-Connection-Conn.html#v:floor), [`ceiling`](https://hackage.haskell.org/package/connections/docs/Data-Connection-Conn.html#v:ceiling), [`round`](https://hackage.haskell.org/package/connections/docs/Data-Connection-Conn.html#v:round), and [`truncate`](https://hackage.haskell.org/package/connections/docs/Data-Connection-Conn.html#v:truncate).

There is also a [class](https://hackage.haskell.org/package/connections/docs/Data-Connection-Class.html#t:Connection) with lawful versions of `fromInteger` and `fromRational`, suitable for use with `-XRebindableSyntax`

Lastly, it provides [lattices and algebras](https://hackage.haskell.org/package/connections/docs/Data-Lattice.html).

### How do connections work?

Let's look at a simple connection between `Ordering` and `Bool`:

```
ordbin :: Conn 'L Ordering Bool
ordbin = ConnL f g where
  f LT = False
  f _  = True
 
  g False = LT
  g True = GT
```

The two component functions are each monotonic (i.e. `x1 <= x2` implies `f x1 <= f x2`), and are 'interlocked' or adjoint in the specific way outlined above: `f x <= y` if and only if `x <= g y`. 

We can easily verify the adjointness property by hand in this case:

`f`/`g`| `False` | `True`  |
------ | ------- | ------- |
 `LT`  | `=`/`=` | `<`/`<` |
 `EQ`  | `>`/`>` | `=`/`<` |
 `GT`  | `>`/`>` | `=`/`=` |

Each cell represents a pairing of (`x`,`y`) with the two relations `f x _ y` and `x _ g y`. A cell with either `=`/`>`, `>`/`=`, or arrows facing in opposite directions would indictate a failure. See the `test` folder for further examples, or `Data.Connection.Property` for the properties tested.

Interestingly, there is a second 'flipped' connection available as well, where the same `g` can serve as the lower end:

```
binord :: Conn 'L Bool Ordering
binord = ConnL g h where
  g False = LT
  g True  = GT
  
  h GT = True
  h _  = False
```

It turns out that this situation happens fairly frequently- the three functions are called an adjoint [string](https://ncatlab.org/nlab/show/adjoint+string) or chain of length 3 (i.e. `f` is adjoint to `g` is adjoint to `h`). It is useful to be able to work with these length-3 chains directly, because the choice of two routes back from P to Q is what enables lawful rounding and truncation. 

Therefore the connection type in `Data.Connection.Conn` is parametrized over a data kind (e.g. `'L`) that specifies which pair we are talking about (`f`/`g` or `g`/`h`). When a chain is available the data kind is existentialized (see the view pattern `Conn`).

In our example above, it turns out that a small change in the adjoints on each side enables such a chain:

```
ordbin :: Conn k Ordering Bool
ordbin = Conn f g h
  where
    f LT = False
    f _  = True
        
    g False = LT
    g True = GT
    
    h GT = True
    h _  = False
```

Once again we can check the adjointness property for each of the two connections (`f`/`g` or `g`/`h`):
 
 `f`/`g`/`h` |   `False`   |    `True`   |
------------ | ----------- | ----------- |
    `LT`     | `=`/`=`/`=` | `<`/`<`/`<` |
    `EQ`     | `>`/`>`/`=` | `=`/`<`/`<` |
    `GT`     | `>`/`>`/`>` | `=`/`=`/`=` |




### What can you do with them? <a name="what"></a>

Lots of things!

At a basic level connections can tell you interesting things about the underlying types themselves:

```
λ> import Data.Connection
λ> inner ratf32 (1 / 8)    -- eighths are exactly representable in a float
1 % 8
λ> outer ratf32 (1 % 8)
(0.125,0.125)
λ> inner ratf32 (1 / 7)    -- sevenths are not
9586981 % 67108864
λ> outer ratf32 (1 % 7)
(0.14285713,0.14285715)
```

You can use them to safely convert between types obviously:

```
λ> :t ceiling f64w32
ceiling f64w32 :: Double -> Extended Word32
λ> ceiling f64w32 pi
Finite 4
λ> ceiling f64w32 (0/0)
PosInf
λ> floor f64w32 (0/0)
NegInf
```

... as well as to round, truncate, take medians, etc.

```
λ> round f64w32 pi
Finite 3
λ> round f64w32 (-pi)
Finite 0
λ> round f64i32 (-pi)
Finite (-3)
λ> median f32f32 1 9 7
7.0
λ> median f32f32 1 9 (-1/0)
1.0
λ> median f32f32 1 9 (0/0)
9.0
λ> median f32f32 1 9 (1/0)
9.0
```

You can also lift functions over connections: 

```
λ> :t round1 f64f32
round1 f64f32 :: (Double -> Double) -> Float -> Float
λ> f x = let m = 1.6777215e7 in (m + x) - m
λ> f 2.0 :: Float
1.0
λ> round1 f64f32 f 2.0  -- Avoid loss of precision
2.0
```

... and use various combinators to combine them:

```
λ> :t divide rati16 f32i16
divide rati16 f32i16 :: Conn k (Rational, Float) (Extended Int16)
λ> maximize (divide rati16 f32i16) 2.99 3.01
Finite 4
λ> maximize (divide rati16 f32i16) 2.99 (0/0)
PosInf
λ> minimize (divide rati16 f32i16) 2.99 (0/0)
NegInf
```

In particular connections form a category, which means they compose:

```
λ> :t MkSystemTime
MkSystemTime :: Int64 -> Word32 -> SystemTime
λ> :t connL ratf64 >>> ratsys
connL ratf64 >>> ratsys :: Conn 'L Double (Extended SystemTime)
λ> ceiling (connL ratf64 >>> ratsys) pi
Finite (MkSystemTime {systemSeconds = 3, systemNanoseconds = 141592654})
λ> diffSystemTime x y = inner (connL ratf64 >>> ratsys) $ round2 ratsys (-) (Finite x) (Finite y)
λ> :t diffSystemTime
diffSystemTime :: SystemTime -> SystemTime -> Double
λ> diffSystemTime (MkSystemTime 0 0) (MkSystemTime 0 maxBound)
-4.294967295
divMod (maxBound @Word32) (10^9)
(4,294967295)
```



### What's wrong with the numeric functions in `base`? <a name="base"></a>

Quite a bit unfortunately. As far as `connections` is concerned though, there are two classes of problem: 

* the `Fractional` instances of `Ord` (e.g. `Float`, `Double`, `Rational`)
* the conversion methods of `Integral`, `Num`, `Real` and `Fractional`


##### Orders: total and partial 

The root problem here is quite old: `NaN` values (e.g. `0/0`, `0 * 1/0`, `1/0 - 1/0`, etc) are not comparable to any finite number, so fractional and floating point types cannot be totally ordered.

However the `Ord` instances of `Float`, `Double`, and `Rational` ignore this, leading to nonsensical behavior:

```
λ> import GHC.Real (Ratio(..))
λ> 0 :% 0 < -1
False
λ> 0 :% 0 == -1
False
λ> 0 :% 0 <= -1
True
λ> compare @Float (0/0) (1/0)
GT
λ> compare @Float (1/0) (0/0)
GT
λ> max @Float 0 (-0.0) 
-0.0
λ> max @Float (-0.0) 0
0.0
```

The behavior isn't consistent accross types either:

```
λ> 0 :% 0 <= 0 :% 0
True
λ> (0/0 :: Float) <= 0/0
False
```

This is dangerous and can lead to bugs [well outside of numerical applications](https://github.com/ocaml/ocaml/issues/5222). Fortunately the solution is fairly simple: create a [`Preorder`](https://hackage.haskell.org/package/connections/docs/Data-Order.html#t:Preorder) class with lawful instances for types with `NaN` values. Rust does something [similar](https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html).



##### Coercive conversions

The second set of problems is with the various conversion methods defined in `Integral`, `Num`, `Real` and `Fractional`:

```
fromInteger :: Num a => Integer -> a
toInteger :: Integral a => a -> Integer
fromRational :: Fractional a => Rational -> a
toRational :: Real a => a -> Rational
```

The problem with the conversion methods is that they are all lawless: the classes do not define any equational laws that the user can expect instances to obey. Predictably, the result is chaos:

```
λ> toInteger @Int8 128
-128
λ> fromInteger @Int8 128
-128
λ> toRational @Float (0/0)
(-510423550381407695195061911147652317184) % 1
λ> fromRational @Float (0/0)
*** Exception: Ratio has zero denominator
```

One could object that the examples above are exceptional. Unfortunately, surprises can occur in completely mundane situations as well:

```
λ> fromRational @Float 5000000.2 -- your fintech backend is under-charging 20¢ on every $5M transaction
5000000.0
λ> fromRational @Float 5000000.3 -- or is it over-charging 20¢?
5000000.5
```

Worse, these conversion methods in turn give rise to the aptly-named [coercions](hackage.haskell.org/package/base/docs/src/GHC-Real.html#fromIntegral):

```
fromIntegral :: (Integral a, Num b) => a -> b
fromIntegral = fromInteger . toInteger

realToFrac :: (Real a, Fractional b) => a -> b
realToFrac = fromRational . toRational
```

If you're not careful, these 'just make it type-check' functions will get slotted in everywhere in your application. Sometimes that's ok, but if your application has to deal with small, large, infinite, or otherwise exceptional values then the resultant behavior will make your (or somebody's) life miserable:

```
λ> fromIntegral @Int8 @Word8 128
128
λ> fromIntegral @Int8 @Word 128
18446744073709551488
λ> fromIntegral @Int8 @Natural 128 -- your colleagues will appreciate this _underflow_ exception 
*** Exception: arithmetic underflow
```

```
λ> realToFrac @Float @Double 8765432.1
8765432.0
λ> realToFrac @Double @Float (1/0)
Infinity
λ> realToFrac @Rational @Double (1 :% 0)
Infinity
λ> realToFrac @Double @Rational (1/0)
179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 % 1 -- Infinity is a 309 digit number
```

A similar set of issues arises from the methods of [`RealFrac`](hackage.haskell.org/package/base/docs/GHC-Real.html#t:RealFrac):

```
floor :: (RealFrac a, Integral b) => a -> b
ceiling :: (RealFrac a, Integral b) => a -> b
round :: (RealFrac a, Integral b) => a -> b
truncate :: (RealFrac a, Integral b) => a -> b
```

Here again to the extent that laws are given (e.g. 'ceiling x returns the least integer not less than x'), they seem to be easily violated: 

```
λ> ceiling @Float @Int (1/0)
0
λ> ceiling @Float @Int 3000000.1
3000000
```

Finally, because everyting is forced to go through `Integer` and/or `Rational` you get wierd effects 

```
λ> import GHC.Float (float2Double)
λ> float2Double (1/0)
Infinity
λ> realToFrac @Float @Double (1/0)
3.402823669209385e38
λ> realToFrac @Float @Rational (1/0)
340282366920938463463374607431768211456 % 1
λ> ceiling @Float @Integer (1/0)  
340282366920938463463374607431768211456 -- must be somebody's favorite number
```

The basic problem behind all of this is that functions that can only be meaningfully given laws in pairs (like `toRational` and `fromRational`) are instead broken up between different classes, with no semantics whatsoever.
