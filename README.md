# connections

[![Build Status](https://travis-ci.com/cmk/connections.svg?branch=master)](https://travis-ci.com/cmk/connections)

Galois connections

For example:

```
ordbin :: Conn 'L Ordering Bool
ordbin = ConnL f g where
  f GT = True
  f _  = False

  g True = GT
  g _    = EQ

binord :: Conn 'R Ordering Bool
binord = ConnR f g where
  f False = LT
  f _     = EQ

  g LT = False
  g _  = True
```

Hosted on [Hackage](https://hackage.haskell.org/package/connections)
