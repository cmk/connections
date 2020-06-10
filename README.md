# connections
Galois connections

For example:

```
ordbin :: Conn Ordering Bool
ordbin = Conn f g where
  f GT = True
  f _  = False

  g True = GT
  g _    = EQ

binord :: Conn Bool Ordering
binord = Conn f g where
  f False = LT
  f _     = EQ

  g LT = False
  g _  = True
```
