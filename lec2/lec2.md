
### ADT - Algebric Data Types (A General types descuession, not Idris releated)

####  Types cardinality

```Haskell
data Void
data () = ()
```

```Haskell
data Bool = False | True
```

```Haskell
|Void| = 0
|()|   = 1
|Bool| = 2
```

isomorphic types

```Haskell
to :: s -> t
from :: t -> s

to . from = id
from . to = id
```


Sum, Product and Exponential Types

Examples

```Haskell
|Either a b| = |a| + |b|

data Deal a b
  = This a
  | That b
  | TheOther Bool

|Deal a b| = |a| + |b| + |Bool| = |a| + |b| + 2

|Maybe a| = 1 + |a|

|(a, b)| = |a| × |b|



data MixedFraction a = Fraction
{ mixedBit :: Word8
, numerator :: a
, denominator :: a
}


|MixedFraction a| = |Word8| × |a| × |a| = 256 × |a| × |a|
```


#### prove that a × 1 = a by showing an isomorphism between (a, ()) and a.

```Haskell
prodUnitTo :: a -> (a, ())
prodUnitTo a = (a, ())

prodUnitFrom :: (a, ()) -> a
prodUnitFrom (a, ()) = a
````


Likewise, Void acts as a unit for sum types

````Haskell
sumUnitTo :: Either a Void -> a
sumUnitTo (Left a) = a
sumUnitTo (Right v) = absurd v

sumUnitFrom :: a -> Either a Void
sumUnitFrom = Left
````

Function types also have an encoding as
statements about cardinality—they correspond to exponentialization

More generally, the type a -> b has cardinality |b| ^ |a|.
|a -> b| = |b| × |b| × · · · × |b| = |b| ^ |a|


The Curry–Howard Isomorphism


Algebra   Logic    Types
a + b     a ∨ b    Either a b
a × b     a ∧ b    (a, b)
b ^ a     a ⇒ b     a -> b
a = b     a ⇐⇒ b   isomorphism
  0         ⊥      Void
  1         ⊤      ()



### Idris types


Enumerated - types—Types defined by giving the possible values directly
Union types - Enumerated types that carry additional data with each value
Recursive types - Union types that are defined in terms of themselves
Generic types - Types that are parameterized over some other types
Dependent types - Types that are computed from some other value
