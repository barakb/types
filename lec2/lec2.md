
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

data Deal a b = This a
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

prove that a × 1 = a by showing an isomorphism between (a, ()) and a.

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

\|a -> b| = |b| × |b| × · · · × |b| = |b| ^ |a|



The Curry–Howard Isomorphism


|Algebra |  Logic  | Types         |
|:------:|:-------:|:-------------:|
|a + b   |  a ∨ b  | Either a b    |
|a × b   |  a ∧ b  | (a, b)        |
|b ^ a   |  a ⇒ b  |  a -> b       |
|a = b   |  a ⇐⇒ b | isomorphism   |
|  0     |    ⊥    | Void          |
|  1     |    ⊤    | ()            |



### Idris types


Enumerated - types—Types defined by giving the possible values directly

```Idris
data Bool = False | True
data Direction = North | East | South | West
```

Union types - Enumerated types that carry additional data with each value

```Idris 
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double       
```

This is the same as

```Idris
data Shape : Type where
     Triangle : Double -> Double -> Shape
     Rectangle : Double -> Double -> Shape
     Circle : Double -> Shape
```
Talk about types and kinds
    

Recursive types - Union types that are defined in terms of themselves

```Idris
data Nat = Z | S Nat

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture
```

Generic types - Types that are parameterized over some other types

```Idris
data Maybe a = Just a | Nothing
data Either a b = Left a | Right b
data Tree elem = Empty | Node (Tree elem) elem (Tree elem)
```

Dependent types - Types that are computed from some other value

A dependent data type is a type that’s computed from some other value. for example type, Vect, where the exact type is calculated from the vector’s
length:
Vect : Nat -> Type -> Type
In other words, the type of a Vect depends on its length.

```Idris
data Vect : Nat -> Type -> Type where
  Nil : Vect 0 elem
  (::) : elem -> Vect len elem -> Vect (S len) elem
```


Piano numbers axioms

* 0 is a natural number.

The next four axioms describe the equality relation. Since they are logically valid in first-order logic with equality, they are not considered to be part of "the Peano axioms" in modern treatments.

* For every natural number x, x = x. That is, equality is reflexive.
* For all natural numbers x and y, if x = y, then y = x. That is, equality is symmetric.
* For all natural numbers x, y and z, if x = y and y = z, then x = z. That is, equality is transitive.
* For all a and b, if b is a natural number and a = b, then a is also a natural number. That is, the natural numbers are closed under equality.

The remaining axioms define the arithmetical properties of the natural numbers. The naturals are assumed to be closed under a single-valued "successor" function S.

* For every natural number n, S(n) is a natural number.
* For all natural numbers m and n, m = n if and only if S(m) = S(n). That is, S is an injection.
* For every natural number n, S(n) = 0 is false. That is, there is no natural number whose successor is 0.o

[piano.idr](piano.idr)
