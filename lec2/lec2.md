### Propositional logic

The propositional branch of logic is concerned with the study of propositions, which are statements that are either ⊤ (true) or ⊥ (false). 
Variables can be used to represent propositions. Propositions are formed by other propositions with the use of logical connectives. 
The most basic logical connectives are ∧ (and), ∨ (or), ¬ (negation), and → (implication).
For example, we can say a = Salad is organic, and thus the variable a represents
a true statement. Another statement is a = Rock is organic, and thus a is a false
statement. The statement a = Hi there! is neither a true nor a false statement, and thus is not a proposition.

*Every statment in propositional logic can be proved or falsified using truth table.*


### First-order logic

The first-order logic logical system extends propositional logic by addition-
ally covering predicates and quantifiers. A predicate P (x) takes an input
x, and produces either true or false as an output. There are two quantifiers
introduced: ∀ (universal quantifier) and ∃ (existential quantifier).
One example of a predicate is P(x) = x is organic, with P (Salad) = ⊤, but P (Rock) =
⊥.
In the following example the universal quantifier says that the predicate will hold for
all possible choices of x: ∀x, P (x). Alternatively, the existential quantifier says that
the predicate will hold for at least one choice of x: ∃x, P (x).
Another example of combining a predicate with the universal quantifier is P(x) = x
is a mammal, then ∀x, P (x) is true, for all x ranging over the set of humans. We can
choose P(x) = x eats salad with ∃x, P (x) to say that there is at
least one person that eats salad.

The negation of the quantifiers is defined as follows:
1. Negation of universal quantifier: ¬(∀x, P (x)) ↔ ∃x, ¬P (x)
2. Negation of existential quantifier: ¬(∃x, P (x)) ↔ ∀x, ¬P (x)
As an example, for P(x) = x eats salad the negation of ∃x, P (x) is
∀x, ¬P (x). That is, the negation of there is at least one person that eats salad is for all persons x, x does not eat salad,
or simply put nobody eat salad.


### Higher-order logic
In first order logic, predicates act like functions that take an input value and produce
a proposition. A predicate can’t be true or false until a specific value is substituted for
the variables, and the quantifiers ∀ and ∃ “close” over a predicate to give a statement
which can be either true or false.
Likewise, we can define a “metapredicate” that acts like a function on predicates. For
example, let Γ(P ) be the statement there exists a person x such that P(x) is
true. Note that it doesn’t make sense to ask if Γ(P ) is true or false until we plug in
a specific predicate P . But we can quantify over P , and construct a statement like
∀P, Γ(P ). In English, this statement translates to For any given property P, there
exists a person satisfying that property.
Metapredicates like Γ are called second-order, because they range over first order
predicates. And there’s no reason to stop there; we could define third-order predicates
that range over second-order predicates, and fourth-order predicates that range over
third-order predicates, and so on.


Moving up the hierarchy of logical systems brings power, at a price. Propositional
(zeroth-order) logic is completely decidable. Predicate (first-order) logic is no longer
decidable, and by Gödel’s incompleteness theorem we have to choose between
completeness and consistency, but at least there is still an algorithm that can
determine whether a proof is valid or not. For second-order and higher logic we
lose even this - we have to choose between completeness, consistency, and a proof
detection algorithm.


### Proofs by truth tables (Propositional logic)

Here’s one claim: The proposition A ∧ B → B is true for any values of A and B .
How do you convince someone that this proposition is really true?
We can use one proof technique which is to construct a truth table. The
way truth tables are constructed for a given statement is to break it down
into atoms and then include every subset of the expression.
For example, to prove the statement A ∧ B → B , we can approach as follows:

A |B |A ∧ B | A ∧ B → B
--|--|------|----------
⊤ |⊤ |  ⊤   |    ⊤ 
⊤ |⊥ |  ⊥   |    ⊤
⊥ |⊤ |  ⊥   |    ⊤
⊥ |⊥ |  ⊥   |    ⊤

### Three-column proofs (first order logic)

As we’ve defined before, an argument is a list of statements. There are several ways
to do mathematical proofs. Another one of them is by using the so-called three column proofs. For this technique we construct a table with three columns: number
of step, step (or expression derived), and reasoning (explanation of how we got to the particular step).

Modus ponens (method of affirming) and modus tollens (method of denying) are two inference rules in logic. Their definition is as follows:

1. Modus ponens states: If we are given p → q and p, then we can conclude q
2. Modus tollens states: If we are given p → q and ¬q, then we can conclude ¬p
For example, given A ∨ B , B → C , ¬C , prove A. We can approach the proof as follows:

No.|  Step		    |   Reasoning												 
---|----------------|------------------------------------------------------------------
1  |  A ∨ B		   	|	Given													 
2  |  B → C		   	|	Given													 
3  |  ¬C			|  	Given													 
4  |  (B → C) ∧ ¬C  |	2 and 3													 
5  |  ¬B			|  	Modus tollens rule on 4, i.e. (p → q ∧ ¬q) → ¬p			 
6  |  (A ∨ B) ∧ ¬B  |	1 and 5													 
7  |  A             |	6, where p ∧ ¬p is a contradiction, i.e. invalid argument


Proofs with truth tables look a lot easier than column proofs. You just plug
in truth values and simplify, where column proofs require planning ahead.
Why would we bother with column proofs?
Proofs with truth tables only work for propositional (zeroth order) theorems - the table method is essentially the decidability algorithm for zeroth
order logic. That’s why they are easy (if verbose) and always work, and why column proofs become necessary once we’re using quantifiers.





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

Type constractor vs data constractor.
GADT


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
Phantom types


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
