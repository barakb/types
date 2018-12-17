module main

total
axiom1 : Nat
axiom1 = 0


data EqNat : (n1: Nat) -> (m1 : Nat) -> Type where
  SameNat : (n: Nat) -> EqNat n n
  
||| * For every natural number x, x = x. That is, equality is reflexive.
total
axiom2 : (n : Nat) -> EqNat n n
axiom2 n = SameNat n

||| * For all natural numbers x and y, if x = y, then y = x. That is, equality is symmetric.
total 
axiom3 : (n : Nat) -> (m : Nat) -> EqNat n m -> EqNat m n
axiom3 m m (SameNat m) = SameNat m


||| * For all natural numbers x, y and z, if x = y and y = z, then x = z. That is, equality is transitive.
total 
axiom4 : (n : Nat) -> (m : Nat) -> (p : Nat) -> EqNat n m -> EqNat m p -> EqNat n p
axiom4 m m m (SameNat m) (SameNat m) = SameNat m

||| * For every natural number n, S(n) is a natural number.
total
axiom5 : (n : Nat) -> Nat
axiom5 n = S n

||| * For all natural numbers m and n, m = n if and only if S(m) = S(n). That is, S is an injection.
total 
axiom61 : (n: Nat) -> (m : Nat) -> EqNat n m -> EqNat (S n) (S m)
axiom61 m m (SameNat m) = SameNat (S m)

total
axiom62 : (n : Nat) ->  (m : Nat) -> EqNat (S n) (S m) -> EqNat n m
axiom62 m m (SameNat (S m)) = SameNat m


||| * For every natural number n, S(n) = 0 is false. That is, there is no natural number whose successor is 0.
total
axiom7 : (n : Nat) -> EqNat (S n) 0 -> Void
axiom7 _ (SameNat _) impossible

