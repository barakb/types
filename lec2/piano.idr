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


-- writing a polymorphic version of EqNat
data SameSame : a -> b -> Type where
  Same : SameSame s s
{-
  the (SameSame 3 3) Same
  
-}
||| * a proof that 1 + 1 = 2
proof1 : (1 + 1) `SameSame` 2
proof1 = Same

||| Proofs that `n` is less than or equal to `m`
||| @ n the smaller number
||| @ m the larger number
data LTE' : (n, m : Nat) -> Type where
  LTEZero' : LTE' Z right
  LTESucc' : LTE' left right -> LTE' (S left) (S right)

||| Greater than or equal to
total 
GTE' : Nat -> Nat -> Type
GTE' left right = LTE' right left

||| Strict greater than
total 
GT' : Nat -> Nat -> Type
GT' left right = GTE' (S left) right 

||| Strict less than
total
LT' : Nat -> Nat -> Type
LT' left right = GT' right left 


||| If two numbers are ordered, their predecessors are too
total
fromLteSucc' : (S m `LTE'` S n) -> (m `LTE'` n)
fromLteSucc' (LTESucc' prf) = prf

total
successNotLTEZero' : LTE' (S k) 0 -> Void
successNotLTEZero' LTEZero' impossible
successNotLTEZero' (LTESucc' _) impossible

||| A decision procedure for `LTE'`
total
isLTE' : (m, n : Nat) -> Dec (m `LTE'` n)
isLTE' Z n = Yes LTEZero'
isLTE' (S k) Z = No successNotLTEZero'
isLTE' (S k) (S j) = case isLTE' k j of
                         Yes prf => Yes (LTESucc' prf)
                         No contra => No (contra . fromLteSucc')


||| `LTE'` is reflexive.
lteRefl' : LTE' n n
lteRefl' {n = Z} = LTEZero'
lteRefl' {n = (S k)} = LTESucc' lteRefl'

