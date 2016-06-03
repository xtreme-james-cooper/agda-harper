module Nat where

open import Basics

data nat : Set where
  Zero : nat
  Suc : nat -> nat

neqS : (a b : nat) -> not (a == b) -> not (Suc a == Suc b)
neqS a .a neq Refl = neq Refl

natEq : equality nat
natEq Zero    Zero     = Yes Refl
natEq Zero    (Suc b)  = No (λ ())
natEq (Suc a) Zero     = No (λ ())
natEq (Suc a) (Suc b)  with natEq a b
natEq (Suc a) (Suc .a) | Yes Refl = Yes Refl
natEq (Suc a) (Suc b)  | No neq = No (neqS a b neq)

_+_ : nat -> nat -> nat
Zero  + m = m
Suc n + m = Suc (n + m)

infix 70 _+_

plusSuc : (n m : nat) -> n + Suc m == Suc (n + m)
plusSuc Zero    m = Refl
plusSuc (Suc n) m rewrite plusSuc n m = Refl

plusZero : (n : nat) -> n + Zero == n
plusZero Zero    = Refl
plusZero (Suc n) rewrite plusZero n = Refl

data _>_ : nat -> nat -> Set where
  S>Z : (a : nat) -> Suc a > Zero
  S>S : (a b : nat) -> a > b -> Suc a > Suc b

infix 50 _>_ 

sucNrefl : {n : nat} -> not (n > n)
sucNrefl (S>S n .n gt) = sucNrefl gt

sucGt : {n : nat} -> Suc n > n
sucGt {Zero}  = S>Z Zero
sucGt {Suc n} = S>S (Suc n) n sucGt

gtTrans : {n m p : nat} -> n > m -> m > p -> n > p
gtTrans (S>S n _ gt1) (S>Z _)        = S>Z n
gtTrans (S>S n m gt1) (S>S .m p gt2) = S>S n p (gtTrans gt1 gt2)

gtPlusBefore : {n m : nat} (p : nat) -> n > m -> p + n > p + m
gtPlusBefore p (S>Z n)      rewrite plusSuc p n | plusZero p = lemma p n
  where
    lemma : (n m : nat) -> Suc (n + m) > n
    lemma Zero    m = S>Z m
    lemma (Suc n) m = S>S (Suc (n + m)) n (lemma n m)
gtPlusBefore p (S>S n m gt) rewrite plusSuc p n | plusSuc p m = S>S (p + n) (p + m) (gtPlusBefore p gt)

gtPlusAfter : {n m : nat} (p : nat) -> n > m -> n + p > m + p
gtPlusAfter p (S>Z n)      = lemma n p
  where
    lemma : (n m : nat) -> Suc (n + m) > m
    lemma n Zero    = S>Z (n + Zero)
    lemma n (Suc m) rewrite plusSuc n m = S>S (Suc (n + m)) m (lemma n m)
gtPlusAfter p (S>S n m gt) = S>S (n + p) (m + p) (gtPlusAfter p gt)

gtPlusBoth : {n m p q : nat} -> n > m -> p > q -> n + p > m + q
gtPlusBoth (S>Z n)       (S>Z p)         = S>Z (n + Suc p)
gtPlusBoth (S>Z n)       (S>S p q gt2) rewrite plusSuc n p = S>S (Suc (n + p)) q (lemma n p q gt2)
  where
    lemma : (n p q : nat) -> p > q -> Suc (n + p) > q
    lemma n _ _ (S>Z p)        = S>Z (n + Suc p)
    lemma n _ _ (S>S p q gt) rewrite plusSuc n p = S>S (Suc (n + p)) q (lemma n p q gt)
gtPlusBoth (S>S n m gt1) (S>Z p)       rewrite plusZero m | plusSuc n p = S>S (Suc (n + p)) m (lemma n m p gt1)
  where
    lemma : (n m p : nat) -> n > m -> Suc (n + p) > m
    lemma _ _ p (S>Z n) = S>Z (Suc (n + p))
    lemma _ _ p (S>S n m gt) = S>S (Suc (n + p)) m (lemma n m p gt)
gtPlusBoth (S>S n m gt1) (S>S p q gt2) rewrite plusSuc n p | plusSuc m q = S>S (Suc (n + p)) (Suc (m + q)) (S>S (n + p) (m + q) (gtPlusBoth gt1 gt2))
