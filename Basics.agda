module Basics where

open import Agda.Primitive

data Falsity : Set where

not : {i : Level} -> Set i -> Set i
not x = x -> Falsity

data _==_ {i : Level} {A : Set i} (a : A) : A -> Set i where
  Refl : a == a

infix 40 _==_

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL Refl #-}

sym : {A : Set} {a b : A} -> a == b -> b == a
sym Refl = Refl

cast : {i : Level} {A B : Set i} -> A -> A == B -> B
cast a eq rewrite eq = a

funEq : {i j : Level} {A : Set i} {B : Set j} {a b : A} (f : A -> B) -> a == b -> f a == f b
funEq f Refl = Refl

data examineAndRemember {i : Level} {A : Set i} (x : A) : Set i where
  It : (y : A) -> x == y -> examineAndRemember x 

inspect : {i : Level} {A : Set i} (x : A) -> examineAndRemember x
inspect x = It x Refl 

data decide {i : Level} (A : Set i) : Set i where
  Yes : A -> decide A
  No : not A -> decide A

equality : Set -> Set
equality A = (a b : A) -> decide (a == b)

data _\/_ (A B : Set) : Set where
  InL : A -> A \/ B
  InR : B -> A \/ B

infix 30 _\/_

data _*_ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) (b : B a) -> A * B

infixr 30 _*_

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 30 _×_
infixr 20 _,_

data bool : Set where
  True : bool
  False : bool

boolEq : equality bool
boolEq True  True  = Yes Refl
boolEq True  False = No (λ ())
boolEq False True  = No (λ ())
boolEq False False = Yes Refl

_and_ : bool -> bool -> bool
True  and y = y
False and y = False

infix 70 _and_

andTrue : {b : bool} -> (b and True) == b
andTrue {True}  = Refl
andTrue {False} = Refl

andFalse : {b : bool} -> (b and False) == False
andFalse {True}  = Refl
andFalse {False} = Refl

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

data _>_ : nat -> nat -> Set where
  S>Z : {a : nat} -> Suc a > Zero
  S>S : {a b : nat} -> a > b -> Suc a > Suc b

infix 50 _>_ 

sucNrefl : {n : nat} -> not (n > n)
sucNrefl (S>S gt) = sucNrefl gt

sucGt : {n : nat} -> Suc n > n
sucGt {Zero}  = S>Z
sucGt {Suc n} = S>S sucGt

gtTrans : {n m p : nat} -> n > m -> m > p -> n > p
gtTrans (S>S gt1) S>Z       = S>Z
gtTrans (S>S gt1) (S>S gt2) = S>S (gtTrans gt1 gt2)



