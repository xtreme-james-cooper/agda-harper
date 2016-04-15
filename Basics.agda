module Basics where

open import Agda.Primitive

data Falsity : Set where

not : Set -> Set
not x = x -> Falsity

data Truth : Set where
  tt : Truth

data _==_ {i : Level} {A : Set i} (a : A) : A -> Set i where
  Refl : a == a

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL Refl #-}

sym : {A : Set} {a b : A} -> a == b -> b == a
sym Refl = Refl

funEq : {i j : Level} {A : Set i} {B : Set j} {a b : A} (f : A -> B) -> a == b -> f a == f b
funEq f Refl = Refl

data decide (A : Set) : Set where
  Yes : A -> decide A
  No : not A -> decide A

equals? : {A : Set} -> A -> A -> Set
equals? x y = decide (x == y)

data bool : Set where
  True : bool
  False : bool

boolEq : (x y : bool) -> equals? x y
boolEq True  True  = Yes Refl
boolEq True  False = No (λ ())
boolEq False True  = No (λ ())
boolEq False False = Yes Refl

data _\/_ (A B : Set) : Set where
  InL : A -> A \/ B
  InR : B -> A \/ B

pairEq : {A B : Set} -> ((a b : A) -> equals? a b) -> ((a b : B) -> equals? a b) -> (x y : A \/ B) -> equals? x y
pairEq A_eq B_eq (InL x) (InL y)  with A_eq x y
pairEq A_eq B_eq (InL x) (InL .x) | Yes Refl = Yes Refl
pairEq A_eq B_eq (InL x) (InL y)  | No npf   = No (neqInL npf)
  where
    neqInL : {A B : Set} {x y : A} -> not (x == y) -> not (InL {A} {B} x == InL y)
    neqInL npf Refl = npf Refl
pairEq A_eq B_eq (InL x) (InR y)  = No (λ ())
pairEq A_eq B_eq (InR x) (InL y)  = No (λ ())
pairEq A_eq B_eq (InR x) (InR y)  with B_eq x y
pairEq A_eq B_eq (InR x) (InR .x) | Yes Refl = Yes Refl
pairEq A_eq B_eq (InR x) (InR y)  | No npf    = No (neqInR npf)
  where
    neqInR : {A B : Set} {x y : B} -> not (x == y) -> not (InR {A} {B} x == InR y)
    neqInR npf Refl = npf Refl

data _*_ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) (b : B a) -> A * B

prodEq : {A : Set} {B : A -> Set} -> ((a b : A) -> equals? a b) -> ({c : A} (a b : B c) -> equals? a b) -> (x y : A * B) -> equals? x y
prodEq A_eq B_eq (a , b) (a' , b') with A_eq a a'
prodEq A_eq B_eq (a , b) (.a , b') | Yes Refl with B_eq b b'
prodEq A_eq B_eq (a , b) (.a , .b) | Yes Refl | Yes Refl = Yes Refl
prodEq A_eq B_eq (a , b) (.a , b') | Yes Refl | No npf   = No (neqSnd npf)
  where
    neqSnd : {A : Set} {B : A -> Set} {x : A} {y z : B x} -> not (y == z) -> not ((_,_ {A} {B} x y) == (x , z))
    neqSnd npf Refl = npf Refl
prodEq A_eq B_eq (a , b) (a' , b') | No npf   = No (neqFst npf)
  where
    neqFst : {A : Set} {B : A -> Set} {x y : A} {z : B x} {w : B y} -> not (x == y) -> not ((x , z) == (y , w))
    neqFst npf Refl = npf Refl

data option (A : Set) : Set where
  None : option A
  [_] : A -> option A

optEq : {A : Set} -> ((a b : A) -> equals? a b) -> (x y : option A) -> equals? x y
optEq A_eq None  None   = Yes Refl
optEq A_eq None  [ y ]  = No (λ ())
optEq A_eq [ x ] None   = No (λ ())
optEq A_eq [ x ] [ y ]  with A_eq x y
optEq A_eq [ x ] [ .x ] | Yes Refl = Yes Refl
optEq A_eq [ x ] [ y ]  | No npf   = No (neqSome npf)
  where
    neqSome : {A : Set} {x y : A} -> not (x == y) -> not ([ x ] == [ y ])
    neqSome npf Refl = npf Refl

data nat : Set where
  Zero : nat
  Suc : nat -> nat

natEq : (x y : nat) -> equals? x y
natEq Zero    Zero     = Yes Refl
natEq Zero    (Suc y)  = No (λ ())
natEq (Suc x) Zero     = No (λ ())
natEq (Suc x) (Suc y)  with natEq x y
natEq (Suc x) (Suc .x) | Yes Refl = Yes Refl
natEq (Suc x) (Suc y)  | No npf   = No (neqSuc npf)
  where    
    neqSuc : {x y : nat} -> not (x == y) -> not (Suc x == Suc y)
    neqSuc npf Refl = npf Refl



