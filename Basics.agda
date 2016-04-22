module Basics where

open import Agda.Primitive

data Falsity : Set where

not : Set -> Set
not x = x -> Falsity

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

data _\/_ (A B : Set) : Set where
  InL : A -> A \/ B
  InR : B -> A \/ B

data _*_ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) (b : B a) -> A * B

data nat : Set where
  Zero : nat
  Suc : nat -> nat


