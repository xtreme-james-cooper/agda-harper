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

-- inspect

record Reveal_·_is_ {a b : Level} {A : Set a} {B : A -> Set b} (f : (x : A) -> B x) (x : A) (y : B x) : Set (a ⊔ b) where
  constructor [_]
  field eq : f x == y

inspect : {a b : Level} {A : Set a} {B : A -> Set b} (f : (x : A) -> B x) (x : A) -> Reveal f · x is f x
inspect f x = [ Refl ]
