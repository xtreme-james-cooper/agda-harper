module ExtensionalEquality where

open import Agda.Primitive
open import Basics
open import Fin
open import Vect
open import Sets

data _==ₑₓ_ {i : Level} : {A : Set i} -> A -> A -> Set (lsuc i) where
  BaseEq : {A : Set i} (a b : A) -> a == b -> a ==ₑₓ b
  FunEq : {A B C : Set i} {eq : C == (A -> B)} (f g : C) -> ((a : A) -> cast f eq a ==ₑₓ cast g eq a) -> f ==ₑₓ g

equalityₑₓ : Set -> Set₁
equalityₑₓ A = (a b : A) -> decide (a ==ₑₓ b)

extensionalArgs : {A B : Set} (f g : A -> B) (a : A) -> f ==ₑₓ g -> f a ==ₑₓ g a
extensionalArgs {A} {B} f .f a (BaseEq .f .f Refl) = BaseEq (f a) (f a) Refl
extensionalArgs {A} {B} f g  a (FunEq .f .g eq)    = {!!}

finiteFunEqLemma : {A : Set} {n m : nat} (vals : vect A n) (nvals : vect A m) (v : A) -> 
  ((a : A) -> (a ∈ (v :: vals)) \/ (a ∈ nvals)) -> ((a' : A) -> (a' ∈ vals) \/ (a' ∈ (v :: nvals)))
finiteFunEqLemma vals nvals a complete a' with complete a'
finiteFunEqLemma vals nvals a complete a' | InL (FZ , mem)   = InR (FZ , mem)
finiteFunEqLemma vals nvals a complete a' | InL (FS n , mem) = InL (n , mem)
finiteFunEqLemma vals nvals a complete a' | InR (n , mem)    = InR (FS n , mem)

finiteFunEq' : {A B : Set} {n m : nat} (vals : vect A n) (nvals : vect A m) -> ((a : A) -> (a ∈ vals) \/ (a ∈ nvals)) -> equalityₑₓ B -> (f g : A -> B) -> 
  decide ((a : A) -> a ∈ vals -> f a ==ₑₓ g a)
finiteFunEq' []          nvals complete eqB f g = Yes (λ { a (() , mem) })
finiteFunEq' (a :: vals) nvals complete eqB f g with inspect (eqB (f a) (g a))
finiteFunEq' (a :: vals) nvals complete eqB f g | It (Yes eqa) eq with finiteFunEq' vals (a :: nvals) (finiteFunEqLemma vals nvals a complete) eqB f g 
finiteFunEq' (a :: vals) nvals complete eqB f g | It (Yes eqa) eq | Yes funEq = Yes (λ { .a (FZ , Refl) -> eqa ; a' (FS n , mem) -> funEq a' (n , mem) })
finiteFunEq' (a :: vals) nvals complete eqB f g | It (Yes eqa) eq | No funNeq = No (λ eqp -> funNeq (λ { a' (n , mem) -> eqp a' (FS n , mem) }))
finiteFunEq' (a :: vals) nvals complete eqB f g | It (No neqa) eq = No (λ eqp -> neqa (eqp a (FZ , Refl)))

finiteFunEq : {A B : Set} {n : nat} -> finite A -> equalityₑₓ B -> equalityₑₓ (A -> B)
finiteFunEq (a , (vals , finA)) eqB f g with finiteFunEq' vals [] (λ a' -> InL (finA a')) eqB f g
finiteFunEq (a , (vals , finA)) eqB f g | Yes eq = Yes (FunEq {eq = Refl} f g (λ a' -> eq a' (finA a')))
finiteFunEq (a , (vals , finA)) eqB f g | No neq = No (λ eq -> neq (λ { a (n , mem) -> extensionalArgs f g a eq }))

