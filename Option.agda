module Option where

open import Basics

data option (A : Set) : Set where
  None : option A
  Some : A -> option A

extend : {A B : Set} (eq : equality A) -> A -> B -> (A -> option B) -> (A -> option B)
extend eq a b map a' with eq a a'
extend eq a b map .a | Yes Refl = Some b
extend eq a b map a' | No neq   = map a'

remove : {A B : Set} (eq : equality A) -> A -> (A -> option B) -> (A -> option B)
remove eq a map a' with eq a a'
remove eq a map .a | Yes Refl = None
remove eq a map a' | No neq   = map a'
