module Sets where

open import Basics
open import Vect

data powerset (A : Set) : {n : nat} -> vect A n -> Set where 
  EmptySet : powerset A []
  Insert : {n : nat} {as : vect A n} (a : A) -> powerset A as -> not (a ∈ as) -> powerset A (a :: as)

