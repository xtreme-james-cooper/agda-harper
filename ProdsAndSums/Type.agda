module ProdsAndSums.Type where

open import Basics
open import Vect

data type : Set where
  Tuple : {n : nat} -> vect type n -> type
  _=>_ : type -> type -> type

unitT : type
unitT = Tuple []
