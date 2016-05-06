module SimpleLambda.Type where

open import Basics
open import Fin

data type : Set where
  Bool : type
  _=>_ : type -> type -> type
