module Lambda where

open import Basics

data type : Set where
  Base : type
  _=>_ : type -> type -> type

data lam {n : nat} (gam : vect type n) : type -> Set where
  Var : (x : fin n) -> lam gam (gam ! x) 
  App : {t1 t2 : type} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)



