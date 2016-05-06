module SimpleLambda.Term where

open import Basics
open import Fin
open import Vect
open import SimpleLambda.Type

data lam {n : nat} (gam : vect type n) : type -> Set where
  Var : {t : type} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)
  True : lam gam Bool
  False : lam gam Bool
  If : {t : type} -> lam gam Bool -> lam gam t -> lam gam t -> lam gam t

incr : {n : nat} {gam : vect type n} {t1 t2 : type} (x : fin (Suc n)) -> lam gam t2 -> lam (insertAt x gam t1) t2
incr {gam = gam} x (Var y Refl)   = Var (fincr x y) (insertAtFincr gam y x _)
incr             x (App e1 e2)    = App (incr x e1) (incr x e2)
incr             x (Abs e)        = Abs (incr (FS x) e)
incr             x True           = True
incr             x False          = False
incr             x (If b t f)     = If (incr x b) (incr x t) (incr x f) 

subst : {n : nat} {gam : vect type n} {t1 t2 : type} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
subst                       x (Var y pf)    v with finEq y x
subst {gam = gam} {t1 = t1} x (Var .x Refl) v | Yes Refl rewrite lookupInsertAt gam x t1 = v
subst                       x (Var y pf)    v | No npf   = Var (fdecr x y npf) (insertAtFdecr npf pf)
subst                       x (App e1 e2)   v = App (subst x e1 v) (subst x e2 v)
subst                       x (Abs e)       v = Abs (subst (fincr FZ x) e (incr FZ v))
subst                       x True          v = True
subst                       x False         v = False
subst                       x (If b t f)    v = If (subst x b v) (subst x t v) (subst x f v)
