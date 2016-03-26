module Lambda where

open import Basics

data type : Set where
  Base : type
  _=>_ : type -> type -> type

data lam {n : nat} (gam : vect type n) : type -> Set where
  Var : {t : type} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)

incr : {n : nat} {gam : vect type n} {t1 t2 : type} (x : fin (Suc n)) -> lam gam t2 -> lam  (insertAt x gam t1) t2
incr {n} {gam} x (Var y (Refl .(gam ! y))) = Var (fincr y x) (insertAtFincr gam y x _)
incr           x (App e1 e2)               = App (incr x e1) (incr x e2)
incr           x (Abs e)                   = Abs (incr (fincr x FZ) e)

subst : {n : nat} {gam : vect type n} {t1 t2 : type} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
subst x (Var y pf)         v with fin_eq y x
subst x (Var .x (Refl ._)) v | Eq (Refl .x) = cast v (funEq (lam _) (flip (lookupInsertAt _ x _)))
subst x (Var y pf)         v | NEq npf      = Var (fdecr y x npf) (insertAtFdecr npf pf)
subst x (App e1 e2)        v = App (subst x e1 v) (subst x e2 v)
subst x (Abs e)            v = Abs (subst (fincr x FZ) e (incr FZ v))

data eval : {n : nat} {gam : vect type n} {t : type} -> lam gam t -> lam gam t -> Set where
  EvalApp1 : {n : nat} {gam : vect type n} {t1 t2 : type} {e1 e1' : lam gam (t1 => t2)} {e2 : lam gam t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvalApp2 : {n : nat} {gam : vect type n} {t1 t2 : type} {e1 : lam (t1 :: gam) t2} {e2 : lam gam t1} -> eval (App (Abs e1) e2) (subst FZ e1 e2)

data isVal {n : nat} {gam : vect type n} : {t : type} -> lam gam t -> Set where
  AbsVal : {t1 t2 : type} {e : lam (t2 :: gam) t1} -> isVal (Abs e)

evaluate : {t : type} (e : lam [] t) -> isVal e + (lam [] t * eval e)
evaluate (Var () pf)
evaluate (App e1            e2) with evaluate e1
evaluate (App (Var x pf)    e2) | InL ()
evaluate (App (App e11 e12) e2) | InL ()
evaluate (App (Abs e1)      e2) | InL AbsVal     = InR (subst FZ e1 e2 , EvalApp2)
evaluate (App e1            e2) | InR (e1' , ev) = InR (App e1' e2 , EvalApp1 ev)
evaluate (Abs e)                = InL AbsVal
