module ProdsAndSums.Term where

open import Basics
open import Fin
open import Vect
open import ProdsAndSums.Type

data lam {n : nat} (gam : vect type n) : type -> Set where
  Var : {t : type} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)
  Let : {t1 t2 : type} -> lam gam t1 -> lam (t1 :: gam) t2 -> lam gam t2
  Tuple : {tn : nat} {ts : vect type tn} -> ((i : fin tn) -> lam gam (ts ! i)) -> lam gam (Tuple ts)
  Proj : {tn : nat} {ts : vect type tn} -> lam gam (Tuple ts) -> (p : fin tn) -> lam gam (ts ! p)

incr : {n : nat} {gam : vect type n} {t1 t2 : type} (x : fin (Suc n)) -> lam gam t2 -> lam (insertAt x gam t1) t2
incr {gam = gam} x (Var y Refl)   = Var (fincr x y) (insertAtFincr gam y x _)
incr             x (App e1 e2)    = App (incr x e1) (incr x e2)
incr             x (Abs e)        = Abs (incr (FS x) e)
incr             x (Let e1 e2)    = Let (incr x e1) (incr (FS x) e2)
incr             x (Tuple es)     = Tuple (λ i -> incr x (es i))
incr             x (Proj e p)     = Proj (incr x e) p

subst : {n : nat} {gam : vect type n} {t1 t2 : type} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
subst                       x (Var y pf)    v with finEq y x
subst {gam = gam} {t1 = t1} x (Var .x Refl) v | Yes Refl rewrite lookupInsertAt gam x t1 = v
subst                       x (Var y pf)    v | No npf   = Var (fdecr x y npf) (insertAtFdecr npf pf)
subst                       x (App e1 e2)   v = App (subst x e1 v) (subst x e2 v)
subst                       x (Abs e)       v = Abs (subst (fincr FZ x) e (incr FZ v))
subst                       x (Let e1 e2)   v = Let (subst x e1 v) (subst (fincr FZ x) e2 (incr FZ v))
subst                       x (Tuple es)    v = Tuple (λ i -> subst x (es i) v)
subst                       x (Proj e p)    v = Proj (subst x e v) p

unitE : {n : nat} {gam : vect type n} -> lam gam unitT
unitE = Tuple (λ ())

