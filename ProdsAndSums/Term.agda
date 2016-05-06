module ProdsAndSums.Term where

open import Basics
open import Fin
open import Vect
open import ProdsAndSums.Type

data lam {n : nat} (gam : vect type n) : type -> Set
data rec {n : nat} (gam : vect type n) : {tn : nat} -> vect type tn -> Set
data pat {n : nat} (t : type) (gam : vect type n) : {tn : nat} -> vect type tn -> Set
data lam {n} gam where
  Var : {t : type} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)
  Let : {t1 t2 : type} -> lam gam t1 -> lam (t1 :: gam) t2 -> lam gam t2
  Tuple : {tn : nat} {ts : vect type tn} -> rec gam ts -> lam gam (Tuple ts)
  Proj : {tn : nat} {ts : vect type tn} -> lam gam (Tuple ts) -> (p : fin tn) -> lam gam (ts ! p)
  Variant : {tn : nat} {ts : vect type tn} (l : fin tn) -> lam gam (ts ! l) -> lam gam (Variant ts)
  Case : {tn : nat} {t : type} {ts : vect type tn} -> lam gam (Variant ts) -> pat t gam ts -> lam gam t
data rec {n} gam where
  Unit : rec gam []
  Field : {tn : nat} {t : type} {ts : vect type tn} -> lam gam t -> rec gam ts -> rec gam (t :: ts)
data pat {n} t gam where
  Fail : pat t gam []
  Match : {tn : nat} {t2 : type} {ts : vect type tn} -> lam (t2 :: gam) t -> pat t gam ts -> pat t gam (t2 :: ts)

incr : {n : nat} {gam : vect type n} {t1 t2 : type} (x : fin (Suc n)) -> lam gam t2 -> lam (insertAt x gam t1) t2
incrRec : {n tn : nat} {gam : vect type n} {t : type} {ts : vect type tn} (x : fin (Suc n)) -> rec gam ts -> rec (insertAt x gam t) ts
incrPat : {n tn : nat} {gam : vect type n} {t t2 : type} {ts : vect type tn} (x : fin (Suc n)) -> pat t gam ts -> pat t (insertAt x gam t2) ts
incr {gam = gam} x (Var y Refl)  = Var (fincr x y) (insertAtFincr gam y x _)
incr             x (App e1 e2)   = App (incr x e1) (incr x e2)
incr             x (Abs e)       = Abs (incr (FS x) e)
incr             x (Let e1 e2)   = Let (incr x e1) (incr (FS x) e2)
incr             x (Tuple rec)   = Tuple (incrRec x rec)
incr             x (Proj e p)    = Proj (incr x e) p
incr             x (Variant l e) = Variant l (incr x e)
incr             x (Case e ps)   = Case (incr x e) (incrPat x ps)
incrRec x Unit        = Unit
incrRec x (Field e r) = Field (incr x e) (incrRec x r)
incrPat x Fail         = Fail
incrPat x (Match e ps) = Match (incr (FS x) e) (incrPat x ps)

subst : {n : nat} {gam : vect type n} {t1 t2 : type} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
substRec : {n tn : nat} {gam : vect type n} {t : type} {ts : vect type tn} (x : fin (Suc n)) -> rec (insertAt x gam t) ts -> lam gam t -> rec gam ts
substPat : {n tn : nat} {gam : vect type n} {t t2 : type} {ts : vect type tn} (x : fin (Suc n)) -> pat t (insertAt x gam t2) ts -> lam gam t2 -> pat t gam ts
subst                       x (Var y pf)    v with finEq y x
subst {gam = gam} {t1 = t1} x (Var .x Refl) v | Yes Refl rewrite lookupInsertAt gam x t1 = v
subst                       x (Var y pf)    v | No npf   = Var (fdecr x y npf) (insertAtFdecr npf pf)
subst                       x (App e1 e2)   v = App (subst x e1 v) (subst x e2 v)
subst                       x (Abs e)       v = Abs (subst (fincr FZ x) e (incr FZ v))
subst                       x (Let e1 e2)   v = Let (subst x e1 v) (subst (fincr FZ x) e2 (incr FZ v))
subst                       x (Tuple rec)   v = Tuple (substRec x rec v)
subst                       x (Proj e p)    v = Proj (subst x e v) p
subst                       x (Variant l e) v = Variant l (subst x e v)
subst                       x (Case e ps)   v = Case (subst x e v) (substPat x ps v)
substRec x Unit        v = Unit
substRec x (Field e r) v = Field (subst x e v) (substRec x r v)
substPat x Fail         v = Fail
substPat x (Match e ps) v = Match (subst (fincr FZ x) e (incr FZ v)) (substPat x ps v)

unitE : {n : nat} {gam : vect type n} -> lam gam unitT
unitE = Tuple Unit

abortE : {n : nat} {gam : vect type n} {t : type} -> lam gam voidT -> lam gam t
abortE e = Case e Fail
