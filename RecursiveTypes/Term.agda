module RecursiveTypes.Term where

open import Basics
open import Fin
open import Vect
open import RecursiveTypes.Type

data lam {n tn : nat} (gam : vect (type tn) n) : type tn -> Set
data rec {n tn : nat} (gam : vect (type tn) n) : {rn : nat} -> vect (type tn) rn -> Set
data pat {n tn : nat} (t : type tn) (gam : vect (type tn) n) : {pn : nat} -> vect (type tn) pn -> Set
data lam {n} {tn} gam where
  Var : {t : type tn} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type tn} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type tn} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)
  Let : {t1 t2 : type tn} -> lam gam t1 -> lam (t1 :: gam) t2 -> lam gam t2
  Tuple : {rn : nat} {ts : vect (type tn) rn} -> rec gam ts -> lam gam (Tuple ts)
  Proj : {rn : nat} {ts : vect (type tn) rn} -> lam gam (Tuple ts) -> (p : fin rn) -> lam gam (ts ! p)
  Variant : {pn : nat} {ts : vect (type tn) pn} (l : fin pn) -> lam gam (ts ! l) -> lam gam (Variant ts)
  Case : {pn : nat} {t : type tn} {ts : vect (type tn) pn} -> lam gam (Variant ts) -> pat t gam ts -> lam gam t
  Fold : {t : type (Suc tn)} -> lam gam (tsubst FZ (Rec t) t) -> lam gam (Rec t)
  Unfold : {t : type (Suc tn)} {t2 : type tn} -> lam gam (Rec t) -> tsubst FZ (Rec t) t == t2 -> lam gam t2
data rec {n} {tn} gam where
  Unit : rec gam []
  Field : {rn : nat} {t : type tn} {ts : vect (type tn) rn} -> lam gam t -> rec gam ts -> rec gam (t :: ts)
data pat {n} {tn} t gam where
  Fail : pat t gam []
  Match : {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} -> lam (t2 :: gam) t -> pat t gam ts -> pat t gam (t2 :: ts)

incr : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam gam t2 -> lam (insertAt x gam t1) t2
incrRec : {n tn rn : nat} {gam : vect (type tn) n} {t : type tn} {ts : vect (type tn) rn} (x : fin (Suc n)) -> rec gam ts -> rec (insertAt x gam t) ts
incrPat : {n tn pn : nat} {gam : vect (type tn) n} {t t2 : type tn} {ts : vect (type tn) pn} (x : fin (Suc n)) -> pat t gam ts -> pat t (insertAt x gam t2) ts
incr {gam = gam} x (Var y Refl)  = Var (fincr x y) (insertAtFincr gam y x _)
incr             x (App e1 e2)   = App (incr x e1) (incr x e2)
incr             x (Abs e)       = Abs (incr (FS x) e)
incr             x (Let e1 e2)   = Let (incr x e1) (incr (FS x) e2)
incr             x (Tuple rec)   = Tuple (incrRec x rec)
incr             x (Proj e p)    = Proj (incr x e) p
incr             x (Variant l e) = Variant l (incr x e)
incr             x (Case e ps)   = Case (incr x e) (incrPat x ps)
incr             x (Fold e)      = Fold (incr x e)
incr             x (Unfold e eq) = Unfold (incr x e) eq
incrRec x Unit        = Unit
incrRec x (Field e r) = Field (incr x e) (incrRec x r)
incrPat x Fail         = Fail
incrPat x (Match e ps) = Match (incr (FS x) e) (incrPat x ps)

subst : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
substRec : {n tn rn : nat} {gam : vect (type tn) n} {t : type tn} {ts : vect (type tn) rn} (x : fin (Suc n)) -> rec (insertAt x gam t) ts -> lam gam t -> rec gam ts
substPat : {n tn pn : nat} {gam : vect (type tn) n} {t t2 : type tn} {ts : vect (type tn) pn} (x : fin (Suc n)) -> pat t (insertAt x gam t2) ts -> lam gam t2 -> pat t gam ts
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
subst                       x (Fold e)      v = Fold (subst x e v)
subst                       x (Unfold e eq) v = Unfold (subst x e v) eq
substRec x Unit        v = Unit
substRec x (Field e r) v = Field (subst x e v) (substRec x r v)
substPat x Fail         v = Fail
substPat x (Match e ps) v = Match (subst (fincr FZ x) e (incr FZ v)) (substPat x ps v)

unitE : {n tn : nat} {gam : vect (type tn) n} -> lam gam unitT
unitE = Tuple Unit

abortE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} -> lam gam voidT -> lam gam t
abortE e = Case e Fail

