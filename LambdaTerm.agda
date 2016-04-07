module LambdaTerm where

open import Basics
open import LambdaType

data direction : Set where
  L : direction
  R : direction

proj : {A : Set} -> direction -> A -> A -> A
proj L t1 t2 = t1
proj R t1 t2 = t2

data lam {n tn : nat} (gam : vect (type tn) n) : type tn -> Set where
  Var : {t : type tn} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type tn} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type tn} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)
  Triv : lam gam Unit
  Pair : {t1 t2 : type tn} -> lam gam t1 -> lam gam t2 -> lam gam (t1 X t2)
  Proj : {t1 t2 : type tn} (d : direction) -> lam gam (t1 X t2) -> lam gam (proj d t1 t2)
  Abort : {t : type tn} -> lam gam Void -> lam gam t
  Inj : {t1 t2 : type tn} (d : direction) -> lam gam (proj d t1 t2) -> lam gam (t1 + t2)
  Case : {t1 t2 t : type tn} -> lam gam (t1 + t2) -> lam (t1 :: gam) t -> lam (t2 :: gam) t -> lam gam t
  Map : {rh rh' : type tn} (t : type (Suc tn)) (pf : postype FZ t) -> lam (rh :: gam) rh' -> lam gam (tsubst FZ t pf rh) -> 
    lam gam (tsubst FZ t pf rh')
  Fold : {t : type (Suc tn)} (pf : postype FZ t) -> lam gam (tsubst FZ t pf (Ind t)) -> lam gam (Ind t)
  Rec : {t : type (Suc tn)} {t2 : type tn} (pf : postype FZ t) -> lam (tsubst FZ t pf t2 :: gam) t2 -> lam gam (Ind t) -> lam gam t2
  Unfold : {t : type (Suc tn)} (pf : postype FZ t) -> lam gam (CoInd t) -> lam gam (tsubst FZ t pf (CoInd t))
  Gen : {t : type (Suc tn)} {t2 : type tn} (pf : postype FZ t) -> lam (t2 :: gam) (tsubst FZ t pf t2) -> lam gam t2 -> lam gam (CoInd t)

incr : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam gam t2 -> lam  (insertAt x gam t1) t2
incr {gam = gam} x (Var y (Refl .(gam ! y))) = Var (fincr y x) (insertAtFincr gam y x _)
incr             x (App e1 e2)               = App (incr x e1) (incr x e2)
incr             x (Abs e)                   = Abs (incr (fincr x FZ) e)
incr             x Triv                      = Triv
incr             x (Pair e1 e2)              = Pair (incr x e1) (incr x e2)
incr             x (Proj d e)                = Proj d (incr x e)
incr             x (Abort e)                 = Abort (incr x e)
incr             x (Inj d e)                 = Inj d (incr x e)
incr             x (Case e el er)            = Case (incr x e) (incr (fincr x FZ) el) (incr (fincr x FZ) er)
incr             x (Map t pf e0 e)           = Map t pf (incr (fincr x FZ) e0) (incr x e)
incr             x (Fold pf e)               = Fold pf (incr x e)
incr             x (Rec pf e0 e)             = Rec pf (incr (fincr x FZ) e0) (incr x e)
incr             x (Unfold pf e)             = Unfold pf (incr x e)
incr             x (Gen pf e0 e)             = Gen pf (incr (fincr x FZ) e0) (incr x e)

subst : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
subst x (Var y pf)         v with fin_eq y x
subst x (Var .x (Refl ._)) v | Yes (Refl .x) = v castTo (funEq (lam _) (flip (lookupInsertAt _ x _)))
subst x (Var y pf)         v | No npf        = Var (fdecr y x npf) (insertAtFdecr npf pf)
subst x (App e1 e2)        v = App (subst x e1 v) (subst x e2 v)
subst x (Abs e)            v = Abs (subst (fincr x FZ) e (incr FZ v))
subst x Triv               v = Triv
subst x (Pair e1 e2)       v = Pair (subst x e1 v) (subst x e2 v)
subst x (Proj d e)         v = Proj d (subst x e v)
subst x (Abort e)          v = Abort (subst x e v)
subst x (Inj d e)          v = Inj d (subst x e v)
subst x (Case e el er)     v = Case (subst x e v) (subst (fincr x FZ) el (incr FZ v)) (subst (fincr x FZ) er (incr FZ v))
subst x (Map t pf e0 e)    v = Map t pf (subst (fincr x FZ) e0 (incr FZ v)) (subst x e v)
subst x (Fold pf e)        v = Fold pf (subst x e v)
subst x (Rec pf e0 e)      v = Rec pf (subst (fincr x FZ) e0 (incr FZ v)) (subst x e v)
subst x (Unfold pf e)      v = Unfold pf (subst x e v)
subst x (Gen pf e0 e)      v = Gen pf (subst (fincr x FZ) e0 (incr FZ v)) (subst x e v)
