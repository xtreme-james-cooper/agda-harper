module LambdaTerm where

open import Basics
open import LambdaType

data lam {n tn : nat} (gam : vect (type tn) n) : type tn -> Set where
  Var : {t : type tn} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type tn} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type tn} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)
  TApp : {t1 : type (Suc tn)} -> lam gam (Forall t1) -> (t2 : type tn) {t3 : type tn} -> tsubst FZ t2 t1 == t3 -> lam gam t3
  TAbs : {t : type (Suc tn)} {gam' : vect (type (Suc tn)) n} -> lam gam' t -> map (tincr FZ) gam == gam' -> lam gam (Forall t)

teincr : {n tn : nat} {t : type tn} {gam : vect (type tn) n} (x : fin (Suc tn)) -> lam gam t -> lam (map (tincr x) gam) (tincr x t)
teincr {gam = gam} x (Var y Refl)    = Var y (mapLookup (tincr x) gam y)
teincr             x (App e1 e2)     = App (teincr x e1) (teincr x e2)
teincr             x (Abs e)         = Abs (teincr x e)
teincr             x (TApp e t Refl) = TApp (teincr x e) (tincr x t) {!!} 
teincr             x (TAbs e pf)     = TAbs (teincr (FS x) e) {!!}

tesubst : {n tn : nat} {t1 : type (Suc tn)} {gam : vect (type (Suc tn)) n} (x : fin (Suc tn)) -> lam gam t1 -> (t2 : type tn) -> 
  lam (map (tsubst x t2) gam) (tsubst x t2 t1)
tesubst {gam = gam} x (Var y Refl) t2 = Var y (mapLookup (tsubst x t2) gam y)
tesubst             x (App e1 e2)  t2 = App (tesubst x e1 t2) (tesubst x e2 t2)
tesubst             x (Abs e)      t2 = Abs (tesubst x e t2)
tesubst {n} {tn} {.(tsubst FZ t t1)} {gam} x (TApp {t1} e t Refl)   t2 = TApp {t1 = {!!}} {!!} (tsubst x t2 t) {!!}
tesubst             x (TAbs e pf)  t2 = TAbs {!!} {!!}

incr : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam gam t2 -> lam (insertAt x gam t1) t2
incr {gam = gam} x (Var y Refl)  = Var (fincr y x) (insertAtFincr gam y x _)
incr             x (App e1 e2)   = App (incr x e1) (incr x e2)
incr             x (Abs e)       = Abs (incr (FS x) e)
incr             x (TApp e t pf) = TApp (incr x e) t pf
incr {gam = gam} x (TAbs e pf)   = TAbs (incr {!!} {!!}) {!!}

subst : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
subst                       x (Var y pf)    v with fin_eq y x
subst {gam = gam} {t1 = t1} x (Var .x Refl) v | Yes Refl rewrite lookupInsertAt gam x t1 = v
subst                       x (Var y pf)    v | No npf   = Var (fdecr y x npf) (insertAtFdecr npf pf)
subst                       x (App e1 e2)   v = App (subst x e1 v) (subst x e2 v)
subst                       x (Abs e)       v = Abs (subst (fincr x FZ) e (incr FZ v))
subst                       x (TApp e t pf) v = TApp (subst x e v) t pf
subst {n} {tn} {gam} {t1}   x (TAbs {t} {.(map (tincr FZ) (insertAt x gam t1))} e Refl) v = 
  TAbs (subst {gam = map (tincr FZ) gam} {tincr FZ t1} x {!!} (teincr FZ v)) Refl

