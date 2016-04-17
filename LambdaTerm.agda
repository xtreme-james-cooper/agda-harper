module LambdaTerm where

open import Basics
open import Fin
open import Vect
open import LambdaType

data lam {n tn : nat} (gam : vect (type tn) n) : type tn -> Set where
  Var : {t : type tn} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type tn} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type tn} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)
  TApp : {t1 : type (Suc tn)} -> lam gam (Forall t1) -> (t2 : type tn) {t3 : type tn} -> tsubst FZ t2 t1 == t3 -> lam gam t3
  TAbs : {t : type (Suc tn)} {gam' : vect (type (Suc tn)) n} -> lam gam' t -> map (tincr FZ) gam == gam' -> lam gam (Forall t)

teincr : {n tn : nat} {t : type tn} {gam : vect (type tn) n} (x : fin (Suc tn)) -> lam gam t -> lam (map (tincr x) gam) (tincr x t)
teincr {gam = gam} x (Var y Refl)         = Var y (mapLookup (tincr x) gam y)
teincr             x (App e1 e2)          = App (teincr x e1) (teincr x e2)
teincr             x (Abs e)              = Abs (teincr x e)
teincr             x (TApp {t1} e t Refl) = TApp (teincr x e) (tincr x t) (tsubstIncr t t1 x FZ >=FZ)
teincr {gam = gam} x (TAbs e Refl)        = TAbs (teincr (FS x) e) (teincrLemma x gam)
  where
    teincrLemma : {n tn : nat} (x : fin (Suc tn)) (gam : vect (type tn) n) -> map (tincr FZ) (map (tincr x) gam) == map (tincr (FS x)) (map (tincr FZ) gam)
    teincrLemma x []         = Refl
    teincrLemma x (t :: gam) rewrite tincrSwap t x FZ >=FZ | teincrLemma x gam = Refl 

tesubst : {n tn : nat} {t1 : type (Suc tn)} {gam : vect (type (Suc tn)) n} (x : fin (Suc tn)) (t2 : type tn) -> lam gam t1 -> 
  lam (map (tsubst x t2) gam) (tsubst x t2 t1)
tesubst {gam = gam} x t2 (Var y Refl)         = Var y (mapLookup (tsubst x t2) gam y)
tesubst             x t2 (App e1 e2)          = App (tesubst x t2 e1) (tesubst x t2 e2)
tesubst             x t2 (Abs e)              = Abs (tesubst x t2 e)
tesubst {gam = gam} x t2 (TApp {t1} e t Refl) = TApp (tesubst x t2 e) (tsubst x t2 t) {!!}
tesubst {gam = gam} x t2 (TAbs {t} e Refl)    = TAbs (tesubst (FS x) (tincr FZ t2) e) (tesubstLemma x t2 gam)
  where
    tesubstLemma : {n tn : nat} (x : fin (Suc tn)) (t : type tn) (gam : vect (type (Suc tn)) n) -> 
      map (tincr FZ) (map (tsubst x t) gam) == map (tsubst (FS x) (tincr FZ t)) (map (tincr FZ) gam)
    tesubstLemma x t []          = Refl
    tesubstLemma x t (t1 :: gam) rewrite tesubstLemma x t gam = {!!}

incr : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam gam t2 -> lam (insertAt x gam t1) t2
incr {gam = gam} x (Var y Refl)   = Var (fincr y x) (insertAtFincr gam y x _)
incr             x (App e1 e2)    = App (incr x e1) (incr x e2)
incr             x (Abs e)        = Abs (incr (FS x) e)
incr             x (TApp e t pf)  = TApp (incr x e) t pf
incr {n} {tn} {gam} {t1} x (TAbs {t} e Refl) = TAbs (incr {n} {Suc tn} {map (tincr FZ) gam} {tincr FZ t1} x e) (mapInsertAt gam t1 (tincr FZ) x)

subst : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
subst                       x (Var y pf)    v with finEq y x
subst {gam = gam} {t1 = t1} x (Var .x Refl) v | Yes Refl rewrite lookupInsertAt gam x t1 = v
subst                       x (Var y pf)    v | No npf   = Var (fdecr y x npf) (insertAtFdecr npf pf)
subst                       x (App e1 e2)   v = App (subst x e1 v) (subst x e2 v)
subst                       x (Abs e)       v = Abs (subst (fincr x FZ) e (incr FZ v))
subst                       x (TApp e t pf) v = TApp (subst x e v) t pf
subst {n} {tn} {gam} {t1}   x (TAbs {t} {.(map (tincr FZ) (insertAt x gam t1))} e Refl) v rewrite mapInsertAt gam t1 (tincr FZ) x = 
  TAbs (subst {gam = map (tincr FZ) gam} {tincr FZ t1} x e (teincr FZ v)) Refl

