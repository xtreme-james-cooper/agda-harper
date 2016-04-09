module LambdaType where

open import Basics

data type (tn : nat) : Set where
  TyVar : fin tn -> type tn
  _=>_ : type tn -> type tn -> type tn
  Forall : type (Suc tn) -> type tn

tincr : {tn : nat} -> fin (Suc tn) -> type tn -> type (Suc tn)
tincr x (TyVar y) = TyVar (fincr y x)
tincr x (t1 => t2) = tincr x t1 => tincr x t2
tincr x (Forall t) = Forall (tincr (FS x) t)

tsubst : {tn : nat} -> fin (Suc tn) -> type tn -> type (Suc tn) -> type tn
tsubst tv v (TyVar tv') with fin_eq tv' tv
tsubst tv v (TyVar .tv) | Yes Refl = v
tsubst tv v (TyVar tv') | No npf   = TyVar (fdecr tv' tv npf)
tsubst tv v (t1 => t2)  = tsubst tv v t1 => tsubst tv v t2
tsubst tv v (Forall t)  = Forall (tsubst (FS tv) (tincr FZ v) t)

tsubstIncr : (tn : nat) (t1 : type tn) (t2 : type (Suc tn)) (x : fin (Suc tn)) -> tsubst FZ (tincr x t1) (tincr (FS x) t2) == tincr x (tsubst FZ t1 t2)
tsubstIncr tn t1 (TyVar FZ) x = Refl
tsubstIncr tn t1 (TyVar (FS y)) x = {!!}
tsubstIncr tn t1 (t21 => t22) x rewrite tsubstIncr tn t1 t21 x | tsubstIncr tn t1 t22 x = Refl
tsubstIncr tn t1 (Forall t2) x = {!!}

--tsubstSwap : {tn : nat} (y : fin tn) (x : fin (Suc tn)) (pf : fle y x) (t1 : type (Suc (Suc tn))) (t2 : type (Suc tn)) (t3 : type tn) -> 
--  tsubst FZ (tsubst x t3 t2) (tsubst (FS x) (tincr FZ t3) t1) == tsubst x t3 (tsubst FZ t2 t1)
--tsubstSwap y x pf (TyVar z)    t2 t3 = {!!}
--tsubstSwap y x pf (t11 => t12) t2 t3 rewrite tsubstSwap y x pf t11 t2 t3 | tsubstSwap y x pf t12 t2 t3 = Refl
--tsubstSwap y x pf (Forall t1)  t2 t3 = {!!}
