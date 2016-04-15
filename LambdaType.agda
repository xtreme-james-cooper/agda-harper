module LambdaType where

open import Basics
open import Fin

data type (tn : nat) : Set where
  TyVar : fin tn -> type tn
  _=>_ : type tn -> type tn -> type tn
  Forall : type (Suc tn) -> type tn

tincr : {tn : nat} -> fin (Suc tn) -> type tn -> type (Suc tn)
tincr x (TyVar y) = TyVar (fincr y x)
tincr x (t1 => t2) = tincr x t1 => tincr x t2
tincr x (Forall t) = Forall (tincr (FS x) t)

tincrSwap : {tn : nat} (t : type tn) (x y : fin (Suc tn)) -> x >=F y -> tincr (weaken y) (tincr x t) == tincr (FS x) (tincr y t)
tincrSwap (TyVar tv) x y gt rewrite fincrSwap tv x y gt = Refl
tincrSwap (t1 => t2) x y gt rewrite tincrSwap t1 x y gt | tincrSwap t2 x y gt = Refl
tincrSwap (Forall t) x y gt rewrite tincrSwap t (FS x) (FS y) (S>=S gt) = Refl

tsubst : {tn : nat} -> fin (Suc tn) -> type tn -> type (Suc tn) -> type tn
tsubst tv v (TyVar tv') with finEq tv' tv
tsubst tv v (TyVar tv') | Yes pf = v
tsubst tv v (TyVar tv') | No npf = TyVar (fdecr tv' tv npf)
tsubst tv v (t1 => t2)  = tsubst tv v t1 => tsubst tv v t2
tsubst tv v (Forall t)  = Forall (tsubst (FS tv) (tincr FZ v) t)

tSubstIncrLemma : {n : nat} {y x : fin n} -> x >=F y -> not (FS x == weaken y)
tSubstIncrLemma Z>=Z      ()
tSubstIncrLemma S>=Z      ()
tSubstIncrLemma (S>=S gt) eq with tSubstIncrLemma gt (eqFSBackwards eq) 
tSubstIncrLemma (S>=S gt) eq | ()

tsubstIncr : {tn : nat} (t1 : type tn) (t2 : type (Suc tn)) (x y : fin (Suc tn)) -> x >=F y -> tsubst (weaken y) (tincr x t1) (tincr (FS x) t2) == tincr x (tsubst y t1 t2)
tsubstIncr t1 (TyVar tv)   x      y gt with finEq (fincr tv (FS x)) (weaken y) | finEq tv y
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | Yes eq2  = Refl
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   with (finComp x tv)
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   | Yes gt2 rewrite fincrAbove x tv gt2 with neq (weakenEq eq)
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   | Yes gt2 | ()
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   | No ngt  with finEq tv x
tsubstIncr t1 (TyVar .x)   x      y gt | Yes eq | No neq   | No ngt  | Yes Refl with ngt >=FRefl
tsubstIncr t1 (TyVar .x)   x      y gt | Yes eq | No neq   | No ngt  | Yes Refl | ()
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   | No ngt  | No neq2  with finTric x tv ngt neq2
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   | No ngt  | No neq2  | lt rewrite fincrBelow x tv lt neq2 with tSubstIncrLemma (fgtTrans tv x y lt gt) eq
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   | No ngt  | No neq2  | lt | ()
tsubstIncr t1 (TyVar .y)   x      y gt | No neq | Yes Refl rewrite fincrAbove x y gt with neq Refl
tsubstIncr t1 (TyVar .y)   x      y gt | No neq | Yes Refl | ()
tsubstIncr t1 (TyVar tv)   x      y gt | No neq | No neq2  rewrite fincrFdecrSwap x y tv neq neq2 gt = Refl
tsubstIncr t1 (t21 => t22) x      y gt rewrite tsubstIncr t1 t21 x y gt | tsubstIncr t1 t22 x y gt = Refl
tsubstIncr t1 (Forall t2)  FZ     y gt rewrite tincrSwap t1 FZ FZ Z>=Z | tsubstIncr (tincr FZ t1) t2 (FS FZ) (FS y) (S>=S gt) = Refl
tsubstIncr t1 (Forall t2)  (FS x) y gt rewrite tincrSwap t1 (FS x) FZ S>=Z | tsubstIncr (tincr FZ t1) t2 (FS (FS x)) (FS y) (S>=S gt) = Refl

--tsubstSwap : {tn : nat} (y : fin tn) (x : fin (Suc tn)) (pf : fle y x) (t1 : type (Suc (Suc tn))) (t2 : type (Suc tn)) (t3 : type tn) -> 
--  tsubst FZ (tsubst x t3 t2) (tsubst (FS x) (tincr FZ t3) t1) == tsubst x t3 (tsubst FZ t2 t1)
--tsubstSwap y x pf (TyVar z)    t2 t3 = {!!}
--tsubstSwap y x pf (t11 => t12) t2 t3 rewrite tsubstSwap y x pf t11 t2 t3 | tsubstSwap y x pf t12 t2 t3 = Refl
--tsubstSwap y x pf (Forall t1)  t2 t3 = {!!}
