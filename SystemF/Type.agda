module SystemF.Type where

open import Basics
open import Fin

data type (tn : nat) : Set where
  TyVar : fin tn -> type tn
  _=>_ : type tn -> type tn -> type tn
  Forall : type (Suc tn) -> type tn

tincr : {tn : nat} -> fin (Suc tn) -> type tn -> type (Suc tn)
tincr x (TyVar y) = TyVar (fincr x y)
tincr x (t1 => t2) = tincr x t1 => tincr x t2
tincr x (Forall t) = Forall (tincr (FS x) t)

tincrSwap : {tn : nat} (t : type tn) (x y : fin (Suc tn)) -> x >=F y -> tincr (weaken y) (tincr x t) == tincr (FS x) (tincr y t)
tincrSwap (TyVar tv) x y gt rewrite fincrSwap tv x y gt = Refl
tincrSwap (t1 => t2) x y gt rewrite tincrSwap t1 x y gt | tincrSwap t2 x y gt = Refl
tincrSwap (Forall t) x y gt rewrite tincrSwap t (FS x) (FS y) (S>=S gt) = Refl

tsubst : {tn : nat} -> fin (Suc tn) -> type tn -> type (Suc tn) -> type tn
tsubst tv v (TyVar tv') with finEq tv' tv
tsubst tv v (TyVar tv') | Yes pf = v
tsubst tv v (TyVar tv') | No npf = TyVar (fdecr tv tv' npf)
tsubst tv v (t1 => t2)  = tsubst tv v t1 => tsubst tv v t2
tsubst tv v (Forall t)  = Forall (tsubst (FS tv) (tincr FZ v) t)

tSubstIncrLemma : {n : nat} {y x : fin n} -> x >=F y -> not (FS x == weaken y)
tSubstIncrLemma Z>=Z      ()
tSubstIncrLemma S>=Z      ()
tSubstIncrLemma (S>=S gt) eq with tSubstIncrLemma gt (eqFS eq) 
tSubstIncrLemma (S>=S gt) eq | ()

tsubstIncr : {tn : nat} (t1 : type tn) (t2 : type (Suc tn)) (x y : fin (Suc tn)) -> x >=F y ->
  tsubst (weaken y) (tincr x t1) (tincr (FS x) t2) == tincr x (tsubst y t1 t2)
tsubstIncr t1 (TyVar tv)   x      y gt with finEq (fincr (FS x) tv) (weaken y) | finEq tv y
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | Yes eq2  = Refl
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   with finComp x tv
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   | GT gt2 neq2 nlt rewrite fincrAbove x tv gt2 with neq (weakenEq eq)
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   | GT gt2 neq2 nlt | ()
tsubstIncr t1 (TyVar .x)   x      y gt | Yes eq | No neq   | EQ ngt Refl nlt rewrite fincrAbove x x >=FRefl | weakenEq eq with neq Refl
tsubstIncr t1 (TyVar .x)   x      y gt | Yes eq | No neq   | EQ ngt Refl nlt | ()
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   | LT ngt neq2 lt 
  rewrite fincrBelow x tv lt (λ eq -> neq2 (sym eq)) with tSubstIncrLemma (fgtTrans lt gt) eq
tsubstIncr t1 (TyVar tv)   x      y gt | Yes eq | No neq   | LT ngt neq2 lt | ()
tsubstIncr t1 (TyVar .y)   x      y gt | No neq | Yes Refl rewrite fincrAbove x y gt with neq Refl
tsubstIncr t1 (TyVar .y)   x      y gt | No neq | Yes Refl | ()
tsubstIncr t1 (TyVar tv)   x      y gt | No neq | No neq2  rewrite fincrFdecrSwap x y tv neq neq2 gt = Refl
tsubstIncr t1 (t21 => t22) x      y gt rewrite tsubstIncr t1 t21 x y gt | tsubstIncr t1 t22 x y gt = Refl
tsubstIncr t1 (Forall t2)  FZ     y gt rewrite tincrSwap t1 FZ FZ Z>=Z | tsubstIncr (tincr FZ t1) t2 (FS FZ) (FS y) (S>=S gt) = Refl
tsubstIncr t1 (Forall t2)  (FS x) y gt rewrite tincrSwap t1 (FS x) FZ S>=Z | tsubstIncr (tincr FZ t1) t2 (FS (FS x)) (FS y) (S>=S gt) = Refl

tincrSubstLemma : {tn : nat} {x y : fin (Suc tn)} -> weaken x == FS y -> not (y >=F x)
tincrSubstLemma {tn}     {FZ}    {FZ}   () Z>=Z
tincrSubstLemma {tn}     {FZ}    {FS y} () S>=Z
tincrSubstLemma {Zero}   {FS ()} {FS y} eq (S>=S gt)
tincrSubstLemma {Suc tn} {FS x}  {FS y} eq (S>=S gt) = tincrSubstLemma {tn} {x} {y} (eqFS eq) gt

tincrSubst : {tn : nat} (t1 : type tn) (t2 : type (Suc tn)) (x y : fin (Suc tn)) -> y >=F x ->
  tsubst (FS y) (tincr x t1) (tincr (weaken x) t2) == tincr x (tsubst y t1 t2)
tincrSubst t1 (TyVar tv)   x y lt with finEq (fincr (weaken x) tv) (FS y) | finEq tv y 
tincrSubst t1 (TyVar tv)   x y lt | Yes eq  | Yes eq2 = Refl
tincrSubst t1 (TyVar tv)   x y lt | Yes eq  | No neq2 with finComp tv x 
tincrSubst t1 (TyVar tv)   x y lt | Yes eq  | No neq2 | GT gt neq3 nlt  rewrite fincrBelow' x tv gt with neq2 (eqFS eq)
tincrSubst t1 (TyVar tv)   x y lt | Yes eq  | No neq2 | GT gt neq3 nlt  | ()
tincrSubst t1 (TyVar .x)   x y lt | Yes eq  | No neq2 | EQ ngt Refl nlt rewrite fincrBelow' x x >=FRefl with neq2 (eqFS eq)
tincrSubst t1 (TyVar .x)   x y lt | Yes eq  | No neq2 | EQ ngt Refl nlt | ()
tincrSubst t1 (TyVar tv)   x y lt | Yes eq  | No neq2 | LT ngt neq3 lt2 rewrite fincrAbove' x tv lt2 neq3 with tincrSubstLemma eq (fgtTrans lt lt2)
tincrSubst t1 (TyVar tv)   x y lt | Yes eq  | No neq2 | LT ngt neq3 lt2 | ()
tincrSubst t1 (TyVar .y)   x y lt | No neq2 | Yes Refl with neq2 (fincrBelow' x y lt)
tincrSubst t1 (TyVar .y)   x y lt | No neq2 | Yes Refl | ()
tincrSubst t1 (TyVar tv)   x y lt | No neq2 | No neq3 rewrite fincrFdecrSwap' x y tv neq2 neq3 lt = Refl
tincrSubst t1 (t21 => t22) x y lt rewrite tincrSubst t1 t21 x y lt | tincrSubst t1 t22 x y lt = Refl
tincrSubst t1 (Forall t2)  x y lt rewrite tincrSwap t1 x FZ >=FZ | tincrSubst (tincr FZ t1) t2 (FS x) (FS y) (S>=S lt) = Refl

tsubstIncrRefl : {tn : nat} (t t2 : type tn) (x : fin (Suc tn)) -> tsubst x t2 (tincr x t) == t
tsubstIncrRefl (TyVar tv)   t2 x with finEq (fincr x tv) x 
tsubstIncrRefl (TyVar tv)   t2 x | Yes eq with fincrNeq x tv eq
tsubstIncrRefl (TyVar tv)   t2 x | Yes eq | ()
tsubstIncrRefl (TyVar tv)   t2 x | No neq rewrite fdecrFincrRefl x tv neq = Refl
tsubstIncrRefl (t11 => t12) t2 x rewrite tsubstIncrRefl t11 t2 x | tsubstIncrRefl t12 t2 x = Refl
tsubstIncrRefl (Forall t)   t2 x rewrite tsubstIncrRefl t (tincr FZ t2) (FS x) = Refl

tsubstSwapLemma : {tn : nat} {x y : fin (Suc tn)} {z : fin (Suc (Suc tn))} (neq : not (z == FS x)) -> fdecr (FS x) z neq == y -> x >=F y -> z == weaken y
tsubstSwapLemma {tn}     {FZ}    {FZ}   {FZ}        neq eq Z>=Z      = Refl
tsubstSwapLemma {tn}     {FZ}    {FZ}   {FS FZ}     neq () Z>=Z     
tsubstSwapLemma {tn}     {FZ}    {FZ}   {FS (FS z)} neq () Z>=Z      
tsubstSwapLemma {tn}     {FS x}  {FZ}   {FZ}        neq eq S>=Z      = Refl
tsubstSwapLemma {tn}     {FS x}  {FZ}   {FS z}      neq () S>=Z      
tsubstSwapLemma {tn}     {FS x}  {FS y} {FZ}        neq () (S>=S gt)
tsubstSwapLemma {Zero}   {FS ()} {FS y} {FS z}      neq eq (S>=S gt)
tsubstSwapLemma {Suc tn} {FS x}  {FS y} {FS z}      neq eq (S>=S gt) rewrite tsubstSwapLemma {tn} {x} {y} {z} (neqFS neq) (eqFS eq) gt = Refl

tsubstSwapLemma2 : {tn : nat} {x y : fin (Suc tn)} {z : fin (Suc (Suc tn))} (neq : not (z == weaken y)) -> fdecr (weaken y) z neq == x -> x >=F y -> z == FS x
tsubstSwapLemma2 {tn}     {FZ}    {FZ}   {FZ}         neq eq   Z>=Z      with neq Refl
tsubstSwapLemma2 {tn}     {FZ}    {FZ}   {FZ}         neq eq   Z>=Z      | ()
tsubstSwapLemma2 {tn}     {FZ}    {FZ}   {FS .FZ}     neq Refl Z>=Z      = Refl
tsubstSwapLemma2 {tn}     {FS x}  {FZ}   {FZ}         neq eq   S>=Z      with neq Refl
tsubstSwapLemma2 {tn}     {FS x}  {FZ}   {FZ}         neq eq   S>=Z      | ()
tsubstSwapLemma2 {tn}     {FS x}  {FZ}   {FS .(FS x)} neq Refl S>=Z      = Refl
tsubstSwapLemma2 {tn}     {FS x}  {FS y} {FZ}         neq ()   (S>=S gt)
tsubstSwapLemma2 {Zero}   {FS ()} {FS y} {FS z}       neq eq   (S>=S gt)
tsubstSwapLemma2 {Suc tn} {FS x}  {FS y} {FS z}       neq eq   (S>=S gt) rewrite tsubstSwapLemma2 {tn} {x} {y} {z} (neqFS neq) (eqFS eq) gt = Refl

tsubstSwap : {tn : nat} (t1 : type (Suc (Suc tn))) (t2 : type tn) (t3 : type (Suc tn)) (x y : fin (Suc tn)) -> x >=F y ->
  tsubst y (tsubst x t2 t3) (tsubst (FS x) (tincr y t2) t1) == tsubst x t2 (tsubst (weaken y) t3 t1)
tsubstSwap (TyVar tv)          t2 t3 x y gt with finEq tv (FS x) | finEq tv (weaken y) 
tsubstSwap (TyVar .(FS x))     t2 t3 x y gt | Yes Refl | Yes eq   with tincrSubstLemma (sym eq) gt
tsubstSwap (TyVar .(FS x))     t2 t3 x y gt | Yes Refl | Yes eq   | ()
tsubstSwap (TyVar .(FS x))     t2 t3 x y gt | Yes Refl | No neq   with finEq (fdecr (weaken y) (FS x) neq) x
tsubstSwap (TyVar .(FS x))     t2 t3 x y gt | Yes Refl | No neq   | Yes eq2 = tsubstIncrRefl t2 (tsubst x t2 t3) y
tsubstSwap (TyVar .(FS x))     t2 t3 x y gt | Yes Refl | No neq   | No neq2 rewrite fdecrBelow x y neq gt with neq2 Refl
tsubstSwap (TyVar .(FS x))     t2 t3 x y gt | Yes Refl | No neq   | No neq2 | ()
tsubstSwap (TyVar tv)          t2 t3 x y gt | No neq   | Yes eq   with finEq (fdecr (FS x) tv neq) y 
tsubstSwap (TyVar tv)          t2 t3 x y gt | No neq   | Yes eq   | Yes eq2 = Refl
tsubstSwap (TyVar .(weaken y)) t2 t3 x y gt | No neq   | Yes Refl | No neq2 with neq2 (fdecrAbove x y neq gt)
tsubstSwap (TyVar .(weaken y)) t2 t3 x y gt | No neq   | Yes Refl | No neq2 | ()
tsubstSwap (TyVar tv)          t2 t3 x y gt | No neq   | No neq2 with finEq (fdecr (FS x) tv neq) y
tsubstSwap (TyVar tv)          t2 t3 x y gt | No neq   | No neq2 | Yes eq with neq2 (tsubstSwapLemma neq eq gt)
tsubstSwap (TyVar tv)          t2 t3 x y gt | No neq   | No neq2 | Yes eq | ()
tsubstSwap (TyVar tv)          t2 t3 x y gt | No neq   | No neq2 | No neq3 with finEq (fdecr (weaken y) tv neq2) x
tsubstSwap (TyVar tv)          t2 t3 x y gt | No neq   | No neq2 | No neq3 | Yes eq  with neq (tsubstSwapLemma2 neq2 eq gt)
tsubstSwap (TyVar tv)          t2 t3 x y gt | No neq   | No neq2 | No neq3 | Yes eq  | ()
tsubstSwap (TyVar tv)          t2 t3 x y gt | No neq   | No neq2 | No neq3 | No neq4 rewrite fdecrSwap x y tv neq neq2 neq3 neq4 gt = Refl
tsubstSwap (t11 => t12)        t2 t3 x y gt rewrite tsubstSwap t11 t2 t3 x y gt | tsubstSwap t12 t2 t3 x y gt = Refl
tsubstSwap (Forall t1)         t2 t3 x y gt 
  rewrite tincrSwap t2 y FZ >=FZ | sym (tincrSubst t2 t3 FZ x >=FZ) | tsubstSwap t1 (tincr FZ t2) (tincr FZ t3) (FS x) (FS y) (S>=S gt) = Refl

tsubstIncrCollapse : {tn : nat} (x : fin (Suc tn)) (t t2 : type tn) -> tsubst x t2 (tincr x t) == t
tsubstIncrCollapse {Zero}   FZ     (TyVar ())      t2
tsubstIncrCollapse {Suc tn} FZ     (TyVar tv)      t2 = Refl
tsubstIncrCollapse {tn}     (FS x) (TyVar tv)      t2 with finEq (fincr (FS x) tv) (FS x)
tsubstIncrCollapse {Zero}   (FS x) (TyVar ())      t2 | Yes eq
tsubstIncrCollapse {Suc tn} (FS x) (TyVar FZ)      t2 | Yes ()
tsubstIncrCollapse {Suc tn} (FS x) (TyVar (FS tv)) t2 | Yes eq with fincrNeq x tv (eqFS eq)
tsubstIncrCollapse {Suc tn} (FS x) (TyVar (FS tv)) t2 | Yes eq | ()
tsubstIncrCollapse {tn}     (FS x) (TyVar tv)      t2 | No neq rewrite fdecrFincrRefl (FS x) tv neq = Refl 
tsubstIncrCollapse {tn}     x      (t11 => t12)    t2 rewrite tsubstIncrCollapse x t11 t2 | tsubstIncrCollapse x t12 t2 = Refl
tsubstIncrCollapse {tn}     x      (Forall t)      t2 rewrite tsubstIncrCollapse (FS x) t (tincr FZ t2) = Refl
