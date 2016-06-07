module Type where

open import Basics
open import Nat
open import Fin
open import Vect

data type (tn : nat) : Set where
  TyVar : fin tn -> type tn
  _=>_ : type tn -> type tn -> type tn
  Tuple : {n : nat} -> vect (type tn) n -> type tn
  Variant : {n : nat} -> vect (type tn) n -> type tn
--  Rec : type (Suc tn) -> type tn

tincr : {tn : nat} -> fin (Suc tn) -> type tn -> type (Suc tn)
tincrVect : {n tn : nat} -> fin (Suc tn) -> vect (type tn) n -> vect (type (Suc tn)) n
tincr x (TyVar y) = TyVar (fincr x y)
tincr x (t1 => t2) = tincr x t1 => tincr x t2
tincr x (Tuple ts)   = Tuple (tincrVect x ts)
tincr x (Variant ts) = Variant (tincrVect x ts)
--tincr x (Rec t)      = Rec (tincr (FS x) t)
tincrVect x []        = []
tincrVect x (t :: ts) = tincr x t :: tincrVect x ts

tsubst : {tn : nat} -> fin (Suc tn) -> type tn -> type (Suc tn) -> type tn
tsubstVect : {n tn : nat} -> fin (Suc tn) -> type tn -> vect (type (Suc tn)) n -> vect (type tn) n
tsubst tv v (TyVar tv') with finEq tv' tv
tsubst tv v (TyVar tv') | Yes pf = v
tsubst tv v (TyVar tv') | No npf = TyVar (fdecr tv tv' npf)
tsubst tv v (t1 => t2)  = tsubst tv v t1 => tsubst tv v t2
tsubst tv v (Tuple ts)   = Tuple (tsubstVect tv v ts)
tsubst tv v (Variant ts) = Variant (tsubstVect tv v ts)
--tsubst tv v (Rec t)      = Rec (tsubst (FS tv) (tincr FZ v) t)
tsubstVect tv v []        = []
tsubstVect tv v (t :: ts) = tsubst tv v t :: tsubstVect tv v ts

-- abbreviations 

unitT : {tn : nat} -> type tn
unitT = Tuple []

voidT : {tn : nat} -> type tn
voidT = Variant []

-- nat = μx. 1 + x
--natT' : {tn : nat} -> type (Suc tn)
--natT' = Variant (unitT :: TyVar FZ :: [])

--natT : {tn : nat} -> type tn
--natT = Rec natT'

-- list a = μx. 1 + (a × x)
--listT' : {tn : nat} -> type tn -> type (Suc tn)
--listT' a = Variant (unitT :: Tuple (tincr FZ a :: TyVar FZ :: []) :: [])

--listT : {tn : nat} -> type tn -> type tn
--listT a = Rec (listT' a)

-- lemmas

tincrIdx : {n tn : nat} (x : fin (Suc tn)) (ts : vect (type tn) n) (y : fin n) -> tincrVect x ts ! y == tincr x (ts ! y)
tincrIdx x []        ()
tincrIdx x (t :: ts) FZ     = Refl
tincrIdx x (t :: ts) (FS y) rewrite tincrIdx x ts y = Refl

tsubstIdx : {n tn : nat} (x : fin (Suc tn)) (t : type tn) (ts : vect (type (Suc tn)) n) (y : fin n) -> tsubstVect x t ts ! y == tsubst x t (ts ! y)
tsubstIdx x v []        ()
tsubstIdx x v (t :: ts) FZ     = Refl
tsubstIdx x v (t :: ts) (FS y) rewrite tsubstIdx x v ts y = Refl

tincrSwap : {tn : nat} (t : type tn) (x y : fin (Suc tn)) -> x >=F y -> tincr (weaken y) (tincr x t) == tincr (FS x) (tincr y t)
tincrSwapVect : {n tn : nat} (ts : vect (type tn) n) (x y : fin (Suc tn)) -> x >=F y -> tincrVect (weaken y) (tincrVect x ts) == tincrVect (FS x) (tincrVect y ts)
tincrSwap (TyVar tv)   x y gt rewrite fincrSwap tv x y gt = Refl
tincrSwap (t1 => t2)   x y gt rewrite tincrSwap t1 x y gt | tincrSwap t2 x y gt = Refl
tincrSwap (Tuple ts)   x y gt rewrite tincrSwapVect ts x y gt = Refl
tincrSwap (Variant ts) x y gt rewrite tincrSwapVect ts x y gt = Refl
--tincrSwap (Rec t)      x y gt rewrite tincrSwap t (FS x) (FS y) (S>=S gt) = Refl
tincrSwapVect []        x y gt = Refl
tincrSwapVect (t :: ts) x y gt rewrite tincrSwap t x y gt | tincrSwapVect ts x y gt = Refl

tincrSwapMap : {n tn : nat} (ts : vect (type tn) n) (x y : fin (Suc tn)) -> x >=F y -> map (tincr (weaken y)) (map (tincr x) ts) == map (tincr (FS x)) (map (tincr y) ts)
tincrSwapMap []        x y gt = Refl
tincrSwapMap (t :: ts) x y gt rewrite tincrSwap t x y gt | tincrSwapMap ts x y gt = Refl

tSubstIncrLemma : {n : nat} {y x : fin n} -> x >=F y -> not (FS x == weaken y)
tSubstIncrLemma Z>=Z      ()
tSubstIncrLemma S>=Z      ()
tSubstIncrLemma (S>=S gt) eq with tSubstIncrLemma gt (eqFS eq) 
tSubstIncrLemma (S>=S gt) eq | ()

tsubstIncr : {tn : nat} (t1 : type tn) (t2 : type (Suc tn)) (x y : fin (Suc tn)) -> x >=F y ->
  tsubst (weaken y) (tincr x t1) (tincr (FS x) t2) == tincr x (tsubst y t1 t2)
tsubstIncrVect : {n tn : nat} (t : type tn) (ts : vect (type (Suc tn)) n) (x y : fin (Suc tn)) -> x >=F y ->
  tsubstVect (weaken y) (tincr x t) (tincrVect (FS x) ts) == tincrVect x (tsubstVect y t ts)
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
tsubstIncr t1 (Tuple ts)   x      y gt rewrite tsubstIncrVect t1 ts x y gt = Refl
tsubstIncr t1 (Variant ts) x      y gt rewrite tsubstIncrVect t1 ts x y gt = Refl
--tsubstIncr t1 (Rec t2)     FZ     y gt rewrite tincrSwap t1 FZ FZ Z>=Z | tsubstIncr (tincr FZ t1) t2 (FS FZ) (FS y) (S>=S gt) = Refl
--tsubstIncr t1 (Rec t2)     (FS x) y gt rewrite tincrSwap t1 (FS x) FZ S>=Z | tsubstIncr (tincr FZ t1) t2 (FS (FS x)) (FS y) (S>=S gt) = Refl
tsubstIncrVect t1 []         x y gt = Refl
tsubstIncrVect t1 (t2 :: ts) x y gt rewrite tsubstIncr t1 t2 x y gt | tsubstIncrVect t1 ts x y gt = Refl

tincrSubstLemma : {tn : nat} {x y : fin (Suc tn)} -> weaken x == FS y -> not (y >=F x)
tincrSubstLemma {tn}     {FZ}    {FZ}   () Z>=Z
tincrSubstLemma {tn}     {FZ}    {FS y} () S>=Z
tincrSubstLemma {Zero}   {FS ()} {FS y} eq (S>=S gt)
tincrSubstLemma {Suc tn} {FS x}  {FS y} eq (S>=S gt) = tincrSubstLemma {tn} {x} {y} (eqFS eq) gt

tincrSubst : {tn : nat} (t1 : type tn) (t2 : type (Suc tn)) (x y : fin (Suc tn)) -> y >=F x ->
  tsubst (FS y) (tincr x t1) (tincr (weaken x) t2) == tincr x (tsubst y t1 t2)
tincrSubstVect : {n tn : nat} (t : type tn) (ts : vect (type (Suc tn)) n) (x y : fin (Suc tn)) -> y >=F x ->
  tsubstVect (FS y) (tincr x t) (tincrVect (weaken x) ts) == tincrVect x (tsubstVect y t ts)
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
tincrSubst t1 (Tuple ts)   x y lt rewrite tincrSubstVect t1 ts x y lt = Refl
tincrSubst t1 (Variant ts) x y lt rewrite tincrSubstVect t1 ts x y lt = Refl
--tincrSubst t1 (Rec t2)     x y lt rewrite tincrSwap t1 x FZ >=FZ | tincrSubst (tincr FZ t1) t2 (FS x) (FS y) (S>=S lt) = Refl
tincrSubstVect t1 []         x y lt = Refl
tincrSubstVect t1 (t2 :: ts) x y lt rewrite tincrSubst t1 t2 x y lt | tincrSubstVect t1 ts x y lt = Refl

tsubstIncrRefl : {tn : nat} (t t2 : type tn) (x : fin (Suc tn)) -> tsubst x t2 (tincr x t) == t
tsubstIncrReflVect : {n tn : nat} (ts : vect (type tn) n) (t : type tn) (x : fin (Suc tn)) -> tsubstVect x t (tincrVect x ts) == ts
tsubstIncrRefl (TyVar tv)   t2 x with finEq (fincr x tv) x 
tsubstIncrRefl (TyVar tv)   t2 x | Yes eq with fincrNeq x tv eq
tsubstIncrRefl (TyVar tv)   t2 x | Yes eq | ()
tsubstIncrRefl (TyVar tv)   t2 x | No neq rewrite fdecrFincrRefl x tv neq = Refl
tsubstIncrRefl (t11 => t12) t2 x rewrite tsubstIncrRefl t11 t2 x | tsubstIncrRefl t12 t2 x = Refl
tsubstIncrRefl (Tuple ts)   t2 x rewrite tsubstIncrReflVect ts t2 x = Refl
tsubstIncrRefl (Variant ts) t2 x rewrite tsubstIncrReflVect ts t2 x = Refl
--tsubstIncrRefl (Rec t)      t2 x rewrite tsubstIncrRefl t (tincr FZ t2) (FS x) = Refl
tsubstIncrReflVect []         t2 x = Refl
tsubstIncrReflVect (t1 :: ts) t2 x rewrite tsubstIncrRefl t1 t2 x | tsubstIncrReflVect ts t2 x = Refl

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
tsubstSwapVect : {n tn : nat} (ts : vect (type (Suc (Suc tn))) n) (t2 : type tn) (t3 : type (Suc tn)) (x y : fin (Suc tn)) -> x >=F y ->
  tsubstVect y (tsubst x t2 t3) (tsubstVect (FS x) (tincr y t2) ts) == tsubstVect x t2 (tsubstVect (weaken y) t3 ts)
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
tsubstSwap (Tuple ts)          t2 t3 x y gt rewrite tsubstSwapVect ts t2 t3 x y gt = Refl
tsubstSwap (Variant ts)        t2 t3 x y gt rewrite tsubstSwapVect ts t2 t3 x y gt = Refl
--tsubstSwap (Rec t1)            t2 t3 x y gt 
--  rewrite tincrSwap t2 y FZ >=FZ | sym (tincrSubst t2 t3 FZ x >=FZ) | tsubstSwap t1 (tincr FZ t2) (tincr FZ t3) (FS x) (FS y) (S>=S gt) = Refl
tsubstSwapVect []         t2 t3 x y gt = Refl
tsubstSwapVect (t1 :: ts) t2 t3 x y gt rewrite tsubstSwap t1 t2 t3 x y gt | tsubstSwapVect ts t2 t3 x y gt = Refl

tsubstIncrCollapse : {tn : nat} (x : fin (Suc tn)) (t t2 : type tn) -> tsubst x t2 (tincr x t) == t
tsubstIncrCollapseVect : {n tn : nat} (x : fin (Suc tn)) (t : vect (type tn) n) (t2 : type tn) -> tsubstVect x t2 (tincrVect x t) == t
tsubstIncrCollapse {Zero}   FZ     (TyVar ())      t2
tsubstIncrCollapse {Suc tn} FZ     (TyVar tv)      t2 = Refl
tsubstIncrCollapse {tn}     (FS x) (TyVar tv)      t2 with finEq (fincr (FS x) tv) (FS x)
tsubstIncrCollapse {Zero}   (FS x) (TyVar ())      t2 | Yes eq
tsubstIncrCollapse {Suc tn} (FS x) (TyVar FZ)      t2 | Yes ()
tsubstIncrCollapse {Suc tn} (FS x) (TyVar (FS tv)) t2 | Yes eq with fincrNeq x tv (eqFS eq)
tsubstIncrCollapse {Suc tn} (FS x) (TyVar (FS tv)) t2 | Yes eq | ()
tsubstIncrCollapse {tn}     (FS x) (TyVar tv)      t2 | No neq rewrite fdecrFincrRefl (FS x) tv neq = Refl 
tsubstIncrCollapse {tn}     x      (t11 => t12)    t2 rewrite tsubstIncrCollapse x t11 t2 | tsubstIncrCollapse x t12 t2 = Refl
tsubstIncrCollapse {tn}     x      (Tuple ts)      t2 rewrite tsubstIncrCollapseVect x ts t2 = Refl
tsubstIncrCollapse {tn}     x      (Variant ts)    t2 rewrite tsubstIncrCollapseVect x ts t2 = Refl
--tsubstIncrCollapse {tn}     x      (Rec t)         t2 rewrite tsubstIncrCollapse (FS x) t (tincr FZ t2) = Refl
tsubstIncrCollapseVect x []         t2 = Refl
tsubstIncrCollapseVect x (t1 :: ts) t2 rewrite tsubstIncrCollapse x t1 t2 | tsubstIncrCollapseVect x ts t2 = Refl

-- equality

typeEq : {tn : nat} -> equality (type tn)
typeVectEq : {n tn : nat} -> equality (vect (type tn) n)
typeEq (TyVar tv1)        (TyVar tv2)          with finEq tv1 tv2
typeEq (TyVar tv1)        (TyVar .tv1)         | Yes Refl = Yes Refl
typeEq (TyVar tv1)        (TyVar tv2)          | No neq   = No (lemma neq)
  where 
    lemma : {tn : nat} {tv1 tv2 : fin tn} -> not (tv1 == tv2) -> not (TyVar tv1 == TyVar tv2)
    lemma neq Refl = neq Refl
typeEq (TyVar tv1)        (t21 => t22)         = No (λ ())
typeEq (TyVar tv1)        (Tuple ts2)          = No (λ ())
typeEq (TyVar tv1)        (Variant ts2)        = No (λ ())
--typeEq (TyVar tv1)        (Rec t2)             = No (λ ())
typeEq (t11 => t12)       (TyVar tv2)          = No (λ ())
typeEq (t11 => t12)       (t21 => t22)         with typeEq t11 t21 | typeEq t12 t22
typeEq (t11 => t12)       (.t11 => .t12)       | Yes Refl | Yes Refl = Yes Refl
typeEq (t11 => t12)       (.t11 => t22)        | Yes Refl | No neq   = No (lemma neq)
  where 
    lemma : {tn : nat} {t11 t12 t22 : type tn} -> not (t12 == t22) -> not ((t11 => t12) == (t11 => t22))
    lemma neq Refl = neq Refl
typeEq (t11 => t12)       (t21 => t22)         | No neq   | _        = No (lemma neq)
  where 
    lemma : {tn : nat} {t11 t12 t21 t22 : type tn} -> not (t11 == t21) -> not ((t11 => t12) == (t21 => t22))
    lemma neq Refl = neq Refl
typeEq (t11 => t12)       (Tuple ts2)          = No (λ ())
typeEq (t11 => t12)       (Variant ts2)        = No (λ ())
--typeEq (t11 => t12)       (Rec t3)             = No (λ ())
typeEq (Tuple ts1)        (TyVar tv2)          = No (λ ())
typeEq (Tuple ts1)        (t21 => t22)         = No (λ ())
typeEq (Tuple {n1} ts1)   (Tuple {n2} ts2)     with natEq n1 n2 
typeEq (Tuple {n1} ts1)   (Tuple {.n1} ts2)    | Yes Refl with typeVectEq ts1 ts2
typeEq (Tuple {n1} ts1)   (Tuple {.n1} .ts1)   | Yes Refl | Yes Refl = Yes Refl
typeEq (Tuple {n1} ts1)   (Tuple {.n1} ts2)    | Yes Refl | No neq   = No (lemma neq)
  where 
    lemma : {n tn : nat} {ts1 ts2 : vect (type tn) n} -> not (ts1 == ts2) -> not (Tuple ts1 == Tuple ts2)
    lemma neq Refl = neq Refl
typeEq (Tuple {n1} ts1)   (Tuple {n2} ts2)     | No neq   = No (lemma neq)
  where 
    lemma : {n1 n2 tn : nat} {ts1 : vect (type tn) n1} {ts2 : vect (type tn) n2} -> not (n1 == n2) -> not (Tuple ts1 == Tuple ts2)
    lemma neq Refl = neq Refl
typeEq (Tuple ts1)        (Variant ts2)        = No (λ ())
--typeEq (Tuple ts1)        (Rec t2)             = No (λ ())
typeEq (Variant ts1)      (TyVar tv2)          = No (λ ())
typeEq (Variant ts1)      (t21 => t22)         = No (λ ())
typeEq (Variant ts1)      (Tuple ts2)          = No (λ ())
typeEq (Variant {n1} ts1) (Variant {n2} ts2)   with natEq n1 n2 
typeEq (Variant {n1} ts1) (Variant {.n1} ts2)  | Yes Refl with typeVectEq ts1 ts2
typeEq (Variant {n1} ts1) (Variant {.n1} .ts1) | Yes Refl | Yes Refl = Yes Refl
typeEq (Variant {n1} ts1) (Variant {.n1} ts2)  | Yes Refl | No neq   = No (lemma neq)
  where 
    lemma : {n tn : nat} {ts1 ts2 : vect (type tn) n} -> not (ts1 == ts2) -> not (Variant ts1 == Variant ts2)
    lemma neq Refl = neq Refl
typeEq (Variant {n1} ts1) (Variant {n2} ts2)   | No neq   = No (lemma neq)
  where 
    lemma : {n1 n2 tn : nat} {ts1 : vect (type tn) n1} {ts2 : vect (type tn) n2} -> not (n1 == n2) -> not (Variant ts1 == Variant ts2)
    lemma neq Refl = neq Refl
--typeEq (Variant ts1)      (Rec t2)             = No (λ ())
--typeEq (Rec t1)           (TyVar tv2)          = No (λ ())
--typeEq (Rec t1)           (t21 => t22)         = No (λ ())
--typeEq (Rec t1)           (Tuple ts2)          = No (λ ())
--typeEq (Rec t1)           (Variant ts2)        = No (λ ())
--typeEq (Rec t1)           (Rec t2)             with typeEq t1 t2 
--typeEq (Rec t1)           (Rec .t1)            | Yes Refl = Yes Refl
--typeEq (Rec t1)           (Rec t2)             | No neq   = No (lemma neq)
--  where 
--    lemma : {tn : nat} {t1 t2 : type (Suc tn)} -> not (t1 == t2) -> not (Rec t1 == Rec t2)
--    lemma neq Refl = neq Refl
typeVectEq []          []            = Yes Refl
typeVectEq (t1 :: ts1) (t2 :: ts2)   with typeEq t1 t2 | typeVectEq ts1 ts2
typeVectEq (t1 :: ts1) (.t1 :: .ts1) | Yes Refl        | Yes Refl = Yes Refl
typeVectEq (t1 :: ts1) (.t1 :: ts2)  | Yes Refl        | No neq   = No (lemma neq)
  where 
    lemma : {n tn : nat} {t1 : type tn} {ts1 ts2 : vect (type tn) n} -> not (ts1 == ts2) -> not (t1 :: ts1 == t1 :: ts2)
    lemma neq Refl = neq Refl
typeVectEq (t1 :: ts1) (t2 :: ts2)   | No neq          | _        = No (lemma neq)
  where 
    lemma : {n tn : nat} {t1 t2 : type tn} {ts1 ts2 : vect (type tn) n} -> not (t1 == t2) -> not (t1 :: ts1 == t2 :: ts2)
    lemma neq Refl = neq Refl

-- used variables

data contains' {tn : nat} (tv : fin tn) : type tn -> Set
data containsVect' {tn : nat} (tv : fin tn) : {n : nat} -> vect (type tn) n -> Set
data contains' {tn} tv where
  TyVarCont : contains' tv (TyVar tv)
  ArrowCont1 : (t1 t2 : type tn) -> contains' tv t1 -> contains' tv (t1 => t2)
  ArrowCont2 : (t1 t2 : type tn) -> contains' tv t2 -> contains' tv (t1 => t2)
  TupleCont : {n : nat} (ts : vect (type tn) n) -> containsVect' tv ts -> contains' tv (Tuple ts)
  VariantCont :  {n : nat} (ts : vect (type tn) n) -> containsVect' tv ts -> contains' tv (Variant ts)
--  RecCont : (t : type (Suc tn)) -> contains' (FS tv) t -> contains' tv (Rec t)
data containsVect' {tn} tv where
  ConsCont1 : {n : nat} (t : type tn) (ts : vect (type tn) n) -> contains' tv t -> containsVect' tv (t :: ts)
  ConsCont2 : {n : nat} (t : type tn) (ts : vect (type tn) n) -> containsVect' tv ts -> containsVect' tv (t :: ts)

_contains_ : {tn : nat} -> type tn -> fin tn -> Set
_contains_ t tv = contains' tv t

_containsVect_ : {n tn : nat} -> vect (type tn) n -> fin tn -> Set
_containsVect_ t tv = containsVect' tv t

_∈t_ : {tn : nat} (tv : fin tn) (t : type tn) -> decide (t contains tv) 
_∈tvect_ : {n tn : nat} (tv : fin tn) (ts : vect (type tn) n) -> decide (ts containsVect tv) 
tv ∈t TyVar tv'  with finEq tv tv'
tv ∈t TyVar .tv  | Yes Refl = Yes TyVarCont
tv ∈t TyVar tv'  | No neq   = No (lemma neq)
  where
    lemma : {tn : nat} {tv tv' : fin tn} -> not (tv == tv') -> not (TyVar tv' contains tv)
    lemma neq TyVarCont = neq Refl
tv ∈t (t1 => t2) with tv ∈t t1 | tv ∈t t2
tv ∈t (t1 => t2) | Yes i      | i'    = Yes (ArrowCont1 t1 t2 i)
tv ∈t (t1 => t2) | No n       | Yes i = Yes (ArrowCont2 t1 t2 i)
tv ∈t (t1 => t2) | No n       | No n' = No (λ { (ArrowCont1 _ _ i) -> n i ; (ArrowCont2 _ _ i) -> n' i })
tv ∈t Tuple ts   with tv ∈tvect ts 
tv ∈t Tuple ts   | Yes i = Yes (TupleCont ts i)
tv ∈t Tuple ts   | No n  = No (λ { (TupleCont _ i) -> n i })
tv ∈t Variant ts with tv ∈tvect ts 
tv ∈t Variant ts | Yes i = Yes (VariantCont ts i)
tv ∈t Variant ts | No n  = No (λ { (VariantCont _ i) -> n i })
--tv ∈t Rec t      with FS tv ∈ t 
--tv ∈t Rec t      | Yes i = Yes (RecCont t i)
--tv ∈t Rec t      | No n  = No (λ { (RecCont _ x) -> n x })
tv ∈tvect []      = No (λ ())
tv ∈tvect t :: ts with tv ∈t t | tv ∈tvect ts 
tv ∈tvect t :: ts | Yes i     | i'    = Yes (ConsCont1 t ts i)
tv ∈tvect t :: ts | No n      | Yes i = Yes (ConsCont2 t ts i)
tv ∈tvect t :: ts | No n      | No n' = No (λ { (ConsCont1 _ _ i) -> n i ; (ConsCont2 _ _ i) -> n' i })

infix 50 _∈t_
