module Substitution where

open import Basics
open import Fin
open import Vect
open import Type
open import RawTerm
open import Term

typeSubstitution : nat -> nat -> Set
typeSubstitution n m = vect (type m) n 

tapplyTsubst : {tn tn' : nat} -> typeSubstitution tn tn' -> type tn -> type tn'
tapplyTsubstVect : {n tn tn' : nat} -> typeSubstitution tn tn' -> vect (type tn) n -> vect (type tn') n
tapplyTsubst sub (TyVar tv)   = sub ! tv
tapplyTsubst sub (t1 => t2)   = tapplyTsubst sub t1 => tapplyTsubst sub t2
tapplyTsubst sub (Tuple ts)   = Tuple (tapplyTsubstVect sub ts)
tapplyTsubst sub (Variant ts) = Variant (tapplyTsubstVect sub ts)
tapplyTsubst sub (Rec t)      = Rec (tapplyTsubst (TyVar FZ :: map (tincr FZ) sub) t)
tapplyTsubstVect sub []        = []
tapplyTsubstVect sub (t :: ts) = tapplyTsubst sub t :: tapplyTsubstVect sub ts

applySubstIncr : {tn tn' : nat} (x : fin (Suc tn')) (y : fin (Suc tn)) (t : type tn) (sub : typeSubstitution tn tn') -> 
  tapplyTsubst (insertAt y (map (tincr x) sub) (TyVar x)) (tincr y t) == tincr x (tapplyTsubst sub t)
applySubstIncrVect : {tn tn' n : nat} (x : fin (Suc tn')) (y : fin (Suc tn)) (t : vect (type tn) n) (sub : typeSubstitution tn tn') -> 
  tapplyTsubstVect (insertAt y (map (tincr x) sub) (TyVar x)) (tincrVect y t) == tincrVect x (tapplyTsubstVect sub t)
applySubstIncr x y (TyVar z) sub    rewrite insertAtFincr (map (tincr x) sub) z y (TyVar x) | mapLookup (tincr x) sub z = Refl
applySubstIncr x y (t1 => t2) sub   rewrite applySubstIncr x y t1 sub | applySubstIncr x y t2 sub = Refl
applySubstIncr x y (Tuple ts) sub   rewrite applySubstIncrVect x y ts sub = Refl
applySubstIncr x y (Variant ts) sub rewrite applySubstIncrVect x y ts sub = Refl
applySubstIncr x y (Rec t) sub      
  rewrite mapInsertAt (map (tincr x) sub) (TyVar x) (tincr FZ) y | tincrSwapMap sub x FZ >=FZ | sym (applySubstIncr (FS x) (FS y) t (TyVar FZ :: map (tincr FZ) sub)) = Refl
applySubstIncrVect x y [] sub        = Refl
applySubstIncrVect x y (t :: ts) sub rewrite applySubstIncr x y t sub | applySubstIncrVect x y ts sub = Refl

applySubstSubstSwap : {tn tn' : nat} (x : fin (Suc tn)) (y : fin (Suc tn')) (t1 : type tn) (t2 : type (Suc tn)) (sub : typeSubstitution tn tn') ->
  tsubst y (tapplyTsubst sub t1) (tapplyTsubst (insertAt x (map (tincr y) sub) (TyVar y)) t2) == tapplyTsubst sub (tsubst x t1 t2)
applySubstSubstSwapVect : {n tn tn' : nat} (x : fin (Suc tn)) (y : fin (Suc tn')) (t1 : type tn) (ts : vect (type (Suc tn)) n) (sub : typeSubstitution tn tn') ->
  tsubstVect y (tapplyTsubst sub t1) (tapplyTsubstVect (insertAt x (map (tincr y) sub) (TyVar y)) ts) == tapplyTsubstVect sub (tsubstVect x t1 ts)
applySubstSubstSwap x y t1 (TyVar z)    sub with finEq z x
applySubstSubstSwap x y t1 (TyVar .x)   sub | Yes Refl rewrite lookupInsertAt (map (tincr y) sub) x (TyVar y) | finEqRefl y = Refl
applySubstSubstSwap x y t1 (TyVar z)    sub | No neq   
  rewrite lookupInsertAtNeq (map (tincr y) sub) x z (TyVar y) neq | mapLookup (tincr y) sub (fdecr x z neq) 
    | tsubstIncrCollapse y (sub ! fdecr x z neq) (tapplyTsubst sub t1) = Refl
applySubstSubstSwap x y t1 (t21 => t22) sub rewrite applySubstSubstSwap x y t1 t21 sub | applySubstSubstSwap x y t1 t22 sub = Refl
applySubstSubstSwap x y t1 (Tuple ts)   sub rewrite applySubstSubstSwapVect x y t1 ts sub = Refl
applySubstSubstSwap x y t1 (Variant ts) sub rewrite applySubstSubstSwapVect x y t1 ts sub = Refl
applySubstSubstSwap x y t1 (Rec t2)     sub 
  rewrite applySubstIncr FZ FZ t1 sub | sym (applySubstSubstSwap (FS x) (FS y) (tincr FZ t1) t2 (TyVar FZ :: map (tincr FZ) sub)) 
    | mapInsertAt (map (tincr y) sub) (TyVar y) (tincr FZ) x | tincrSwapMap sub y FZ >=FZ = {!!} 

--tincr FZ (tapplyTsubst sub t1)
--==
--tapplyTsubst (TyVar FZ :: map (tincr FZ) sub) (tincr FZ t1)
applySubstSubstSwapVect x y t1 []         sub = Refl
applySubstSubstSwapVect x y t1 (t2 :: ts) sub rewrite applySubstSubstSwap x y t1 t2 sub | applySubstSubstSwapVect x y t1 ts sub = Refl

applySubstLemma : {tn tn' : nat} (t : type (Suc tn)) {t2 : type tn} {sub : typeSubstitution tn tn'} -> tsubst FZ (Rec t) t == t2 -> 
  tsubst FZ (Rec (tapplyTsubst (TyVar FZ :: map (tincr FZ) sub) t)) (tapplyTsubst (TyVar FZ :: map (tincr FZ) sub) t) == tapplyTsubst sub t2
applySubstLemma t {t2} {sub} eq rewrite sym eq = applySubstSubstSwap FZ FZ (Rec t) t sub

applyTsubst : {n tn tn' : nat} (sub : typeSubstitution tn tn') {gam : vect (type tn) n} {b : bool} {r : rawlam n b} {t : type tn} -> 
  lam gam r t -> lam (map (tapplyTsubst sub) gam) r (tapplyTsubst sub t)
applyTsubstRec : {n tn tn' rn : nat} (sub : typeSubstitution tn tn') {gam : vect (type tn) n} {b : bool} {r : rawrec n b} {ts : vect (type tn) rn} -> 
  rec gam r ts -> rec (map (tapplyTsubst sub) gam) r (tapplyTsubstVect sub ts)
applyTsubstPat : {n tn tn' pn : nat} (sub : typeSubstitution tn tn') {t : type tn} {gam : vect (type tn) n} {r : rawpat n} {ts : vect (type tn) pn} -> 
  pat t gam r ts -> pat (tapplyTsubst sub t) (map (tapplyTsubst sub) gam) r (tapplyTsubstVect sub ts)
applyTsubst sub {gam} (Var x eq)      rewrite sym eq = Var x (mapLookup (tapplyTsubst sub) gam x)
applyTsubst sub       (App e1 e2)     = App (applyTsubst sub e1) (applyTsubst sub e2)
applyTsubst sub       (Abs e)         = Abs (applyTsubst sub e)
applyTsubst sub       (Let e1 e2)     = Let (applyTsubst sub e1) (applyTsubst sub e2)
applyTsubst sub       (Tuple r)       = Tuple (applyTsubstRec sub r)
applyTsubst sub       (Proj e p)      = Proj (applyTsubst sub {!!}) p
applyTsubst sub       (Variant l e)   = Variant l (applyTsubst sub {!!})
applyTsubst sub       (Case e p)      = Case (applyTsubst sub e) (applyTsubstPat sub p)
applyTsubst sub       (Fold t e eq)   = Fold (tapplyTsubst (TyVar FZ :: map (tincr FZ) sub) t) (applyTsubst sub e) (applySubstLemma t eq)
applyTsubst sub       (Unfold t e eq) = Unfold (tapplyTsubst (TyVar FZ :: map (tincr FZ) sub) t) (applyTsubst sub e) (applySubstLemma t eq)
applyTsubstRec sub Unit = Unit
applyTsubstRec sub (Field e r pf) = Field (applyTsubst sub e) (applyTsubstRec sub r) pf
applyTsubstPat sub Fail = Fail
applyTsubstPat sub (Match e p) = Match (applyTsubst sub e) (applyTsubstPat sub p)

