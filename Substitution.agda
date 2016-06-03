module Substitution where

open import Basics
open import Nat
open import Fin
open import Vect
open import Type
open import RawTerm
open import Term

typeSubstitution : nat -> nat -> Set
typeSubstitution n m = vect (type m) n 

applyTsubst : {tn tn' : nat} -> typeSubstitution tn tn' -> type tn -> type tn'
applyTsubstVect : {n tn tn' : nat} -> typeSubstitution tn tn' -> vect (type tn) n -> vect (type tn') n
applyTsubst sub (TyVar tv)   = sub ! tv
applyTsubst sub (t1 => t2)   = applyTsubst sub t1 => applyTsubst sub t2
applyTsubst sub (Tuple ts)   = Tuple (applyTsubstVect sub ts)
applyTsubst sub (Variant ts) = Variant (applyTsubstVect sub ts)
applyTsubstVect sub []        = []
applyTsubstVect sub (t :: ts) = applyTsubst sub t :: applyTsubstVect sub ts

tsubstComp : {tn tn' tn'' : nat} -> typeSubstitution tn' tn'' -> typeSubstitution tn tn' -> typeSubstitution tn tn''
tsubstComp sub2 = map (applyTsubst sub2)

tsubstCompIsComp : {tn tn' tn'' : nat} (sub2 : typeSubstitution tn' tn'') (sub1 : typeSubstitution tn tn') (t : type tn) -> 
  applyTsubst (tsubstComp sub2 sub1) t == applyTsubst sub2 (applyTsubst sub1 t)
tsubstCompIsCompVect : {n tn tn' tn'' : nat} (sub2 : typeSubstitution tn' tn'') (sub1 : typeSubstitution tn tn') (ts : vect (type tn) n) -> 
  applyTsubstVect (tsubstComp sub2 sub1) ts == applyTsubstVect sub2 (applyTsubstVect sub1 ts)
tsubstCompIsComp sub2 sub1 (TyVar tv)   rewrite mapLookup (applyTsubst sub2) sub1 tv = Refl
tsubstCompIsComp sub2 sub1 (t1 => t2)   rewrite tsubstCompIsComp sub2 sub1 t1 | tsubstCompIsComp sub2 sub1 t2 = Refl
tsubstCompIsComp sub2 sub1 (Tuple ts)   rewrite tsubstCompIsCompVect sub2 sub1 ts = Refl
tsubstCompIsComp sub2 sub1 (Variant ts) rewrite tsubstCompIsCompVect sub2 sub1 ts = Refl
tsubstCompIsCompVect sub2 sub1 []        = Refl
tsubstCompIsCompVect sub2 sub1 (t :: ts) rewrite tsubstCompIsComp sub2 sub1 t | tsubstCompIsCompVect sub2 sub1 ts = Refl

idSubst : {tn : nat} -> typeSubstitution tn tn
idSubst {Zero}   = []
idSubst {Suc tn} = TyVar FZ :: map (tincr FZ) idSubst

deltaSubst : {tn : nat} -> fin tn -> type tn -> typeSubstitution tn tn
deltaSubst x t = replace x idSubst t

data idempotent {tn : nat} (sub : typeSubstitution tn tn) : Set where
  Idempotent : tsubstComp sub sub == sub -> idempotent sub

data _fixedPoint_ : {tn : nat} -> type tn -> typeSubstitution tn tn -> Set where
  Fixed : {tn : nat} (t : type tn) (sub : typeSubstitution tn tn) -> applyTsubst sub t == t -> t fixedPoint sub

_unmoved_ : {tn : nat} -> fin tn -> typeSubstitution tn tn -> Set
tv unmoved sub = TyVar tv fixedPoint sub

data unifier {tn tn' : nat} (t1 t2 : type tn) (sub : typeSubstitution tn tn') : Set where
  Unifer : applyTsubst sub t1 == applyTsubst sub t2 -> unifier t1 t2 sub

data _extends_ {tn tn' tn'' : nat} (sub' : typeSubstitution tn tn'') (sub : typeSubstitution tn tn') : Set where
  Extends : (sub'' : typeSubstitution tn' tn'') -> sub' == tsubstComp sub'' sub -> sub' extends sub

data mostGeneralUnifier {tn tn' : nat} (t1 t2 : type tn) (sub : typeSubstitution tn tn') : Set where
  MostGeneral : unifier t1 t2 sub -> ({tn'' : nat} (sub' : typeSubstitution tn tn'') -> unifier t1 t2 sub' -> sub' extends sub) -> mostGeneralUnifier t1 t2 sub

occursSize : {tn : nat} -> type tn -> nat
occursSizeVect : {n tn : nat} -> vect (type tn) n -> nat
occursSize (TyVar x)    = Zero
occursSize (t1 => t2)   = Suc (occursSize t1 + occursSize t2)
occursSize (Tuple ts)   = Suc (occursSizeVect ts)
occursSize (Variant ts) = Suc (occursSizeVect ts)
occursSizeVect []        = Zero
occursSizeVect (t :: ts) = Suc (occursSize t + occursSizeVect ts)

sizeLemma : {tn : nat} (tv : fin tn) (t : type tn) (sub : typeSubstitution tn tn) -> 
  occursSize (applyTsubst sub t) > occursSize t \/ occursSize (applyTsubst sub t) == occursSize t
sizeLemmaVect : {n tn : nat} (tv : fin tn) (ts : vect (type tn) n) (sub : typeSubstitution tn tn) -> 
  occursSizeVect (applyTsubstVect sub ts) > occursSizeVect ts \/ occursSizeVect (applyTsubstVect sub ts) == occursSizeVect ts
sizeLemma tv (TyVar x)    sub with occursSize (sub ! x)
sizeLemma tv (TyVar x)    sub | Zero  = InR Refl
sizeLemma tv (TyVar x)    sub | Suc n = InL (S>Z n)
sizeLemma tv (t1 => t2)   sub with sizeLemma tv t1 sub | sizeLemma tv t2 sub
sizeLemma tv (t1 => t2)   sub | InL gt | InL gt2 = InL (S>S _ _ (gtPlusBoth gt gt2))
sizeLemma tv (t1 => t2)   sub | InL gt | InR eq  rewrite eq = InL (S>S _ _ (gtPlusAfter _ gt))
sizeLemma tv (t1 => t2)   sub | InR eq | InL gt  rewrite eq = InL (S>S _ _ (gtPlusBefore (occursSize t1) gt))
sizeLemma tv (t1 => t2)   sub | InR eq | InR eq2 rewrite eq | eq2 = InR Refl
sizeLemma tv (Tuple ts)   sub with sizeLemmaVect tv ts sub 
sizeLemma tv (Tuple ts)   sub | InL gt = InL (S>S _ _ gt)
sizeLemma tv (Tuple ts)   sub | InR eq rewrite eq = InR Refl
sizeLemma tv (Variant ts) sub with sizeLemmaVect tv ts sub 
sizeLemma tv (Variant ts) sub | InL gt = InL (S>S _ _ gt)
sizeLemma tv (Variant ts) sub | InR eq rewrite eq = InR Refl
sizeLemmaVect tv []        sub = InR Refl
sizeLemmaVect tv (t :: ts) sub with sizeLemma tv t sub | sizeLemmaVect tv ts sub
sizeLemmaVect tv (t :: ts) sub | InL gt | InL gt2 = InL (S>S _ _ (gtPlusBoth gt gt2))
sizeLemmaVect tv (t :: ts) sub | InL gt | InR eq  rewrite eq = InL (S>S _ _ (gtPlusAfter _ gt))
sizeLemmaVect tv (t :: ts) sub | InR eq | InL gt  rewrite eq = InL (S>S _ _ (gtPlusBefore (occursSize t) gt))
sizeLemmaVect tv (t :: ts) sub | InR eq | InR eq2 rewrite eq | eq2 = InR Refl

occursLemma : {tn : nat} (tv : fin tn) (t : type tn) (sub : typeSubstitution tn tn) -> contains tv t -> not (fin tn * λ x -> sub ! tv == TyVar x) -> 
  occursSize (applyTsubst sub t) > occursSize t
occursLemmaVect : {n tn : nat} (tv : fin tn) (t : vect (type tn) n) (sub : typeSubstitution tn tn) -> containsVect tv t -> not (fin tn * λ x -> sub ! tv == TyVar x) -> 
  occursSizeVect (applyTsubstVect sub t) > occursSizeVect t
occursLemma tv _ sub TyVarCont               ntv with sub ! tv 
occursLemma tv _ sub TyVarCont               ntv | TyVar x    with ntv (x , Refl) 
occursLemma tv _ sub TyVarCont               ntv | TyVar x    | ()
occursLemma tv _ sub TyVarCont               ntv | t1 => t2   = S>Z _
occursLemma tv _ sub TyVarCont               ntv | Tuple ts   = S>Z _
occursLemma tv _ sub TyVarCont               ntv | Variant ts = S>Z _
occursLemma tv _ sub (ArrowCont1 t1 t2 cont) ntv with sizeLemma tv t2 sub
occursLemma tv _ sub (ArrowCont1 t1 t2 cont) ntv | InL gt = S>S _ _ (gtPlusBoth (occursLemma tv t1 sub cont ntv) gt)
occursLemma tv _ sub (ArrowCont1 t1 t2 cont) ntv | InR eq rewrite eq = S>S _ _ (gtPlusAfter _ (occursLemma tv t1 sub cont ntv ))
occursLemma tv _ sub (ArrowCont2 t1 t2 cont) ntv with sizeLemma tv t1 sub
occursLemma tv _ sub (ArrowCont2 t1 t2 cont) ntv | InL gt = S>S _ _ (gtPlusBoth gt (occursLemma tv t2 sub cont ntv))
occursLemma tv _ sub (ArrowCont2 t1 t2 cont) ntv | InR eq rewrite eq = S>S _ _ (gtPlusBefore (occursSize t1) (occursLemma tv t2 sub cont ntv ))
occursLemma tv _ sub (TupleCont ts x)        ntv = S>S _ _ (occursLemmaVect tv ts sub x ntv)
occursLemma tv _ sub (VariantCont ts x)      ntv = S>S _ _ (occursLemmaVect tv ts sub x ntv)
occursLemmaVect tv _ sub (ConsCont1 t ts cont) ntv with sizeLemmaVect tv ts sub
occursLemmaVect tv _ sub (ConsCont1 t ts cont) ntv | InL gt = S>S _ _ (gtPlusBoth (occursLemma tv t sub cont ntv) gt)
occursLemmaVect tv _ sub (ConsCont1 t ts cont) ntv | InR eq rewrite eq = S>S _ _ (gtPlusAfter (occursSizeVect ts) (occursLemma tv t sub cont ntv))
occursLemmaVect tv _ sub (ConsCont2 t ts cont) ntv with sizeLemma tv t sub
occursLemmaVect tv _ sub (ConsCont2 t ts cont) ntv | InL gt = S>S _ _ (gtPlusBoth gt (occursLemmaVect tv ts sub cont ntv))
occursLemmaVect tv _ sub (ConsCont2 t ts cont) ntv | InR eq rewrite eq = S>S _ _ (gtPlusBefore (occursSize t) (occursLemmaVect tv ts sub cont ntv))

occursCheck : {tn : nat} (tv : fin tn) (t : type tn) (sub : typeSubstitution tn tn) -> contains tv t -> unifier (TyVar tv) t sub -> t == TyVar tv
occursCheck tv .(TyVar tv)   sub TyVarCont               (Unifer eq) = Refl
occursCheck tv .(t1 => t2)   sub (ArrowCont1 t1 t2 cont) (Unifer eq) = {!!}
occursCheck tv .(t1 => t2)   sub (ArrowCont2 t1 t2 cont) (Unifer eq) = {!!}
occursCheck tv .(Tuple ts)   sub (TupleCont ts x)        (Unifer eq) = {!!}
occursCheck tv .(Variant ts) sub (VariantCont ts x)      (Unifer eq) = {!!}

extend : {tn : nat} (sub : typeSubstitution tn tn) (tv : fin tn) (t : type tn) -> idempotent sub -> t fixedPoint sub -> tv unmoved sub -> 
  decide (typeSubstitution tn tn * λ sub' -> idempotent sub' × (sub' extends sub) × unifier (TyVar tv) t sub')
extend sub tv t  (Idempotent id) (Fixed .t .sub fx) (Fixed ._ .sub fx2) with typeEq t (TyVar tv)
extend sub tv ._ (Idempotent id) (Fixed ._ .sub fx) (Fixed ._ .sub fx2) | Yes Refl = 
  Yes (sub , Idempotent id , Extends sub (sym id) , Unifer Refl)
extend sub tv t  (Idempotent id) (Fixed .t .sub fx) (Fixed ._ .sub fx2) | No neq with tv ∈ t
extend sub tv t  (Idempotent id) (Fixed .t .sub fx) (Fixed ._ .sub fx2) | No neq | Yes i = No (λ { (sub , _ , _ , u) -> neq (occursCheck tv t sub i u) })
extend sub tv t  (Idempotent id) (Fixed .t .sub fx) (Fixed ._ .sub fx2) | No neq | No ni = 
  Yes (tsubstComp (deltaSubst tv t) sub , Idempotent {!!} , Extends (deltaSubst tv t) Refl , Unifer {!!})

