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

occursLemma : {tn : nat} (tv : fin tn) (t : type tn) (sub : typeSubstitution tn tn) -> contains tv t -> not (t == TyVar tv) ->
  occursSize (applyTsubst sub t) > occursSize (applyTsubst sub (TyVar tv))
occursLemmaVect : {n tn : nat} (tv : fin tn) (ts : vect (type tn) n) (sub : typeSubstitution tn tn) (cont : containsVect tv ts) -> 
  occursSizeVect (applyTsubstVect sub ts) > occursSize (applyTsubst sub (TyVar tv))
occursLemma tv _ sub TyVarCont               neq with neq Refl
occursLemma tv _ sub TyVarCont               neq | ()
occursLemma tv _ sub (ArrowCont1 t1 t2 cont) neq with typeEq t1 (TyVar tv)
occursLemma tv _ sub (ArrowCont1 ._ t2 cont) neq | Yes Refl = gtPlusBeforeLemma _ (occursSize (applyTsubst sub t2))
occursLemma tv _ sub (ArrowCont1 t1 t2 cont) neq | No neq2  = gtPlusBothLemma2 _ _ _ (occursLemma tv t1 sub cont neq2)
occursLemma tv _ sub (ArrowCont2 t1 t2 cont) neq with typeEq t2 (TyVar tv)
occursLemma tv _ sub (ArrowCont2 t1 ._ cont) neq | Yes Refl = gtPlusAfterLemma (occursSize (applyTsubst sub t1)) _
occursLemma tv _ sub (ArrowCont2 t1 t2 cont) neq | No neq2  = gtPlusBothLemma1 (occursSize (applyTsubst sub t1)) _ _ (occursLemma tv t2 sub cont neq2)
occursLemma tv _ sub (TupleCont ts cont)     neq = gtTrans sucGt (occursLemmaVect tv ts sub cont)
occursLemma tv _ sub (VariantCont ts cont)   neq = gtTrans sucGt (occursLemmaVect tv ts sub cont)
occursLemmaVect tv _ sub (ConsCont1 t ts cont) with typeEq t (TyVar tv)
occursLemmaVect tv _ sub (ConsCont1 _ ts cont) | Yes Refl = gtPlusBeforeLemma _ (occursSizeVect (applyTsubstVect sub ts))
occursLemmaVect tv _ sub (ConsCont1 t ts cont) | No neq   = gtPlusBothLemma2 _ _ _ (occursLemma tv t sub cont neq)
occursLemmaVect tv _ sub (ConsCont2 t ts cont) = gtPlusBothLemma1 (occursSize (applyTsubst sub t)) _ _ (occursLemmaVect tv ts sub cont) 

occursCheck : {tn : nat} (tv : fin tn) (t : type tn) (sub : typeSubstitution tn tn) -> contains tv t -> unifier (TyVar tv) t sub -> t == TyVar tv
occursCheck tv t sub cont (Unifer eq) with typeEq t (TyVar tv)
occursCheck tv _ sub cont (Unifer eq) | Yes Refl = Refl
occursCheck tv t sub cont (Unifer eq) | No neq   with occursLemma tv t sub cont neq 
occursCheck tv t sub cont (Unifer eq) | No neq   | lem rewrite eq with sucNrefl lem
occursCheck tv t sub cont (Unifer eq) | No neq   | lem | ()

extend : {tn : nat} (sub : typeSubstitution tn tn) (tv : fin tn) (t : type tn) -> idempotent sub -> t fixedPoint sub -> tv unmoved sub -> 
  decide (typeSubstitution tn tn * λ sub' -> idempotent sub' × (sub' extends sub) × unifier (TyVar tv) t sub')
extend sub tv t  (Idempotent id) (Fixed .t .sub fx) (Fixed ._ .sub fx2) with typeEq t (TyVar tv)
extend sub tv ._ (Idempotent id) (Fixed ._ .sub fx) (Fixed ._ .sub fx2) | Yes Refl = 
  Yes (sub , Idempotent id , Extends sub (sym id) , Unifer Refl)
extend sub tv t  (Idempotent id) (Fixed .t .sub fx) (Fixed ._ .sub fx2) | No neq with tv ∈ t
extend sub tv t  (Idempotent id) (Fixed .t .sub fx) (Fixed ._ .sub fx2) | No neq | Yes i = No (λ { (sub , _ , _ , u) -> neq (occursCheck tv t sub i u) })
extend sub tv t  (Idempotent id) (Fixed .t .sub fx) (Fixed ._ .sub fx2) | No neq | No ni = 
  Yes (tsubstComp (deltaSubst tv t) sub , Idempotent {!!} , Extends (deltaSubst tv t) Refl , Unifer {!!})

