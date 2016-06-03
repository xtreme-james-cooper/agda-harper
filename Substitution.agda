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

_∘_ : {tn tn' tn'' : nat} -> typeSubstitution tn' tn'' -> typeSubstitution tn tn' -> typeSubstitution tn tn''
_∘_ sub2 = map (applyTsubst sub2)

infixr 50 _∘_

tsubstCompIsComp : {tn tn' tn'' : nat} (sub2 : typeSubstitution tn' tn'') (sub1 : typeSubstitution tn tn') (t : type tn) -> 
  applyTsubst (sub2 ∘ sub1) t == applyTsubst sub2 (applyTsubst sub1 t)
tsubstCompIsCompVect : {n tn tn' tn'' : nat} (sub2 : typeSubstitution tn' tn'') (sub1 : typeSubstitution tn tn') (ts : vect (type tn) n) -> 
  applyTsubstVect (sub2 ∘ sub1) ts == applyTsubstVect sub2 (applyTsubstVect sub1 ts)
tsubstCompIsComp sub2 sub1 (TyVar tv)   rewrite mapLookup (applyTsubst sub2) sub1 tv = Refl
tsubstCompIsComp sub2 sub1 (t1 => t2)   rewrite tsubstCompIsComp sub2 sub1 t1 | tsubstCompIsComp sub2 sub1 t2 = Refl
tsubstCompIsComp sub2 sub1 (Tuple ts)   rewrite tsubstCompIsCompVect sub2 sub1 ts = Refl
tsubstCompIsComp sub2 sub1 (Variant ts) rewrite tsubstCompIsCompVect sub2 sub1 ts = Refl
tsubstCompIsCompVect sub2 sub1 []        = Refl
tsubstCompIsCompVect sub2 sub1 (t :: ts) rewrite tsubstCompIsComp sub2 sub1 t | tsubstCompIsCompVect sub2 sub1 ts = Refl

tsubstCompAssoc : {tn1 tn2 tn3 tn4 : nat} (sub1 : typeSubstitution tn3 tn4) (sub2 : typeSubstitution tn2 tn3) (sub3 : typeSubstitution tn1 tn2) -> 
  (sub1 ∘ sub2) ∘ sub3 == sub1 ∘ sub2 ∘ sub3
tsubstCompAssoc sub1 sub2 []          = Refl
tsubstCompAssoc sub1 sub2 (t :: sub3) rewrite tsubstCompAssoc sub1 sub2 sub3 | tsubstCompIsComp sub1 sub2 t = Refl

idSubst : {tn : nat} -> typeSubstitution tn tn
idSubst {Zero}   = []
idSubst {Suc tn} = TyVar FZ :: map (tincr FZ) idSubst

deltaSubst : {tn : nat} -> fin tn -> type tn -> typeSubstitution tn tn
deltaSubst x t = replace x idSubst t

idempotent : {tn : nat} -> typeSubstitution tn tn -> Set
idempotent sub = sub ∘ sub == sub

_fixedPoint_ : {tn : nat} -> type tn -> typeSubstitution tn tn -> Set
_fixedPoint_ t sub = applyTsubst sub t == t

_unmoved_ : {tn : nat} -> fin tn -> typeSubstitution tn tn -> Set
tv unmoved sub = TyVar tv fixedPoint sub

unifier : {tn tn' : nat} -> type tn -> type tn -> typeSubstitution tn tn' -> Set
unifier t1 t2 sub = applyTsubst sub t1 == applyTsubst sub t2

_extends_ : {tn tn' tn'' : nat} -> typeSubstitution tn tn'' -> typeSubstitution tn tn' -> Set
_extends_ {tn} {tn'} {tn''} sub' sub = typeSubstitution tn' tn'' * λ sub'' -> sub' == sub'' ∘ sub

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

occursLemma : {tn : nat} (tv : fin tn) (t : type tn) (sub : typeSubstitution tn tn) -> t contains tv -> not (t == TyVar tv) ->
  occursSize (applyTsubst sub t) > occursSize (applyTsubst sub (TyVar tv))
occursLemmaVect : {n tn : nat} (tv : fin tn) (ts : vect (type tn) n) (sub : typeSubstitution tn tn) (cont : ts containsVect tv) -> 
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

occursCheck : {tn : nat} (tv : fin tn) (t : type tn) (sub : typeSubstitution tn tn) -> t contains tv -> unifier (TyVar tv) t sub -> t == TyVar tv
occursCheck tv t sub cont eq with typeEq t (TyVar tv)
occursCheck tv _ sub cont eq | Yes Refl = Refl
occursCheck tv t sub cont eq | No neq   with occursLemma tv t sub cont neq 
occursCheck tv t sub cont eq | No neq   | lem rewrite eq with sucNrefl lem
occursCheck tv t sub cont eq | No neq   | lem | ()

unsafeExtend : {tn : nat} (sub : typeSubstitution tn tn) (tv : fin tn) (t : type tn) -> typeSubstitution tn tn
unsafeExtend sub tv t = deltaSubst tv t ∘ sub

extend : {tn : nat} (sub : typeSubstitution tn tn) (tv : fin tn) (t : type tn) -> idempotent sub -> t fixedPoint sub -> tv unmoved sub -> 
  decide (typeSubstitution tn tn * λ sub' -> idempotent sub' × (sub' extends sub) × unifier (TyVar tv) t sub')
extend {tn} sub tv t  id fx fx2 with typeEq t (TyVar tv)
extend {tn} sub tv ._ id fx fx2 | Yes Refl = Yes (sub , id , (sub , sym id) , Refl)
extend {tn} sub tv t  id fx fx2 | No neq with tv ∈ t
extend {tn} sub tv t  id fx fx2 | No neq | Yes i = No (λ { (sub , _ , _ , u) -> neq (occursCheck tv t sub i u) })
extend {tn} sub tv t  id fx fx2 | No neq | No ni = Yes (unsafeExtend sub tv t , idem sub tv t , (deltaSubst tv t , Refl) , unify fx2)
  where
    idem : {tn : nat} (sub : typeSubstitution tn tn) (tv : fin tn) (t : type tn) -> idempotent (unsafeExtend sub tv t)
    idem sub tv t rewrite tsubstCompAssoc (deltaSubst tv t) sub (unsafeExtend sub tv t) = {!!}

    unify : sub ! tv == TyVar tv -> unifier (TyVar tv) t (unsafeExtend sub tv t)
    unify fx3 rewrite mapLookup (applyTsubst (replace tv idSubst t)) sub tv | fx3 | replaceLookup tv idSubst t = {!!}
