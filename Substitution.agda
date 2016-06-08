module Substitution where

open import Basics
open import Nat
open import Fin
open import Vect
open import Sets
open import Type
open import RawTerm
open import Term

data typeSubstitution (tn : nat) : Set where
  TSubst : {domsize : nat} (dom : vect (fin tn) domsize) 
    (sub : (x : fin tn) -> (x ∈ dom × type tn * λ t -> ((y : fin tn) -> t contains y -> not (y ∈ dom))) \/ not (x ∈ dom)) -> isSet dom -> typeSubstitution tn

applySubstVar : {tn : nat} -> typeSubstitution tn -> fin tn -> type tn
applySubstVar (TSubst dom sub is) tv with sub tv
applySubstVar (TSubst dom sub is) tv | InL (_ , t , _) = t
applySubstVar (TSubst dom sub is) tv | InR _           = TyVar tv

applyTsubst : {tn : nat} -> typeSubstitution tn -> type tn -> type tn
applyTsubstVect : {n tn : nat} -> typeSubstitution tn -> vect (type tn) n -> vect (type tn) n
applyTsubst sub (TyVar tv)   = applySubstVar sub tv
applyTsubst sub (t1 => t2)   = applyTsubst sub t1 => applyTsubst sub t2
applyTsubst sub (Tuple ts)   = Tuple (applyTsubstVect sub ts)
applyTsubst sub (Variant ts) = Variant (applyTsubstVect sub ts)
applyTsubstVect sub []        = []
applyTsubstVect sub (t :: ts) = applyTsubst sub t :: applyTsubstVect sub ts

_∘_ : {tn : nat} -> typeSubstitution tn -> typeSubstitution tn -> typeSubstitution tn
_∘_ {tn} (TSubst dom1 sub1 is1) (TSubst dom2 sub2 is2) with union finEq dom1 dom2 | inspect (union finEq dom1) dom2
_∘_ {tn} (TSubst dom1 sub1 is1) (TSubst dom2 sub2 is2) | domsize , dom3           | [ eq ] = 
  TSubst dom3 sub3 (unionRemainsSet finEq dom1 dom2 dom3 is1 is2 eq)
  where 
    sub3 : (x : fin tn) -> (x ∈ dom3 × type tn * λ t -> ((y : fin tn) -> t contains y -> not (y ∈ dom3))) \/ not (x ∈ dom3)
    sub3 x with sub2 x
    sub3 x | InL (mem , t , mv) with typeEq (applyTsubst (TSubst dom1 sub1 is1) t) (TyVar x)
    sub3 x | InL (mem , t , mv) | Yes _  = InR {!!}
    sub3 x | InL (mem , t , mv) | No neq = InL (unionPreserves2 finEq x dom1 dom2 dom3 mem eq , applyTsubst (TSubst dom1 sub1 is1) t , {!!})
    sub3 x | InR nmem           with sub1 x
    sub3 x | InR nmem           | InL (mem , t , mv) = InL (unionPreserves1 finEq x dom1 dom2 dom3 mem eq , t , {!!})
    sub3 x | InR nmem           | InR nmem2          = InR (unionDoesNotAdd finEq x dom1 dom2 dom3 nmem2 nmem eq)

infixr 50 _∘_

idSubst : {tn : nat} -> typeSubstitution tn
idSubst = TSubst [] (λ x -> InR (λ { (() , _) })) EmptySet

idempotent : {tn : nat} (sub : typeSubstitution tn) -> sub ∘ sub == sub
idempotent (TSubst dom sub x) = {!!}

_fixedPoint_ : {tn : nat} -> type tn -> typeSubstitution tn -> Set
t fixedPoint sub = applyTsubst sub t == t

_unmoved_ : {tn : nat} -> fin tn -> typeSubstitution tn -> Set
tv unmoved (TSubst dom sub id) = not (tv ∈ dom)

unmovedDoesNotMove : {tn : nat} (tv : fin tn) (sub : typeSubstitution tn) -> tv unmoved sub -> applySubstVar sub tv == TyVar tv
unmovedDoesNotMove tv (TSubst dom sub is) unm with sub tv
unmovedDoesNotMove tv (TSubst dom sub is) unm | InL (mem , _ , _) with unm mem
unmovedDoesNotMove tv (TSubst dom sub is) unm | InL (mem , _ , _) | ()
unmovedDoesNotMove tv (TSubst dom sub is) unm | InR nmem          = Refl

unifier : {tn : nat} -> type tn -> type tn -> typeSubstitution tn -> Set
unifier t1 t2 sub = applyTsubst sub t1 == applyTsubst sub t2

_extends_ : {tn : nat} -> typeSubstitution tn -> typeSubstitution tn -> Set
_extends_ {tn} sub' sub = typeSubstitution tn * λ sub'' -> sub' == sub'' ∘ sub

mostGeneralUnifier : {tn : nat} (t1 t2 : type tn) (sub : typeSubstitution tn) -> Set
mostGeneralUnifier {tn} t1 t2 sub = unifier t1 t2 sub × ((sub' : typeSubstitution tn) -> unifier t1 t2 sub' -> sub' extends sub)

occursSize : {tn : nat} -> type tn -> nat
occursSizeVect : {n tn : nat} -> vect (type tn) n -> nat
occursSize (TyVar x)    = Zero
occursSize (t1 => t2)   = Suc (occursSize t1 + occursSize t2)
occursSize (Tuple ts)   = Suc (occursSizeVect ts)
occursSize (Variant ts) = Suc (occursSizeVect ts)
occursSizeVect []        = Zero
occursSizeVect (t :: ts) = Suc (occursSize t + occursSizeVect ts)

occursLemma : {tn : nat} (tv : fin tn) (t : type tn) (sub : typeSubstitution tn) -> t contains tv -> not (t == TyVar tv) ->
  occursSize (applyTsubst sub t) > occursSize (applyTsubst sub (TyVar tv))
occursLemmaVect : {n tn : nat} (tv : fin tn) (ts : vect (type tn) n) (sub : typeSubstitution tn) (cont : ts containsVect tv) -> 
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

occursCheck : {tn : nat} (tv : fin tn) (t : type tn) (sub : typeSubstitution tn) -> t contains tv -> unifier (TyVar tv) t sub -> t == TyVar tv
occursCheck tv t sub cont eq with typeEq t (TyVar tv)
occursCheck tv _ sub cont eq | Yes Refl = Refl
occursCheck tv t sub cont eq | No neq   with occursLemma tv t sub cont neq 
occursCheck tv t sub cont eq | No neq   | lem rewrite eq with sucNrefl lem
occursCheck tv t sub cont eq | No neq   | lem | ()

extend : {tn : nat} (sub : typeSubstitution tn) (tv : fin tn) (t : type tn) -> t fixedPoint sub -> tv unmoved sub -> 
  decide (typeSubstitution tn * λ sub' -> (sub' extends sub) × unifier (TyVar tv) t sub')
extend {tn} (TSubst dom sub is) tv t fx fx2 with typeEq t (TyVar tv)
extend {tn} (TSubst dom sub is) tv _ fx fx2 | Yes Refl = Yes (TSubst dom sub is , (TSubst dom sub is , sym (idempotent (TSubst dom sub is))) , Refl)
extend {tn} (TSubst dom sub is) tv t fx fx2 | No neq with tv ∈t t
extend {tn} (TSubst dom sub is) tv t fx fx2 | No neq | Yes i = No (λ { (sub , _ , u) -> neq (occursCheck tv t sub i u) })
extend {tn} (TSubst dom sub is) tv t fx fx2 | No neq | No ni = Yes (TSubst (tv :: dom) sub' (Insert tv is fx2) , {!!} , {!!})
  where
    sub' : (x : fin tn) -> (x ∈ (tv :: dom) × type tn * λ t -> ((y : fin tn) -> t contains y -> not (y ∈ tv :: dom))) \/ not (x ∈ (tv :: dom))
    sub' x   with sub x
    sub' x   | InL ((ix , i) , t' , mv) = InL ((FS ix , i) , applyTsubst (TSubst (tv :: []) {!!} (Insert tv EmptySet (λ { (() , _) }))) t' , {!!})
    sub' x   | InR nmem                 with finEq tv x
    sub' .tv | InR nmem                 | Yes Refl = InL (unionPreserves1 finEq tv (tv :: []) dom (tv :: dom) (FZ , Refl) {!!} , t , {!!})
    sub' x   | InR nmem                 | No neq   = InR (unionDoesNotAdd finEq x (tv :: []) dom (tv :: dom) (λ { (FZ , i) -> neq i ; (FS () , _) }) nmem {!!})

