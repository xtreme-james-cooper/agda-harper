module Substitution where

open import Basics
open import Nat
open import Fin
open import Vect
open import Sets
open import Type
open import RawTerm
open import Term

subBody : (tn : nat) {domsize : nat} (dom : vect (fin tn) domsize) -> Set
subBody tn dom = (x : fin tn) -> (x ∈ dom × type tn * λ t -> ((y : fin tn) -> t contains y -> not (y ∈ dom))) \/ not (x ∈ dom)

data typeSubstitution (tn : nat) : Set where
  TSubst : {domsize : nat} (dom : vect (fin tn) domsize) -> subBody tn dom -> isSet dom -> typeSubstitution tn

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

idSubst : {tn : nat} -> typeSubstitution tn
idSubst = TSubst [] (λ x -> InR (λ { (() , _) })) EmptySet

idempotentLemma : {tn : nat} {domsize : nat} (t : type tn) (dom : vect (fin tn) domsize) (mv : (y : fin tn) -> t contains y -> not (y ∈ dom))
    (sub : subBody tn dom) (is : isSet dom) -> applyTsubst (TSubst dom sub is) t == t
idempotentLemmaVect : {tn n : nat} {domsize : nat} (ts : vect (type tn) n) (dom : vect (fin tn) domsize) (mv : (y : fin tn) -> ts containsVect y -> not (y ∈ dom))
    (sub : subBody tn dom) (is : isSet dom) -> applyTsubstVect (TSubst dom sub is) ts == ts
idempotentLemma (TyVar tv)   dom mv sub is with sub tv 
idempotentLemma (TyVar tv)   dom mv sub is | InL (mem , t , _) with mv tv TyVarCont mem
idempotentLemma (TyVar tv)   dom mv sub is | InL (mem , t , _) | ()
idempotentLemma (TyVar tv)   dom mv sub is | InR _             = Refl
idempotentLemma (t1 => t2)   dom mv sub is 
  rewrite idempotentLemma t1 dom (λ y cont -> mv y (ArrowCont1 t1 t2 cont)) sub is | idempotentLemma t2 dom (λ y cont -> mv y (ArrowCont2 t1 t2 cont)) sub is = Refl
idempotentLemma (Tuple ts)   dom mv sub is rewrite idempotentLemmaVect ts dom (λ y cont -> mv y (TupleCont ts cont)) sub is = Refl
idempotentLemma (Variant ts) dom mv sub is rewrite idempotentLemmaVect ts dom (λ y cont -> mv y (VariantCont ts cont)) sub is = Refl
idempotentLemmaVect []        dom mv sub is = Refl
idempotentLemmaVect (t :: ts) dom mv sub is
  rewrite idempotentLemma t dom (λ y cont -> mv y (ConsCont1 t ts cont)) sub is | idempotentLemmaVect ts dom (λ y cont -> mv y (ConsCont2 t ts cont)) sub is = Refl

idempotentVar : {tn : nat} (sub : typeSubstitution tn) (tv : fin tn) -> applyTsubst sub (applySubstVar sub tv) == applySubstVar sub tv
idempotentVar (TSubst dom sub is) tv with sub tv | inspect sub tv
idempotentVar (TSubst dom sub is) tv | InL (mem , t , mv) | [ pf ] = idempotentLemma t dom mv sub is
idempotentVar (TSubst dom sub is) tv | InR _              | [ pf ] with sub tv
idempotentVar (TSubst dom sub is) tv | InR _              | [ () ] | InL _
idempotentVar (TSubst dom sub is) tv | InR _              | [ pf ] | InR _ = Refl

idempotent : {tn : nat} (sub : typeSubstitution tn) (t : type tn) -> applyTsubst sub (applyTsubst sub t) == applyTsubst sub t
idempotentVect : {tn n : nat} (sub : typeSubstitution tn) (ts : vect (type tn) n) -> applyTsubstVect sub (applyTsubstVect sub ts) == applyTsubstVect sub ts
idempotent sub (TyVar tv)   = idempotentVar sub tv
idempotent sub (t1 => t2)   rewrite idempotent sub t1 | idempotent sub t2 = Refl
idempotent sub (Tuple ts)   rewrite idempotentVect sub ts = Refl
idempotent sub (Variant ts) rewrite idempotentVect sub ts = Refl
idempotentVect sub []        = Refl
idempotentVect sub (t :: ts) rewrite idempotentVect sub ts | idempotent sub t = Refl

_fixedPoint_ : {tn : nat} -> type tn -> typeSubstitution tn -> Set
_fixedPoint_ {tn} t (TSubst dom sub id) = (tv : fin tn) -> tv ∈ dom -> not (t contains tv)

_fixedPointVect_ : {tn n : nat} -> vect (type tn) n -> typeSubstitution tn -> Set
_fixedPointVect_ {tn} ts (TSubst dom sub id) = (tv : fin tn) -> tv ∈ dom -> not (ts containsVect tv)

_unmoved_ : {tn : nat} -> fin tn -> typeSubstitution tn -> Set
tv unmoved (TSubst dom sub id) = not (tv ∈ dom)

fixedPointIsFixed : {tn : nat} (t : type tn) (sub : typeSubstitution tn) -> t fixedPoint sub -> applyTsubst sub t == t
fixedPointIsFixedVect : {tn n : nat} (ts : vect (type tn) n) (sub : typeSubstitution tn) -> ts fixedPointVect sub -> applyTsubstVect sub ts == ts
fixedPointIsFixed {tn} (TyVar tv)   (TSubst dom sub id) fix with sub tv
fixedPointIsFixed {tn} (TyVar tv)   (TSubst dom sub id) fix | InL (mem , t , _) with fix tv mem TyVarCont
fixedPointIsFixed {tn} (TyVar tv)   (TSubst dom sub id) fix | InL (mem , t , _) | ()
fixedPointIsFixed {tn} (TyVar tv)   (TSubst dom sub id) fix | InR _             = Refl
fixedPointIsFixed {tn} (t1 => t2)   (TSubst dom sub id) fix 
  rewrite fixedPointIsFixed t1 (TSubst dom sub id) (λ tv mem cont -> fix tv mem (ArrowCont1 t1 t2 cont)) 
        | fixedPointIsFixed t2 (TSubst dom sub id) (λ tv mem cont -> fix tv mem (ArrowCont2 t1 t2 cont)) = Refl
fixedPointIsFixed {tn} (Tuple ts)   (TSubst dom sub id) fix rewrite fixedPointIsFixedVect ts (TSubst dom sub id) (λ tv mem cont -> fix tv mem (TupleCont ts cont)) = Refl
fixedPointIsFixed {tn} (Variant ts) (TSubst dom sub id) fix rewrite fixedPointIsFixedVect ts (TSubst dom sub id) (λ tv mem cont -> fix tv mem (VariantCont ts cont)) = Refl
fixedPointIsFixedVect {tn} []        (TSubst dom sub id) fix = Refl
fixedPointIsFixedVect {tn} (t :: ts) (TSubst dom sub id) fix 
  rewrite fixedPointIsFixed t (TSubst dom sub id) (λ tv mem cont -> fix tv mem (ConsCont1 t ts cont)) 
        | fixedPointIsFixedVect ts (TSubst dom sub id) (λ tv mem cont -> fix tv mem (ConsCont2 t ts cont)) = Refl

unmovedDoesNotMove : {tn : nat} (tv : fin tn) (sub : typeSubstitution tn) -> tv unmoved sub -> applySubstVar sub tv == TyVar tv
unmovedDoesNotMove tv (TSubst dom sub is) unm with sub tv
unmovedDoesNotMove tv (TSubst dom sub is) unm | InL (mem , _ , _) with unm mem
unmovedDoesNotMove tv (TSubst dom sub is) unm | InL (mem , _ , _) | ()
unmovedDoesNotMove tv (TSubst dom sub is) unm | InR nmem          = Refl

unifier : {tn : nat} -> type tn -> type tn -> typeSubstitution tn -> Set
unifier t1 t2 sub = applyTsubst sub t1 == applyTsubst sub t2

{-

_extends_ : {tn : nat} -> typeSubstitution tn -> typeSubstitution tn -> Set
_extends_ {tn} sub' sub = typeSubstitution tn * λ sub'' -> sub' == sub'' ∘ sub

mostGeneralUnifier : {tn : nat} (t1 t2 : type tn) (sub : typeSubstitution tn) -> Set
mostGeneralUnifier {tn} t1 t2 sub = unifier t1 t2 sub × ((sub' : typeSubstitution tn) -> unifier t1 t2 sub' -> sub' extends sub)

-}

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

delta : {tn : nat} (tv : fin tn) (t : type tn) -> not (t contains tv) -> typeSubstitution tn
delta {tn} tv t ni = TSubst (tv :: []) delta' (Insert tv EmptySet (λ { (() , b) }))
  where
    delta' : (x : fin tn) -> (x ∈ tv :: [] × type tn * (λ t' → (y : fin tn) → t' contains y → not (y ∈ tv :: []))) \/ not (x ∈ tv :: [])
    delta' x   with finEq tv x
    delta' .tv | Yes Refl = InL ((FZ , Refl) , t , (λ { .tv cont (FZ , Refl) -> ni cont ; y cont (FS () , i) }))
    delta' x   | No neq   = InR (λ { (FZ , i) -> neq i ; (FS () , _) })

deltaClears : {tn : nat} (tv : fin tn) (t t' : type tn) (ni : not (t' contains tv)) -> not (applyTsubst (delta tv t' ni) t contains tv)
deltaClearsVect : {tn n : nat} (tv : fin tn) (ts : vect (type tn) n) (t' : type tn) (ni : not (t' contains tv)) -> not (applyTsubstVect (delta tv t' ni) ts containsVect tv)
deltaClears tv (TyVar tv')  t' ni cont                  with finEq tv tv'
deltaClears tv (TyVar .tv)  t' ni cont                  | Yes Refl = ni cont
deltaClears tv (TyVar .tv)  t' ni TyVarCont             | No neq = neq Refl
deltaClears tv (t1 => t2)   t' ni (ArrowCont1 _ _ cont) = deltaClears tv t1 t' ni cont
deltaClears tv (t1 => t2)   t' ni (ArrowCont2 _ _ cont) = deltaClears tv t2 t' ni cont
deltaClears tv (Tuple ts)   t' ni (TupleCont _ cont)    = deltaClearsVect tv ts t' ni cont
deltaClears tv (Variant ts) t' ni (VariantCont _ cont)  = deltaClearsVect tv ts t' ni cont
deltaClearsVect tv []        t' ni ()
deltaClearsVect tv (t :: ts) t' ni (ConsCont1 _ _ cont) = deltaClears tv t t' ni cont
deltaClearsVect tv (t :: ts) t' ni (ConsCont2 _ _ cont) = deltaClearsVect tv ts t' ni cont

deltaLimitedVars : {tn : nat} (tv tv' : fin tn) (t t' : type tn) (ni : not (t' contains tv)) -> applyTsubst (delta tv t' ni) t contains tv' ->
  (t contains tv') \/ (t' contains tv')
deltaLimitedVarsVect : {tn n : nat} (tv tv' : fin tn) (ts : vect (type tn) n) (t' : type tn) (ni : not (t' contains tv)) -> 
  applyTsubstVect (delta tv t' ni) ts containsVect tv' -> (ts containsVect tv') \/ (t' contains tv')
deltaLimitedVars tv tv' (TyVar x)    t' ni cont                  with finEq tv x
deltaLimitedVars tv tv' (TyVar .tv)  t' ni cont                  | Yes Refl = InR cont
deltaLimitedVars tv tv' (TyVar .tv') t' ni TyVarCont             | No neq   = InL TyVarCont
deltaLimitedVars tv tv' (t1 => t2)   t' ni (ArrowCont1 _ _ cont) with deltaLimitedVars tv tv' t1 t' ni cont
deltaLimitedVars tv tv' (t1 => t2)   t' ni (ArrowCont1 _ _ cont) | InL c = InL (ArrowCont1 t1 t2 c)
deltaLimitedVars tv tv' (t1 => t2)   t' ni (ArrowCont1 _ _ cont) | InR c = InR c
deltaLimitedVars tv tv' (t1 => t2)   t' ni (ArrowCont2 _ _ cont) with deltaLimitedVars tv tv' t2 t' ni cont
deltaLimitedVars tv tv' (t1 => t2)   t' ni (ArrowCont2 _ _ cont) | InL c = InL (ArrowCont2 t1 t2 c)
deltaLimitedVars tv tv' (t1 => t2)   t' ni (ArrowCont2 _ _ cont) | InR c = InR c
deltaLimitedVars tv tv' (Tuple ts)   t' ni (TupleCont _ cont)    with deltaLimitedVarsVect tv tv' ts t' ni cont
deltaLimitedVars tv tv' (Tuple ts)   t' ni (TupleCont _ cont)    | InL c = InL (TupleCont ts c)
deltaLimitedVars tv tv' (Tuple ts)   t' ni (TupleCont _ cont)    | InR c = InR c
deltaLimitedVars tv tv' (Variant ts) t' ni (VariantCont _ cont)  with deltaLimitedVarsVect tv tv' ts t' ni cont
deltaLimitedVars tv tv' (Variant ts) t' ni (VariantCont _ cont)  | InL c = InL (VariantCont ts c)
deltaLimitedVars tv tv' (Variant ts) t' ni (VariantCont _ cont)  | InR c = InR c
deltaLimitedVarsVect tv tv' []        t' ni ()
deltaLimitedVarsVect tv tv' (t :: ts) t' ni (ConsCont1 _ _ cont) with deltaLimitedVars tv tv' t t' ni cont
deltaLimitedVarsVect tv tv' (t :: ts) t' ni (ConsCont1 _ _ cont) | InL c = InL (ConsCont1 t ts c)
deltaLimitedVarsVect tv tv' (t :: ts) t' ni (ConsCont1 _ _ cont) | InR c = InR c
deltaLimitedVarsVect tv tv' (t :: ts) t' ni (ConsCont2 _ _ cont) with deltaLimitedVarsVect tv tv' ts t' ni cont
deltaLimitedVarsVect tv tv' (t :: ts) t' ni (ConsCont2 _ _ cont) | InL c = InL (ConsCont2 t ts c)
deltaLimitedVarsVect tv tv' (t :: ts) t' ni (ConsCont2 _ _ cont) | InR c = InR c

extend : {tn : nat} (sub : typeSubstitution tn) (tv : fin tn) (t : type tn) -> t fixedPoint sub -> tv unmoved sub -> 
  decide (typeSubstitution tn * λ sub' -> unifier (TyVar tv) t sub')
extend {tn} (TSubst dom sub is) tv t fx fx2 with typeEq t (TyVar tv)
extend {tn} (TSubst dom sub is) tv _ fx fx2 | Yes Refl = Yes (TSubst dom sub is , Refl)
extend {tn} (TSubst dom sub is) tv t fx fx2 | No neq with tv ∈t t
extend {tn} (TSubst dom sub is) tv t fx fx2 | No neq | Yes i = No (λ { (sub , u) -> neq (occursCheck tv t sub i u) })
extend {tn} (TSubst dom sub is) tv t fx fx2 | No neq | No ni = Yes (sub' , unify)
  where
    subBody' : subBody tn (tv :: dom)
    subBody' x   with sub x
    subBody' x   | InL ((ix , i) , t' , mv) = InL ((FS ix , i) , applyTsubst (delta tv t ni) t' , lemma)
      where
        lemma : (y : fin tn) -> applyTsubst (delta tv t ni) t' contains y -> not (y ∈ tv :: dom)
        lemma .tv cont (FZ , Refl) = deltaClears tv t' t ni cont
        lemma y   cont (FS ix , i) with deltaLimitedVars tv y t' t ni cont 
        lemma y   cont (FS ix , i) | InL tmem = mv y tmem (ix , i)
        lemma y   cont (FS ix , i) | InR tmem = fx y (ix , i) tmem
    subBody' x   | InR nmem                 with finEq tv x
    subBody' .tv | InR nmem                 | Yes Refl with contains? finEq dom tv
    subBody' .tv | InR nmem                 | Yes Refl | Yes mem  with nmem mem
    subBody' .tv | InR nmem                 | Yes Refl | Yes mem  | ()
    subBody' .tv | InR nmem                 | Yes Refl | No nmem' = InL ((FZ , Refl) , t , lemma)
      where
        lemma : (y : fin tn) -> t contains y -> not (y ∈ tv :: dom)
        lemma .tv cont (FZ , Refl) = ni cont
        lemma y   cont (FS ix , i) = fx y (ix , i) cont
    subBody' x   | InR nmem                 | No neq   = InR (λ { (FZ , i) -> neq i ; (FS ix , i) -> nmem (ix , i) })

    sub' : typeSubstitution tn
    sub' = TSubst (tv :: dom) subBody' (Insert tv is fx2)

    tunmoved : applyTsubst sub' t == t
    tunmoved = {!!}

    unify : applySubstVar sub' tv == applyTsubst sub' t
    unify with sub tv 
    unify | InL (mem , t' , mv) with fx2 mem
    unify | InL (mem , t' , mv) | ()
    unify | InR nmem            with finEq tv tv
    unify | InR nmem            | Yes Refl with contains? finEq dom tv
    unify | InR nmem            | Yes Refl | Yes mem  with nmem mem
    unify | InR nmem            | Yes Refl | Yes mem  | ()
    unify | InR nmem            | Yes Refl | No nmem' = sym tunmoved
    unify | InR nmem            | No neq   with neq Refl
    unify | InR nmem            | No neq   | ()
