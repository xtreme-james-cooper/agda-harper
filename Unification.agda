module Unification where

open import Basics
open import Nat
open import Vect
open import Type
open import Substitution

extendTrans : {tn : nat} {sub1 sub2 sub3 : typeSubstitution tn} -> sub2 extends sub1 -> sub3 extends sub2 -> sub3 extends sub1
extendTrans {tn} {sub1} {sub2} {sub3} (sub12 , ext12) (sub23 , ext23) = {!!} , λ t -> {!!}

extendUnifyPersist : {tn : nat} {sub sub' : typeSubstitution tn} (t1 t2 : type tn) -> sub' extends sub -> applyTsubst sub t1 == applyTsubst sub t2 -> 
  applyTsubst sub' t1 == applyTsubst sub' t2
extendUnifyPersist t1 t2 (sub'' , ext) uni rewrite ext t1 | ext t2 | uni = Refl

impossibleUniT : {tn n1 n2 : nat} (sub : typeSubstitution tn) (ts1 : vect (type tn) n1) (ts2 : vect (type tn) n2) -> not (n1 == n2) ->
  not (Tuple (applyTsubstVect sub ts1) == Tuple (applyTsubstVect sub ts2))
impossibleUniT sub []          []          neq uni = neq Refl
impossibleUniT sub []          (t2 :: ts2) neq ()
impossibleUniT sub (t1 :: ts1) []          neq ()
impossibleUniT sub (t1 :: ts1) (t2 :: ts2) neq uni = impossibleUniT sub ts1 ts2 (neqSDown neq) (lemma _ _ _ _ uni)
  where
    lemma : {tn n1 n2 : nat} (t1 t2 : type tn) (ts1 : vect (type tn) n1) (ts2 : vect (type tn) n2) -> Tuple (t1 :: ts1) == Tuple (t2 :: ts2) -> Tuple ts1 == Tuple ts2
    lemma t .t ts .ts Refl = Refl

impossibleUniV : {tn n1 n2 : nat} (sub : typeSubstitution tn) (ts1 : vect (type tn) n1) (ts2 : vect (type tn) n2) -> not (n1 == n2) ->
  not (Variant (applyTsubstVect sub ts1) == Variant (applyTsubstVect sub ts2))
impossibleUniV sub []          []          neq uni = neq Refl
impossibleUniV sub []          (t2 :: ts2) neq ()
impossibleUniV sub (t1 :: ts1) []          neq ()
impossibleUniV sub (t1 :: ts1) (t2 :: ts2) neq uni = impossibleUniV sub ts1 ts2 (neqSDown neq) (lemma _ _ _ _ uni)
  where
    lemma : {tn n1 n2 : nat} (t1 t2 : type tn) (ts1 : vect (type tn) n1) (ts2 : vect (type tn) n2) -> Variant (t1 :: ts1) == Variant (t2 :: ts2) -> Variant ts1 == Variant ts2
    lemma t .t ts .ts Refl = Refl

arrowUni : {tn : nat} {t1 t2 t3 t4 : type tn} -> t1 == t3 -> t2 == t4 -> (t1 => t2) == (t3 => t4)
arrowUni Refl Refl = Refl

arrowDown1 : {tn : nat} (t1 t2 t3 t4 : type tn) -> (t1 => t2) == (t3 => t4) -> t1 == t3
arrowDown1 t1 t2 .t1 .t2 Refl = Refl
arrowDown2 : {tn : nat} (t1 t2 t3 t4 : type tn) -> (t1 => t2) == (t3 => t4) -> t2 == t4
arrowDown2 t1 t2 .t1 .t2 Refl = Refl
varDown : {tn n : nat} (ts1 ts2 : vect (type tn) n) -> Variant ts1 == Variant ts2 -> ts1 == ts2
varDown ts1 .ts1 Refl = Refl
tupDown : {tn n : nat} (ts1 ts2 : vect (type tn) n) -> Tuple ts1 == Tuple ts2 -> ts1 == ts2
tupDown ts1 .ts1 Refl = Refl
consDown1 : {tn n : nat} (t1 t2 : type tn) (ts1 ts2 : vect (type tn) n)  -> (t1 :: ts1) == (t2 :: ts2) -> t1 == t2
consDown1 t1 .t1 ts1 .ts1 Refl = Refl
consDown2 : {tn n : nat} (t1 t2 : type tn) (ts1 ts2 : vect (type tn) n)  -> (t1 :: ts1) == (t2 :: ts2) -> ts1 == ts2
consDown2 t1 .t1 ts1 .ts1 Refl = Refl

unify : {tn : nat} (sub : typeSubstitution tn) (t1 t2 : type tn) -> decide (typeSubstitution tn * λ sub' -> unifier t1 t2 sub' × sub' extends sub)
unifyVect : {tn n : nat} (sub : typeSubstitution tn) (t1 t2 : vect (type tn) n) -> decide (typeSubstitution tn * λ sub' -> unifierVect t1 t2 sub' × sub' extends sub)
unify sub (TyVar tv)         t2                  = {!!}
unify sub (t11 => t12)       (TyVar x)           = {!!}
unify sub (t11 => t12)       (t21 => t22)        with unify sub t11 t21
unify sub (t11 => t12)       (t21 => t22)        | Yes (sub' , uni , ext) with unify sub' t12 t22
unify sub (t11 => t12)       (t21 => t22)        | Yes (sub' , uni , ext) | Yes (sub'' , uni' , ext') =
  Yes (sub'' , arrowUni (extendUnifyPersist t11 t21 ext' uni) uni' , extendTrans ext ext')
unify sub (t11 => t12)       (t21 => t22)        | Yes (sub' , uni , ext) | No nsub                   = 
  No (λ { (sub'' , uni' , ext') -> nsub (sub'' , arrowDown2 _ _ _ _ uni' , {!!}) })
unify sub (t11 => t12)       (t21 => t22)        | No nsub                = No (λ { (sub' , uni , ext) -> nsub (sub' , arrowDown1 _ _ _ _ uni , ext) })
unify sub (t11 => t12)       (Tuple ts)          = No (λ { (sub' , () , ext) })
unify sub (t11 => t12)       (Variant ts)        = No (λ { (sub' , () , ext) })
unify sub (Tuple {n1} ts1)   (TyVar x)           = {!!}
unify sub (Tuple {n1} ts1)   (t21 => t22)        = No (λ { (sub' , () , ext) })
unify sub (Tuple {n1} ts1)   (Tuple {n2} ts2)    with natEq n1 n2
unify sub (Tuple {n1} ts1)   (Tuple {.n1} ts2)   | Yes Refl with unifyVect sub ts1 ts2
unify sub (Tuple {n1} ts1)   (Tuple {.n1} ts2)   | Yes Refl | Yes (sub' , uni , ext) = Yes (sub' , funEq Tuple uni , ext)
unify sub (Tuple {n1} ts1)   (Tuple {.n1} ts2)   | Yes Refl | No nsub                = No (λ { (sub' , uni , ext) -> nsub (sub' , tupDown _ _ uni , ext) })
unify sub (Tuple {n1} ts1)   (Tuple {n2} ts2)    | No neq   = No (λ { (sub' , uni , ext) -> impossibleUniT sub' ts1 ts2 neq uni })
unify sub (Tuple {n1} ts1)   (Variant ts2)       = No (λ { (sub' , () , ext) })
unify sub (Variant {n1} ts1) (TyVar x)           = {!!}
unify sub (Variant {n1} ts1) (t21 => t22)        = No (λ { (sub' , () , ext) })
unify sub (Variant {n1} ts1) (Tuple ts2)         = No (λ { (sub' , () , ext) })
unify sub (Variant {n1} ts1) (Variant {n2} ts2)  with natEq n1 n2
unify sub (Variant {n1} ts1) (Variant {.n1} ts2) | Yes Refl with unifyVect sub ts1 ts2
unify sub (Variant {n1} ts1) (Variant {.n1} ts2) | Yes Refl | Yes (sub' , uni , ext) = Yes (sub' , funEq Variant uni , ext)
unify sub (Variant {n1} ts1) (Variant {.n1} ts2) | Yes Refl | No nsub                = No (λ { (sub' , uni , ext) -> nsub (sub' , varDown _ _ uni , ext) })
unify sub (Variant {n1} ts1) (Variant {n2} ts2)  | No neq   = No (λ { (sub' , uni , ext) -> impossibleUniV sub' ts1 ts2 neq uni })
unifyVect sub [] []                   = Yes (sub , Refl , extendsRefl sub)
unifyVect sub (t1 :: ts1) (t2 :: ts2) with unifyVect sub ts1 ts2
unifyVect sub (t1 :: ts1) (t2 :: ts2) | Yes (sub' , uni , ext) with unify sub' t1 t2
unifyVect sub (t1 :: ts1) (t2 :: ts2) | Yes (sub' , uni , ext) | Yes (sub'' , uni' , ext') = Yes (sub'' , {!!} , {!!})
unifyVect sub (t1 :: ts1) (t2 :: ts2) | Yes (sub' , uni , ext) | No nsub                   = 
  No (λ { (sub'' , uni' , ext') -> nsub (sub'' , consDown1 _ _ _ _ uni' , {!!}) })
unifyVect sub (t1 :: ts1) (t2 :: ts2) | No nsub                = No (λ { (sub' , uni , ext) -> nsub (sub' , consDown2 _ _ _ _ uni , ext) })
