module Sets where

open import Basics
open import Fin
open import Vect

_∈_ : {A : Set} {n : nat} (a : A) (as : vect A n) -> Set
_∈_ {A} {n} a as = fin n * (λ i -> (as ! i) == a)

data isSet {A : Set} : {n : nat} -> vect A n -> Set where 
  EmptySet : isSet []
  Insert : {n : nat} {as : vect A n} (a : A) -> isSet as -> not (a ∈ as) -> isSet (a :: as)

in? : {A : Set} {n : nat} -> equality A -> (a : A) (as : vect A n) -> decide (a ∈ as)
in? {A} {Zero}  eq a []         = No (λ { (() , y) })
in? {A} {Suc n} eq a (a' :: as) with eq a a'
in? {A} {Suc n} eq a (.a :: as) | Yes Refl = Yes (FZ , Refl)
in? {A} {Suc n} eq a (a' :: as) | No neq   with in? eq a as
in? {A} {Suc n} eq a (a' :: as) | No neq   | Yes (i , pf) = Yes (FS i , pf)
in? {A} {Suc n} eq a (a' :: as) | No neq   | No nmem'     = No (inLemma a a' as neq nmem')
  where 
    inLemma : (a a' : A) (as : vect A n) -> not (a == a') -> not (fin n * (λ i → (as ! i) == a)) -> not (fin (Suc n) * (λ i → ((a' :: as) ! i) == a))
    inLemma a .a as neq nmem (FZ , Refl)  = neq Refl
    inLemma a a' as neq nmem (FS i , mem) = nmem (i , mem)

remove : {A : Set} {n : nat} (a : A) (as : vect A (Suc n)) -> a ∈ as -> vect A n
remove {A} {n}     a (.a :: as) (FZ , Refl)   = as
remove {A} {Zero}  a (a' :: as) (FS () , mem)
remove {A} {Suc n} a (a' :: as) (FS i , mem)  = a' :: remove a as (i , mem)

removeSetLemma : {A : Set} {n : nat} (a a' : A) (as : vect A (Suc n)) (mem : a ∈ as) -> not (a' ∈ as) -> not (a' ∈ remove a as mem)
removeSetLemma a a' (.a :: as)  (FZ , Refl)  nmem (i' , mem')    = nmem (FS i' , mem')
removeSetLemma a a' (.a' :: as) (FS i , mem) nmem (FZ , Refl)    = nmem (FZ , Refl)
removeSetLemma a a' (a2 :: as)  (FS i , mem) nmem (FS i' , mem') = removeSetLemma a a' as (i , mem) (λ { (i2 , mem2) -> nmem (FS i2 , mem2) }) (i' , mem')

removeSet : {A : Set} {n : nat} (a : A) (as : vect A (Suc n)) (mem : a ∈ as) -> isSet as -> isSet (remove a as mem)
removeSet {A} {n}     a (.a :: as) (FZ , Refl)   (Insert .a is nmem)  = is
removeSet {A} {Zero}  a (a' :: as) (FS () , mem) (Insert .a' is nmem)
removeSet {A} {Suc n} a (a' :: as) (FS i , mem)  (Insert .a' is nmem) = Insert a' (removeSet a as (i , mem) is) (removeSetLemma a a' as (i , mem) nmem)

removeRemoves : {A : Set} {n : nat} (a : A) (as : vect A (Suc n)) (mem : a ∈ as) -> isSet as -> not (a ∈ remove a as mem)
removeRemoves {A} {n}     a (.a :: as) (FZ , Refl)   (Insert .a is nmem)  mem'           = nmem mem'
removeRemoves {A} {Zero}  a (a' :: as) (FS () , mem) (Insert .a' is nmem) (i' , mem')
removeRemoves {A} {Suc n} a (.a :: as) (FS i , mem)  (Insert .a is nmem)  (FZ , Refl)    = nmem (i , mem)
removeRemoves {A} {Suc n} a (a' :: as) (FS i , mem)  (Insert .a' is nmem) (FS i' , mem') = removeRemoves a as (i , mem) is (i' , mem')
