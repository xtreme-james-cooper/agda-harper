module Sets where

open import Basics
open import Fin
open import Vect

_∈_ : {A : Set} {n : nat} (a : A) (as : vect A n) -> Set
_∈_ {A} {n} a as = fin n * (λ i -> (as ! i) == a)

finite : Set -> Set
finite A = nat * (λ n -> vect A n * (λ vals -> (a : A) -> a ∈ vals)) 

inCons : {A : Set} {n : nat} {a a' : A} {as : vect A n} -> a ∈ as -> a ∈ (a' :: as)
inCons (i , mem) = FS i , mem

data isSet {A : Set} : {n : nat} -> vect A n -> Set where 
  EmptySet : isSet []
  Insert : {n : nat} {as : vect A n} (a : A) -> isSet as -> not (a ∈ as) -> isSet (a :: as)

in? : {A : Set} {n : nat} -> equality A -> (a : A) (as : vect A n) -> decide (a ∈ as)
in? {A} {Zero}  eq a []         = No (λ { (() , y) })
in? {A} {Suc n} eq a (a' :: as) with eq a a'
in? {A} {Suc n} eq a (.a :: as) | Yes Refl = Yes (FZ , Refl)
in? {A} {Suc n} eq a (a' :: as) | No neq   with in? eq a as
in? {A} {Suc n} eq a (a' :: as) | No neq   | Yes mem  = Yes (inCons mem)
in? {A} {Suc n} eq a (a' :: as) | No neq   | No nmem' = No (inLemma a a' as neq nmem')
  where 
    inLemma : (a a' : A) (as : vect A n) -> not (a == a') -> not (fin n * (λ i → (as ! i) == a)) -> not (fin (Suc n) * (λ i -> ((a' :: as) ! i) == a))
    inLemma a .a as neq nmem (FZ , Refl)  = neq Refl
    inLemma a a' as neq nmem (FS i , mem) = nmem (i , mem)

remove : {A : Set} {n : nat} (a : A) (as : vect A (Suc n)) -> a ∈ as -> vect A n
remove {A} {n}     a (.a :: as) (FZ , Refl)   = as
remove {A} {Zero}  a (a' :: as) (FS () , mem)
remove {A} {Suc n} a (a' :: as) (FS i , mem)  = a' :: remove a as (i , mem)

removeRetainsOthers : {A : Set} {n : nat} (a a' : A) (as : vect A (Suc n)) (mem : a ∈ as) -> not (a == a') -> a' ∈ as -> a' ∈ remove a as mem
removeRetainsOthers {A} {n}     a .a (.a :: as)  (FZ , Refl)   neq (FZ , Refl)    with neq Refl
removeRetainsOthers {A} {n}     a .a (.a :: as)  (FZ , Refl)   neq (FZ , Refl)    | ()
removeRetainsOthers {A} {n}     a a' (.a :: as)  (FZ , Refl)   neq (FS i' , mem') = i' , mem'
removeRetainsOthers {A} {Zero}  a a' (a2 :: as)  (FS () , mem) neq (i' , mem')
removeRetainsOthers {A} {Suc n} a a' (.a' :: as) (FS i , mem)  neq (FZ , Refl)    = FZ , Refl
removeRetainsOthers {A} {Suc n} a a' (a2 :: as)  (FS i , mem)  neq (FS i' , mem') = inCons (removeRetainsOthers a a' as (i , mem) neq (i' , mem'))

removeRetainsOthers' : {A : Set} {n : nat} (a a' : A) (as : vect A (Suc n)) (mem : a ∈ as) -> not (a == a') -> not (a' ∈ remove a as mem) -> not (a' ∈ as)
removeRetainsOthers' {A} {n}     a .a (.a :: as)  (FZ , Refl)   neq nmem (FZ , Refl)    = neq Refl
removeRetainsOthers' {A} {n}     a a' (.a :: as)  (FZ , Refl)   neq nmem (FS i' , mem') = nmem (i' , mem')
removeRetainsOthers' {A} {Zero}  a a' (a2 :: as)  (FS () , mem) neq nmem (i' , mem')
removeRetainsOthers' {A} {Suc n} a a' (.a' :: as) (FS i , mem)  neq nmem (FZ , Refl)    = nmem (FZ , Refl)
removeRetainsOthers' {A} {Suc n} a a' (a2 :: as)  (FS i , mem)  neq nmem (FS i' , mem') = removeRetainsOthers' a a' as (i , mem) neq (λ x -> nmem (inCons x)) (i' , mem')

removeDoesNotAdd : {A : Set} {n : nat} (a a' : A) (as : vect A (Suc n)) (mem : a ∈ as) -> a' ∈ remove a as mem -> a' ∈ as
removeDoesNotAdd a a' (.a :: as)  (FZ , Refl)  mem'           = inCons mem'
removeDoesNotAdd a a' (.a' :: as) (FS i , mem) (FZ , Refl)    = FZ , Refl
removeDoesNotAdd a a' (a2 :: as)  (FS i , mem) (FS i' , mem') = inCons (removeDoesNotAdd a a' as (i , mem) (i' , mem'))

removeDoesNotAdd' : {A : Set} {n : nat} (a a' : A) (as : vect A (Suc n)) (mem : a ∈ as) -> not (a' ∈ as) -> not (a' ∈ remove a as mem)
removeDoesNotAdd' a a' (.a :: as)  (FZ , Refl)  nmem mem'           = nmem (inCons mem')
removeDoesNotAdd' a a' (.a' :: as) (FS i , mem) nmem (FZ , Refl)    = nmem (FZ , Refl)
removeDoesNotAdd' a a' (a2 :: as)  (FS i , mem) nmem (FS i' , mem') = removeDoesNotAdd' a a' as (i , mem) (λ mem2 -> nmem (inCons mem2)) (i' , mem')

removeSet : {A : Set} {n : nat} (a : A) (as : vect A (Suc n)) (mem : a ∈ as) -> isSet as -> isSet (remove a as mem)
removeSet {A} {n}     a (.a :: as) (FZ , Refl)   (Insert .a is nmem)  = is
removeSet {A} {Zero}  a (a' :: as) (FS () , mem) (Insert .a' is nmem)
removeSet {A} {Suc n} a (a' :: as) (FS i , mem)  (Insert .a' is nmem) = Insert a' (removeSet a as (i , mem) is) (removeDoesNotAdd' a a' as (i , mem) nmem)

removeRemoves : {A : Set} {n : nat} (a : A) (as : vect A (Suc n)) (mem : a ∈ as) -> isSet as -> not (a ∈ remove a as mem)
removeRemoves {A} {n}     a (.a :: as) (FZ , Refl)   (Insert .a is nmem)  mem'           = nmem mem'
removeRemoves {A} {Zero}  a (a' :: as) (FS () , mem) (Insert .a' is nmem) (i' , mem')
removeRemoves {A} {Suc n} a (.a :: as) (FS i , mem)  (Insert .a is nmem)  (FZ , Refl)    = nmem (i , mem)
removeRemoves {A} {Suc n} a (a' :: as) (FS i , mem)  (Insert .a' is nmem) (FS i' , mem') = removeRemoves a as (i , mem) is (i' , mem')


