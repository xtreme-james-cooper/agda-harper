module Heap where

open import Basics
open import Fin
open import Vect
open import Option

addr : Set
addr = nat

null : addr
null = Zero

isNull : (a : addr) -> decide (a == null)
isNull Zero    = Yes Refl
isNull (Suc a) = No (λ ())

data heap (A : Set) : nat -> Set where
  Heap : (n : nat) (ls : vect nat n) (map : addr -> option A) -> 
    (asd : (l : addr) -> l ∈ ls -> A * (λ a -> map l == Some a)) -> 
    (nasnd : (l : nat) -> not (l ∈ ls) -> map l == None) -> 
    heap A n
 
initial : {A : Set} -> heap A Zero
initial = Heap Zero [] (λ x -> None) (λ { l (() , mem) }) (λ m _ -> Refl) 

size : {A : Set} {n : nat} -> heap A n -> nat
size (Heap n _ _ _ _) = n

addresses : {A : Set} {n : nat} -> heap A n -> vect nat n
addresses (Heap _ ls _ _ _) = ls

lookup : {A : Set} {n : nat} (h : heap A n) (l : addr) -> l ∈ addresses h -> A
lookup (Heap n ls map asd nasnd) l mem with asd l mem
lookup (Heap n ls map asd nasnd) l mem | a , pf = a

nextAddr : {n : nat} -> vect addr n -> addr
nextAddr {n}     ls with in? natEq (Suc n) ls
nextAddr {Zero}  ls | Yes (() , mem)
nextAddr {Suc n} ls | Yes mem = nextAddr (Vect.remove (Suc (Suc n)) ls mem)
nextAddr {n}     ls | No nmem = Suc n

alloc : {A : Set} {n : nat} -> heap A n -> A -> (heap A (Suc n) × addr)
alloc {A} (Heap n ls map asd nasnd) a = Heap (Suc n) (l :: ls) (extend natEq l a map) updateAsd updateNasnd , l
  where 
    l = nextAddr ls

    updateAsd : (l' : addr) -> l' ∈ (l :: ls) -> A * (λ a' -> extend natEq l a map l' == Some a')
    updateAsd l' mem          with natEq l l'
    updateAsd .l mem          | Yes Refl = a , Refl
    updateAsd l' (FZ , mem)   | No neq with neq mem
    updateAsd l' (FZ , mem)   | No neq | ()
    updateAsd l' (FS i , mem) | No neq = asd l' (i , mem) 

    updateNasnd : (l' : nat) -> not (l' ∈ (l :: ls)) -> extend natEq l a map l' == None
    updateNasnd l' nmem with natEq l l'
    updateNasnd .l nmem | Yes Refl with nmem (FZ , Refl)
    updateNasnd .l nmem | Yes Refl | ()
    updateNasnd l' nmem | No neq   = nasnd l' (λ { (i , mem) -> nmem (FS i , mem) })

update : {A : Set} {n : nat} (h : heap A n) (l : addr) -> A -> l ∈ addresses h -> heap A n
update {A} (Heap n ls map asd nasnd) l a mem = Heap n ls (extend natEq l a map) updateAsd updateNasnd
  where 
    updateAsd : (l' : addr) -> l' ∈ ls -> A * (λ a' -> extend natEq l a map l' == Some a')
    updateAsd l' mem' with natEq l l'
    updateAsd .l mem' | Yes Refl = a , Refl
    updateAsd l' mem' | No neq   = asd l' mem'
    
    updateNasnd : (l' : nat) -> not (l' ∈ ls) -> extend natEq l a map l' == None
    updateNasnd l' nmem with natEq l l'
    updateNasnd .l nmem | Yes Refl with nmem mem 
    updateNasnd .l nmem | Yes Refl | ()
    updateNasnd l' nmem | No neq   = nasnd l' nmem

free : {A : Set} {n : nat} (h : heap A (Suc n)) (l : addr) -> l ∈ addresses h -> heap A n
free {A} {n} (Heap .(Suc n) ls map asd nasnd) l mem = Heap n (Vect.remove l ls mem) (Option.remove natEq l map) updateAsd updateNasnd
  where
    updateAsd : (l' : addr) -> l' ∈ Vect.remove l ls mem -> A * (λ a → Option.remove natEq l map l' == Some a)
    updateAsd l' mem with natEq l l'
    updateAsd .l mem | Yes Refl = {!!}
    updateAsd l' mem | No neq   = {!!}

    updateNasnd : (l' : nat) -> not (l' ∈ Vect.remove l ls mem) -> Option.remove natEq l map l' == None
    updateNasnd l' nmem with natEq l l'
    updateNasnd .l nmem | Yes Refl = {!!}
    updateNasnd l' nmem | No neq   = {!!}
