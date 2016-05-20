module Heap where

open import Basics
open import Fin
open import Vect
open import Sets
open import Option

addr : Set
addr = nat

null : addr
null = Zero

isNull : (a : addr) -> decide (a == null)
isNull Zero    = Yes Refl
isNull (Suc a) = No (λ ())

data heap (A : Set) : nat -> Set where
  Heap : (n : nat) (ls : vect nat n) (map : addr -> option A) -> isSet ls ->
    (asd : (l : addr) -> l ∈ ls -> A * (λ a -> map l == Some a)) -> 
    (nasnd : (l : nat) -> not (l ∈ ls) -> map l == None) -> 
    heap A n
 
initial : {A : Set} -> heap A Zero
initial = Heap Zero [] (λ x -> None) EmptySet (λ { l (() , mem) }) (λ m _ -> Refl) 

size : {A : Set} {n : nat} -> heap A n -> nat
size (Heap n _ _ _ _ _) = n

addresses : {A : Set} {n : nat} -> heap A n -> vect nat n
addresses (Heap _ ls _ _ _ _) = ls

lookup : {A : Set} {n : nat} (h : heap A n) (l : addr) -> l ∈ addresses h -> A
lookup (Heap n ls map is asd nasnd) l mem with asd l mem
lookup (Heap n ls map is asd nasnd) l mem | a , pf = a

nextAddr : {n : nat} (ls : vect addr n) -> isSet ls -> addr
nextAddr {n}     ls is with in? natEq (Suc n) ls
nextAddr {Zero}  ls is | Yes (() , mem)
nextAddr {Suc n} ls is | Yes mem = nextAddr (Sets.remove (Suc (Suc n)) ls mem) (removeSet (Suc (Suc n)) ls mem is)
nextAddr {n}     ls is | No nmem = Suc n

nextAddrNotLarge : {n : nat} (ls : vect addr n) (is : isSet ls) (m : nat) -> m > Suc n -> not (m == nextAddr ls is)
nextAddrNotLarge {n}     ls is m              gt eq   with in? natEq (Suc n) ls 
nextAddrNotLarge {Zero}  ls is m              gt eq   | Yes (() , mem)
nextAddrNotLarge {Suc n} ls is m              gt eq   | Yes mem = 
  nextAddrNotLarge (Sets.remove (Suc (Suc n)) ls mem) (removeSet (Suc (Suc n)) ls mem is) m (gtTrans gt sucGt) eq 
nextAddrNotLarge {Zero}  ls is .(Suc Zero)    gt Refl | No nmem = sucNrefl gt
nextAddrNotLarge {Suc n} ls is .(Suc (Suc n)) gt Refl | No nmem = sucNrefl gt

nextAddrNotMem : {n : nat} (ls : vect addr n) (is : isSet ls) -> not (nextAddr ls is ∈ ls)
nextAddrNotMem {n}     ls is mem with in? natEq (Suc n) ls
nextAddrNotMem {Zero}  ls is mem | Yes (() , mem')
nextAddrNotMem {Suc n} ls is mem | Yes mem' = nextAddrNotMem ls' is' (removeRetainsOthers n' (nextAddr ls' is') ls mem' (nextAddrNotLarge ls' is' n' sucGt) mem)
  where
    n' = Suc (Suc n)
    ls' = Sets.remove n' ls mem'
    is' = removeSet n' ls mem' is
nextAddrNotMem {Zero}  ls is mem | No nmem = nmem mem
nextAddrNotMem {Suc n} ls is mem | No nmem = nmem mem

nextAddrNotNull : {n : nat} (ls : vect addr n) (is : isSet ls) -> not (nextAddr ls is == null)
nextAddrNotNull {n}     ls is eq with in? natEq (Suc n) ls
nextAddrNotNull {Zero}  ls is eq | Yes (() , mem)
nextAddrNotNull {Suc n} ls is eq | Yes mem = nextAddrNotNull (Sets.remove (Suc (Suc n)) ls mem) (removeSet (Suc (Suc n)) ls mem is) eq
nextAddrNotNull {Zero}  ls is () | No nmem
nextAddrNotNull {Suc n} ls is () | No nmem

alloc : {A : Set} {n : nat} -> heap A n -> A -> (heap A (Suc n) × addr)
alloc {A} (Heap n ls map is asd nasnd) a = Heap (Suc n) (l :: ls) (extend natEq l a map) (Insert l is (nextAddrNotMem ls is)) updateAsd updateNasnd , l
  where 
    l = nextAddr ls is

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
    updateNasnd l' nmem | No neq   = nasnd l' (λ mem -> nmem (inCons mem))

update : {A : Set} {n : nat} (h : heap A n) (l : addr) -> A -> l ∈ addresses h -> heap A n
update {A} (Heap n ls map is asd nasnd) l a mem = Heap n ls (extend natEq l a map) is updateAsd updateNasnd
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
free {A} {n} (Heap .(Suc n) ls map is asd nasnd) l mem = Heap n (Sets.remove l ls mem) (Option.remove natEq l map) (removeSet l ls mem is) updateAsd updateNasnd 
  where
    updateAsd : (l' : addr) -> l' ∈ Sets.remove l ls mem -> A * (λ a → Option.remove natEq l map l' == Some a)
    updateAsd l' mem' with natEq l l'
    updateAsd .l mem' | Yes Refl with removeRemoves l ls mem is mem'
    updateAsd .l mem' | Yes Refl | ()
    updateAsd l' mem' | No neq   = asd l' (removeDoesNotAdd l l' ls mem mem')

    updateNasnd : (l' : nat) -> not (l' ∈ Sets.remove l ls mem) -> Option.remove natEq l map l' == None
    updateNasnd l' nmem with natEq l l'
    updateNasnd .l nmem | Yes Refl = Refl
    updateNasnd l' nmem | No neq   = nasnd l' (removeRetainsOthers' l l' ls mem neq nmem)

