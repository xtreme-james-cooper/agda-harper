module Vect where

open import Basics
open import Fin

data vect (A : Set) : nat -> Set where
  [] : vect A Zero
  _::_ : {n : nat} -> A -> vect A n -> vect A (Suc n)

_!_ : {A : Set} {n : nat} -> vect A n -> fin n -> A
[]       ! ()
(x :: v) ! FZ     = x
(x :: v) ! (FS f) = v ! f

insertAt : {A : Set} {n : nat} -> fin (Suc n) -> vect A n -> A -> vect A (Suc n)
insertAt FZ      vect        a = a :: vect
insertAt (FS ()) []          a
insertAt (FS f)  (b :: vect) a = b :: (insertAt f vect a)

map : {A B : Set} {n : nat} -> (A -> B) -> vect A n -> vect B n
map f []        = []
map f (a :: as) = f a :: map f as

_∈_ : {A : Set} {n : nat} (a : A) (as : vect A n) -> Set
_∈_ {A} {n} a as = fin n * (λ i -> (as ! i) == a)

in? : {A : Set} {n : nat} -> equality A -> (a : A) (as : vect A n) -> decide (a ∈ as)
in? {A} {Zero}  eq a []         = No (λ { (() , y) })
in? {A} {Suc n} eq a (a' :: as) with eq a a'
in? {A} {Suc n} eq a (.a :: as) | Yes Refl = Yes (FZ , Refl)
in? {A} {Suc n} eq a (a' :: as) | No neq   with in? eq a as
in? {A} {Suc n} eq a (a' :: as) | No neq   | Yes (i , pf) = Yes (FS i , pf)
in? {A} {Suc n} eq a (a' :: as) | No neq   | No nmem      = No (inLemma a a' as neq nmem)
  where 
    inLemma : (a a' : A) (as : vect A n) -> not (a == a') -> not (fin n * (λ i → (as ! i) == a)) -> not (fin (Suc n) * (λ i → ((a' :: as) ! i) == a))
    inLemma a .a as neq nmem (FZ , Refl)  = neq Refl
    inLemma a a' as neq nmem (FS i , mem) = nmem (i , mem)

remove : {A : Set} {n : nat} (a : A) (as : vect A (Suc n)) -> a ∈ as -> vect A n
remove {A} {n}     a (.a :: as) (FZ , Refl)  = as
remove {A} {Zero}  a (a' :: as) (FS () , mem)
remove {A} {Suc n} a (a' :: as) (FS i , mem) = a' :: remove a as (i , mem)

-- Lemmas

lookupInsertAt : {A : Set} {n : nat} (vs : vect A n) (x : fin (Suc n)) (v : A) -> (insertAt x vs v ! x) == v
lookupInsertAt vs        FZ      v = Refl
lookupInsertAt []        (FS ()) v
lookupInsertAt (x :: vs) (FS y)  v = lookupInsertAt vs y v

insertAtFincr : {A : Set} {n : nat} (gam : vect A n) (x : fin n) (y : fin (Suc n)) (a : A) -> (insertAt y gam a ! fincr y x) == (gam ! x)
insertAtFincr (b :: gam) FZ     FZ     a = Refl
insertAtFincr (b :: gam) FZ     (FS y) a = Refl
insertAtFincr (b :: gam) (FS x) FZ     a = Refl
insertAtFincr (b :: gam) (FS x) (FS y) a = insertAtFincr gam x y a

insertAtFdecr : {A : Set} {n : nat} {vs : vect A n} {x y : fin (Suc n)} {a b : A} -> (npf : not (y == x)) -> (insertAt x vs a ! y) == b -> (vs ! fdecr x y npf) == b
insertAtFdecr {A} {n}     {vs}      {FZ}    {FZ}    npf Refl with npf Refl
insertAtFdecr {A} {n}     {vs}      {FZ}    {FZ}    npf Refl | ()
insertAtFdecr {A} {Zero}  {[]}      {FZ}    {FS ()} npf Refl
insertAtFdecr {A} {Zero}  {[]}      {FS ()} {y}     npf Refl
insertAtFdecr {A} {Suc n} {v :: vs} {FZ}    {FS y}  npf Refl = Refl
insertAtFdecr {A} {Suc n} {v :: vs} {FS x}  {FZ}    npf Refl = Refl
insertAtFdecr {A} {Suc n} {v :: vs} {FS x}  {FS y}  npf Refl = insertAtFdecr (neqFS npf) Refl

mapLookup : {A B : Set} {n : nat} (f : A -> B) (as : vect A n) (x : fin n) -> (map f as ! x) == f (as ! x)
mapLookup f (a :: as) FZ     = Refl
mapLookup f (a :: as) (FS x) = mapLookup f as x

mapInsertAt : {A B : Set} {n : nat} (as : vect A n) (a : A) (f : A -> B) (x : fin (Suc n)) -> map f (insertAt x as a) == insertAt x (map f as) (f a)
mapInsertAt []        b f FZ      = Refl
mapInsertAt []        b f (FS ())
mapInsertAt (a :: as) b f FZ      = Refl
mapInsertAt (a :: as) b f (FS x)  rewrite mapInsertAt as b f x = Refl
