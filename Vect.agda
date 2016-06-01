module Vect where

open import Basics
open import Fin

data vect (A : Set) : nat -> Set where
  [] : vect A Zero
  _::_ : {n : nat} -> A -> vect A n -> vect A (Suc n)

infixr 70 _::_

_!_ : {A : Set} {n : nat} -> vect A n -> fin n -> A
[]     ! ()
x :: v ! FZ   = x
x :: v ! FS f = v ! f

infixl 60 _!_

insertAt : {A : Set} {n : nat} -> fin (Suc n) -> vect A n -> A -> vect A (Suc n)
insertAt FZ      vect        a = a :: vect
insertAt (FS ()) []          a
insertAt (FS f)  (b :: vect) a = b :: (insertAt f vect a)

map : {A B : Set} {n : nat} -> (A -> B) -> vect A n -> vect B n
map f []        = []
map f (a :: as) = f a :: map f as

-- Lemmas

lookupInsertAt : {A : Set} {n : nat} (vs : vect A n) (x : fin (Suc n)) (v : A) -> insertAt x vs v ! x == v
lookupInsertAt vs        FZ      v = Refl
lookupInsertAt []        (FS ()) v
lookupInsertAt (x :: vs) (FS y)  v = lookupInsertAt vs y v

insertAtFincr : {A : Set} {n : nat} (gam : vect A n) (x : fin n) (y : fin (Suc n)) (a : A) -> insertAt y gam a ! fincr y x == gam ! x
insertAtFincr (b :: gam) FZ     FZ     a = Refl
insertAtFincr (b :: gam) FZ     (FS y) a = Refl
insertAtFincr (b :: gam) (FS x) FZ     a = Refl
insertAtFincr (b :: gam) (FS x) (FS y) a = insertAtFincr gam x y a

lookupInsertAtNeq : {A : Set} {n : nat} (vs : vect A n) (x y : fin (Suc n)) (a : A) (npf : not (y == x)) -> insertAt x vs a ! y == vs ! fdecr x y npf
lookupInsertAtNeq vs        FZ      FZ      a npf with npf Refl
lookupInsertAtNeq vs        FZ      FZ      a npf | ()
lookupInsertAtNeq []        FZ      (FS ()) a npf
lookupInsertAtNeq []        (FS ()) y       a npf
lookupInsertAtNeq (v :: vs) FZ      (FS y)  a npf = Refl
lookupInsertAtNeq (v :: vs) (FS x)  FZ      a npf = Refl
lookupInsertAtNeq (v :: vs) (FS x)  (FS y)  a npf = lookupInsertAtNeq vs x y a (neqFS npf)

mapLookup : {A B : Set} {n : nat} (f : A -> B) (as : vect A n) (x : fin n) -> map f as ! x == f (as ! x)
mapLookup f (a :: as) FZ     = Refl
mapLookup f (a :: as) (FS x) = mapLookup f as x

mapInsertAt : {A B : Set} {n : nat} (as : vect A n) (a : A) (f : A -> B) (x : fin (Suc n)) -> map f (insertAt x as a) == insertAt x (map f as) (f a)
mapInsertAt []        b f FZ      = Refl
mapInsertAt []        b f (FS ())
mapInsertAt (a :: as) b f FZ      = Refl
mapInsertAt (a :: as) b f (FS x)  rewrite mapInsertAt as b f x = Refl
