module RecursiveTypes.Type where

open import Basics
open import Fin
open import Vect

data type (tn : nat) : Set where
  TyVar : fin tn -> type tn
  _=>_ : type tn -> type tn -> type tn
  Tuple : {n : nat} -> vect (type tn) n -> type tn
  Variant : {n : nat} -> vect (type tn) n -> type tn
  Rec : type (Suc tn) -> type tn

unitT : {tn : nat} -> type tn
unitT = Tuple []

voidT : {tn : nat} -> type tn
voidT = Variant []

tincr : {tn : nat} -> fin (Suc tn) -> type tn -> type (Suc tn)
tincrVect : {n tn : nat} -> fin (Suc tn) -> vect (type tn) n -> vect (type (Suc tn)) n
tincr x (TyVar y)    = TyVar (fincr x y)
tincr x (t1 => t2)   = tincr x t1 => tincr x t2
tincr x (Tuple ts)   = Tuple (tincrVect x ts)
tincr x (Variant ts) = Variant (tincrVect x ts)
tincr x (Rec t)      = Rec (tincr (FS x) t)
tincrVect x []        = []
tincrVect x (t :: ts) = tincr x t :: tincrVect x ts

tsubst : {tn : nat} -> fin (Suc tn) -> type tn -> type (Suc tn) -> type tn
tsubstVect : {n tn : nat} -> fin (Suc tn) -> type tn -> vect (type (Suc tn)) n -> vect (type tn) n
tsubst tv v (TyVar tv')  with finEq tv' tv
tsubst tv v (TyVar tv')  | Yes pf = v
tsubst tv v (TyVar tv')  | No npf = TyVar (fdecr tv tv' npf)
tsubst tv v (t1 => t2)   = tsubst tv v t1 => tsubst tv v t2
tsubst tv v (Tuple ts)   = Tuple (tsubstVect tv v ts)
tsubst tv v (Variant ts) = Variant (tsubstVect tv v ts)
tsubst tv v (Rec t)      = Rec (tsubst (FS tv) (tincr FZ v) t)
tsubstVect tv v []        = []
tsubstVect tv v (t :: ts) = tsubst tv v t :: tsubstVect tv v ts

