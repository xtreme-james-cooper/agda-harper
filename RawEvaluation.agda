module RawEvaluation where

open import Basics
open import Nat
open import Fin
open import Option
open import RawTerm

_rawlookup_ : {n : nat} {b : bool} -> rawrec n b -> (p : nat) -> option (bool * rawlam n)
Unit         rawlookup x       = None
Field e r pf rawlookup Zero    = Some (_ , e)
Field e r pf rawlookup (Suc p) = r rawlookup p

infix 60 _rawlookup_

data raweval {n : nat} : {b : bool} -> rawlam n False -> rawlam n b -> Set
data rawevalPat {n : nat} : {b1 b2 : bool} (l : nat) -> rawlam n b1 -> rawpat n -> rawlam n b2 -> Set
data raweval {n} where
  EvalApp1 : {b1 b2 : bool} {e1 : rawlam n False} {e1' : rawlam n b1} {e2 : rawlam n b2} -> raweval e1 e1' -> raweval (App e1 e2) (App e1' e2)
  EvalApp2 : {b1 b2 : bool} {e1 : rawlam (Suc n) b1} {e2 : rawlam n False} {e2' : rawlam n b2} -> raweval e2 e2' -> raweval (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {b1 b2 : bool} {e1 : rawlam (Suc n) b1} {e2 : rawlam n True} {e3 : rawlam n b2} -> rawsubst FZ e1 e2 == (b2 , e3) -> raweval (App (Abs e1) e2) e3
  EvalLet1 : {b1 b2 : bool} {e1 : rawlam n False} {e1' : rawlam n b1} {e2 : rawlam (Suc n) b2} -> raweval e1 e1' -> raweval (Let e1 e2) (Let e1' e2)
  EvalLet2 : {b1 b2 : bool} {e1 : rawlam n True} {e2 : rawlam (Suc n) b1} {e3 : rawlam n b2} -> rawsubst FZ e2 e1 == (b2 , e3) -> raweval (Let e1 e2) e3
  EvalProj1 : {b : bool} {e : rawlam n False} {e' : rawlam n b} {p : nat} -> raweval e e' -> raweval (Proj e p) (Proj e' p)
  EvalProj2 : {b1 b2 : bool} {r : rawrec n b1} {p : nat} {e : rawlam n b2} -> (r rawlookup p) == Some (b2 , e) -> raweval (Proj (Tuple r) p) e
  EvalCase1 : {b : bool} {e : rawlam n False} {e' : rawlam n b} {ps : rawpat n} -> raweval e e' -> raweval (Case e ps) (Case e' ps)
  EvalCase2 : {l : nat} {b1 b2 : bool} {e : rawlam n b1} {e' : rawlam n b2} {ps : rawpat n} -> rawevalPat l e ps e' -> raweval (Case (Variant l e) ps) e'
--  EvalUnfold1 : {b : bool} {e : rawlam n False} {e' : rawlam n b} -> raweval e e' -> raweval (Unfold e) (Unfold e')
--  EvalUnfold2 : {b : bool} {e : rawlam n b} -> raweval (Unfold (Fold e)) e
data rawevalPat {n} where
  EvalPat1 :  {b1 b2 b3 : bool} {e1 : rawlam n b1} {e2 : rawlam (Suc n) b2} {e3 : rawlam n b3} {ps : rawpat n} -> 
    rawsubst FZ e2 e1 == (b3 , e3) -> rawevalPat Zero e1 (Match e2 ps) e3
  EvalPat2 : {l : nat} {b1 b2 b3 : bool} {e1 : rawlam n b1} {e2 : rawlam (Suc n) b2} {ps : rawpat n} {e' : rawlam n b3} -> 
    rawevalPat l e1 ps e' -> rawevalPat (Suc l) e1 (Match e2 ps) e'

