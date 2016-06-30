module Agda.RawTerm where

open import AgdaUtils.Basics
open import AgdaUtils.Nat
open import AgdaUtils.Bool
open import AgdaUtils.Fin
open import AgdaUtils.Prod

data rawlam (n : nat) : bool -> Set
data rawrec (n : nat) : bool -> Set
data rawpat (n : nat) : Set
data rawlam n where
  Var : fin n -> rawlam n False
  App : {b1 b2 : bool} -> rawlam n b1 -> rawlam n b2 -> rawlam n False
  Abs : {b : bool} -> rawlam (Suc n) b -> rawlam n True
  Let : {b1 b2 : bool} -> rawlam n b1 -> rawlam (Suc n) b2 -> rawlam n False
  Tuple : {b : bool} -> rawrec n b -> rawlam n True
  Proj : {b : bool} -> rawlam n b -> nat -> rawlam n False
  Variant : {b : bool} -> nat -> rawlam n b -> rawlam n True
  Case : {b : bool} -> rawlam n b -> rawpat n -> rawlam n False
--  Fold : {b : bool} -> rawlam n b -> rawlam n True
--  Unfold : {b : bool} -> rawlam n b -> rawlam n False
data rawrec n where
  Unit : rawrec n True
  Field : {b1 b2 b3 : bool} -> rawlam n b1 -> rawrec n b2 -> b1 and b2 == b3 -> rawrec n b3
data rawpat n where
  Fail : rawpat n
  Match : {b : bool} -> rawlam (Suc n) b -> rawpat n -> rawpat n

rawincr : {n : nat} {b : bool} (x : fin (Suc n)) -> rawlam n b -> rawlam (Suc n) b
rawincrRec : {n : nat} {b : bool} (x : fin (Suc n)) -> rawrec n b -> rawrec (Suc n) b
rawincrPat : {n : nat} (x : fin (Suc n)) -> rawpat n -> rawpat (Suc n)
rawincr x (Var y)       = Var (fincr x y)
rawincr x (App e1 e2)   = App (rawincr x e1) (rawincr x e2)
rawincr x (Abs e)       = Abs (rawincr (FS x) e)
rawincr x (Let e1 e2)   = Let (rawincr x e1) (rawincr (FS x) e2)
rawincr x (Tuple rec)   = Tuple (rawincrRec x rec)
rawincr x (Proj e p)    = Proj (rawincr x e) p
rawincr x (Variant l e) = Variant l (rawincr x e)
rawincr x (Case e ps)   = Case (rawincr x e) (rawincrPat x ps)
--rawincr x (Fold e)      = Fold (rawincr x e)
--rawincr x (Unfold e)    = Unfold (rawincr x e)
rawincrRec x Unit           = Unit
rawincrRec x (Field e r pf) = Field (rawincr x e) (rawincrRec x r) pf
rawincrPat x Fail         = Fail
rawincrPat x (Match e ps) = Match (rawincr (FS x) e) (rawincrPat x ps)

rawsubst : {n : nat} {b1 b2 : bool} (x : fin (Suc n)) -> rawlam (Suc n) b1 -> rawlam n b2 -> bool * rawlam n
rawsubstRec : {n : nat} {b1 b2 : bool} (x : fin (Suc n)) -> rawrec (Suc n) b1 -> rawlam n b2 -> bool * rawrec n
rawsubstPat : {n : nat} {b : bool} (x : fin (Suc n)) -> rawpat (Suc n) -> rawlam n b -> rawpat n
rawsubst x (Var y)       v with finEq y x
rawsubst x (Var .x)      v | Yes Refl = _ , v
rawsubst x (Var y)       v | No npf   = _ , Var (fdecr x y npf)
rawsubst x (App e1 e2)   v with rawsubst x e1 v | rawsubst x e2 v
rawsubst x (App e1 e2)   v | _ , e1' | _ , e2' = _ , App e1' e2'
rawsubst x (Abs e)       v with rawsubst (fincr FZ x) e (rawincr FZ v) 
rawsubst x (Abs e)       v | _ , e' = _ , Abs e'
rawsubst x (Let e1 e2)   v with rawsubst x e1 v | rawsubst (fincr FZ x) e2 (rawincr FZ v) 
rawsubst x (Let e1 e2)   v | _ , e1' | _ , e2' = _ , Let e1' e2'
rawsubst x (Tuple rec)   v with rawsubstRec x rec v 
rawsubst x (Tuple rec)   v | _ , rec' = _ , Tuple rec'
rawsubst x (Proj e p)    v with rawsubst x e v 
rawsubst x (Proj e p)    v | _ , e' = _ , Proj e' p
rawsubst x (Variant l e) v with rawsubst x e v 
rawsubst x (Variant l e) v | _ , e' = _ , Variant l e'
rawsubst x (Case e ps)   v with rawsubst x e v 
rawsubst x (Case e ps)   v | _ , e' = _ , Case e' (rawsubstPat x ps v)
--rawsubst x (Fold e)      v with rawsubst x e v 
--rawsubst x (Fold e)      v | _ , e' = _ , Fold e'
--rawsubst x (Unfold e)    v with rawsubst x e v 
--rawsubst x (Unfold e)    v | _ , e' = _ , Unfold e'
rawsubstRec x Unit           v = _ , Unit
rawsubstRec x (Field e r pf) v with rawsubst x e v | rawsubstRec x r v
rawsubstRec x (Field e r pf) v | b1 , e' | b2 , rec' = (b1 and b2) , Field e' rec' Refl
rawsubstPat x Fail         v = Fail
rawsubstPat x (Match e ps) v with rawsubst (fincr FZ x) e (rawincr FZ v) 
rawsubstPat x (Match e ps) v | _ , e' = Match e' (rawsubstPat x ps v)

-- abbreviations

rawunitE : {n : nat} -> rawlam n True
rawunitE = Tuple Unit

rawabortE : {n : nat} {b : bool} -> rawlam n b -> rawlam n False
rawabortE e = Case e Fail

--rawzeroE : {n : nat} -> rawlam n True
--rawzeroE = Fold (Variant Zero rawunitE)

--rawsuccE : {n : nat} {b : bool} -> rawlam n b -> rawlam n True
--rawsuccE e = Fold (Variant (Suc Zero) e)

--rawnatcaseE : {n : nat} {b1 b2 b3 : bool} -> rawlam n b1 -> rawlam n b2 -> rawlam (Suc n) b3 -> rawlam n False
--rawnatcaseE e e0 es = Case (Unfold e) (Match (rawincr FZ e0) (Match es Fail))

--rawnilE : {n : nat} -> rawlam n True
--rawnilE = Fold (Variant Zero rawunitE)

--rawconsE : {n : nat} {b1 b2 : bool} -> rawlam n b1 -> rawlam n b2 -> rawlam n True
--rawconsE a as = Fold (Variant (Suc Zero) (Tuple (Field a (Field as Unit Refl) Refl)))

--rawlistcaseE : {n : nat} {b1 b2 b3 : bool} -> rawlam n b1 -> rawlam n b2 -> rawlam (Suc (Suc n)) b3 -> rawlam n False
--rawlistcaseE e en ec = Case (Unfold e) (Match (rawincr FZ en) (Match (App (App (rawincr FZ (Abs (Abs ec))) (Proj (Var FZ) Zero)) (Proj (Var FZ) (Suc Zero))) Fail))

