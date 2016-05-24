module RawTerm where

open import Basics
open import Fin

data rawlam (n : nat) : Set
data rawrec (n : nat) : Set
data rawpat (n : nat) : Set
data rawlam n where
  Var : fin n -> rawlam n
  App : rawlam n -> rawlam n -> rawlam n
  Abs : rawlam (Suc n) -> rawlam n
  Let : rawlam n -> rawlam (Suc n) -> rawlam n
  Tuple : rawrec n -> rawlam n
  Proj : rawlam n -> nat -> rawlam n
  Variant : nat -> rawlam n -> rawlam n
  Case : rawlam n -> rawpat n -> rawlam n
  Fold : rawlam n -> rawlam n
  Unfold : rawlam n -> rawlam n
data rawrec n where
  Unit : rawrec n
  Field : rawlam n -> rawrec n -> rawrec n
data rawpat n where
  Fail : rawpat n
  Match : rawlam (Suc n) -> rawpat n -> rawpat n

rawincr : {n : nat} (x : fin (Suc n)) -> rawlam n -> rawlam (Suc n)
rawincrRec : {n : nat} (x : fin (Suc n)) -> rawrec n -> rawrec (Suc n)
rawincrPat : {n : nat} (x : fin (Suc n)) -> rawpat n -> rawpat (Suc n)
rawincr x (Var y)       = Var (fincr x y)
rawincr x (App e1 e2)   = App (rawincr x e1) (rawincr x e2)
rawincr x (Abs e)       = Abs (rawincr (FS x) e)
rawincr x (Let e1 e2)   = Let (rawincr x e1) (rawincr (FS x) e2)
rawincr x (Tuple rec)   = Tuple (rawincrRec x rec)
rawincr x (Proj e p)    = Proj (rawincr x e) p
rawincr x (Variant l e) = Variant l (rawincr x e)
rawincr x (Case e ps)   = Case (rawincr x e) (rawincrPat x ps)
rawincr x (Fold e)      = Fold (rawincr x e)
rawincr x (Unfold e)    = Unfold (rawincr x e)
rawincrRec x Unit        = Unit
rawincrRec x (Field e r) = Field (rawincr x e) (rawincrRec x r)
rawincrPat x Fail         = Fail
rawincrPat x (Match e ps) = Match (rawincr (FS x) e) (rawincrPat x ps)

rawsubst : {n : nat} (x : fin (Suc n)) -> rawlam (Suc n) -> rawlam n -> rawlam n
rawsubstRec : {n : nat} (x : fin (Suc n)) -> rawrec (Suc n) -> rawlam n -> rawrec n
rawsubstPat : {n : nat} (x : fin (Suc n)) -> rawpat (Suc n) -> rawlam n -> rawpat n
rawsubst x (Var y)       v with finEq y x
rawsubst x (Var .x)      v | Yes Refl = v
rawsubst x (Var y)       v | No npf   = Var (fdecr x y npf)
rawsubst x (App e1 e2)   v = App (rawsubst x e1 v) (rawsubst x e2 v)
rawsubst x (Abs e)       v = Abs (rawsubst (fincr FZ x) e (rawincr FZ v))
rawsubst x (Let e1 e2)   v = Let (rawsubst x e1 v) (rawsubst (fincr FZ x) e2 (rawincr FZ v))
rawsubst x (Tuple rec)   v = Tuple (rawsubstRec x rec v)
rawsubst x (Proj e p)    v = Proj (rawsubst x e v) p
rawsubst x (Variant l e) v = Variant l (rawsubst x e v)
rawsubst x (Case e ps)   v = Case (rawsubst x e v) (rawsubstPat x ps v)
rawsubst x (Fold e)      v = Fold (rawsubst x e v)
rawsubst x (Unfold e)    v = Unfold (rawsubst x e v)
rawsubstRec x Unit        v = Unit
rawsubstRec x (Field e r) v = Field (rawsubst x e v) (rawsubstRec x r v)
rawsubstPat x Fail         v = Fail
rawsubstPat x (Match e ps) v = Match (rawsubst (fincr FZ x) e (rawincr FZ v)) (rawsubstPat x ps v)

-- abbreviations

rawunitE : {n : nat} -> rawlam n
rawunitE = Tuple Unit

rawabortE : {n : nat} -> rawlam n -> rawlam n
rawabortE e = Case e Fail

rawzeroE : {n : nat} -> rawlam n
rawzeroE = Fold (Variant Zero rawunitE)

rawsuccE : {n : nat} -> rawlam n -> rawlam n
rawsuccE e = Fold (Variant (Suc Zero) e)

rawnatcaseE : {n : nat} -> rawlam n -> rawlam n -> rawlam (Suc n) -> rawlam n
rawnatcaseE e e0 es = Case (Unfold e) (Match (rawincr FZ e0) (Match es Fail))

rawnilE : {n : nat} -> rawlam n
rawnilE = Fold (Variant Zero rawunitE)

rawconsE : {n : nat} -> rawlam n -> rawlam n -> rawlam n
rawconsE a as = Fold (Variant (Suc Zero) (Tuple (Field a (Field as Unit))))

rawlistcaseE : {n : nat} -> rawlam n -> rawlam n -> rawlam (Suc (Suc n)) -> rawlam n
rawlistcaseE e en ec = Case (Unfold e) (Match (rawincr FZ en) (Match (App (App (rawincr FZ (Abs (Abs ec))) (Proj (Var FZ) Zero)) (Proj (Var FZ) (Suc Zero))) Fail))
