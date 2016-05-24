module RawEvaluation where

open import Basics
open import Fin
open import RawTerm

_rawlookup_ : {n : nat} {b : bool} -> rawrec n b -> (p : nat) -> bool * rawlam n
Unit         rawlookup x = {!!}
Field e r pf rawlookup Zero    = _ , e
Field e r pf rawlookup (Suc p) = r rawlookup p

data raweval {n : nat} : {b : bool} -> rawlam n False -> rawlam n b -> Set
data rawevalPat {n : nat} : {b1 b2 : bool} (l : nat) -> rawlam n b1 -> rawpat n -> rawlam n b2 -> Set
data raweval {n} where
  EvalApp1 : {b1 b2 : bool} {e1 : rawlam n False} {e1' : rawlam n b1} {e2 : rawlam n b2} -> raweval e1 e1' -> raweval (App e1 e2) (App e1' e2)
  EvalApp2 : {b1 b2 : bool} {e1 : rawlam (Suc n) b1} {e2 : rawlam n False} {e2' : rawlam n b2} -> raweval e2 e2' -> raweval (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {b1 b2 : bool} {e1 : rawlam (Suc n) b1} {e2 : rawlam n True} {e3 : rawlam n b2} -> (b2 , e3) == rawsubst FZ e1 e2 -> raweval (App (Abs e1) e2) e3
  EvalLet1 : {b1 b2 : bool} {e1 : rawlam n False} {e1' : rawlam n b1} {e2 : rawlam (Suc n) b2} -> raweval e1 e1' -> raweval (Let e1 e2) (Let e1' e2)
  EvalLet2 : {b1 b2 : bool} {e1 : rawlam n True} {e2 : rawlam (Suc n) b1} {e3 : rawlam n b2} -> (b2 , e3) == rawsubst FZ e2 e1 -> raweval (Let e1 e2) e3
  EvalProj1 : {b : bool} {e : rawlam n False} {e' : rawlam n b} {p : nat} -> raweval e e' -> raweval (Proj e p) (Proj e' p)
  EvalProj2 : {b1 b2 : bool} {r : rawrec n b1} {p : nat} {e : rawlam n b2} -> (r rawlookup p) == (b2 , e) -> raweval (Proj (Tuple r) p) e
  EvalCase1 : {b : bool} {e : rawlam n False} {e' : rawlam n b} {ps : rawpat n} -> raweval e e' -> raweval (Case e ps) (Case e' ps)
  EvalCase2 : {l : nat} {b1 b2 : bool} {e : rawlam n b1} {e' : rawlam n b2} {ps : rawpat n} -> rawevalPat l e ps e' -> raweval (Case (Variant l e) ps) e'
  EvalUnfold1 : {b : bool} {e : rawlam n False} {e' : rawlam n b} -> raweval e e' -> raweval (Unfold e) (Unfold e')
  EvalUnfold2 : {b : bool} {e : rawlam n b} -> raweval (Unfold (Fold e)) e
data rawevalPat {n} where
  EvalPat1 :  {b1 b2 b3 : bool} {e1 : rawlam n b1} {e2 : rawlam (Suc n) b2} {e3 : rawlam n b3} {ps : rawpat n} -> 
    (b3 , e3) == rawsubst FZ e2 e1 -> rawevalPat Zero e1 (Match e2 ps) e3
  EvalPat2 : {l : nat} {b1 b2 b3 : bool} {e1 : rawlam n b1} {e2 : rawlam (Suc n) b2} {ps : rawpat n} {e' : rawlam n b3} -> 
    rawevalPat l e1 ps e' -> rawevalPat (Suc l) e1 (Match e2 ps) e'

{-

evaluate : {t : type Zero} (e : lam [] t False) -> bool * (λ b -> lam [] t b * eval {pf = Refl} {Refl} e)
evaluatePat : {t : type Zero} {pn : nat} {ts : vect (type Zero) pn} {b : bool} (l : fin pn) (e : lam [] (ts ! l) b) (ps : pat t [] ts) -> 
  bool * (λ b -> lam [] t b * evalPat l e ps)
evaluate (Var () pf)
evaluate (App {b1 = True} {True} (Abs e1) e2)        with inspect (subst FZ e1 e2)
evaluate (App {b1 = True} {True} (Abs e1) e2)        | It (_ , e3) eq = _ , (e3 , EvalApp3 (sym eq))
evaluate (App {b1 = True} {False} (Abs e1) e2)       with evaluate e2
evaluate (App {b1 = True} {False} (Abs e1) e2)       | _ , (e2' , ev) = False , (App (Abs e1) e2' , EvalApp2 ev)
evaluate (App {b1 = False} e1 e2)                    with evaluate e1 
evaluate (App {b1 = False} e1 e2)                    | _ , (e1' , ev) = False , (App e1' e2 , EvalApp1 ev)
evaluate (Let {b1 = True} e1 e2)                     with inspect (subst FZ e2 e1)
evaluate (Let {b1 = True} e1 e2)                     | It (_ , e3) eq = _ , (e3 , EvalLet2 (sym eq))
evaluate (Let {b1 = False} e1 e2)                    with evaluate e1
evaluate (Let {b1 = False} e1 e2)                    | _ , (e1' , ev) = _ , (Let e1' e2 , EvalLet1 ev)
evaluate (Proj {b = True} (Tuple r) p)               with inspect (r lookup p) 
evaluate (Proj {b = True} (Tuple r) p)               | It (b , e') eq = b , (e' , EvalProj2 eq)
evaluate (Proj {b = False} e p)                      with evaluate e
evaluate (Proj {b = False} e p)                      | _ , (e' , ev) = False , (Proj e' p , EvalProj1 ev)
evaluate (Case {b = True} (Variant l e) ps)          with evaluatePat l e ps 
evaluate (Case {b = True} (Variant l e) ps)          | _ , (e' , ev) = _ , (e' , EvalCase2 ev)
evaluate (Case {b = False} e ps)                     with evaluate e
evaluate (Case {b = False} e ps)                     | _ , (e' , ev) = False , (Case e' ps , EvalCase1 ev)
evaluate (Unfold t {b = True} (Fold .t e Refl) Refl) = _ , (e , EvalUnfold2)
evaluate (Unfold t {b = False} e Refl)               with evaluate e
evaluate (Unfold t {b = False} e Refl)               | _ , (e' , ev) = False , (Unfold t e' Refl , EvalUnfold1 ev)
evaluatePat ()     e1 Fail
evaluatePat FZ     e1 (Match e2 p) with inspect (subst FZ e2 e1) 
evaluatePat FZ     e1 (Match e2 p) | It (b , e') eq = b , (e' , EvalPat1 (sym eq))
evaluatePat (FS l) e1 (Match e2 p) with evaluatePat l e1 p
evaluatePat (FS l) e1 (Match e2 p) | b , (e' , ev) = b , (e' , EvalPat2 ev)

-}
