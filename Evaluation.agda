module Evaluation where

open import Basics
open import Nat
open import Fin
open import Vect
open import Option
open import Type
open import Term
open import RawTerm
open import RawEvaluation

_lookup_ : {n tn rn : nat} {gam : vect (type tn) n} {ts : vect (type tn) rn} {b : bool} {r : rawrec n b} -> 
  rec gam r ts -> (p : fin rn) -> bool * λ b' -> rawlam n b' * λ r' -> r rawlookup naturalize p == Some (b' , r') × lam gam r' (ts ! p)
Unit         lookup ()
Field e r pf lookup FZ   = _ , _ , Refl , e
Field e r pf lookup FS p = r lookup p

infix 60 _lookup_

data eval {n tn : nat} {gam : vect (type tn) n} : {t : type tn} {r : rawlam n False} {b : bool} {r' : rawlam n b} -> lam gam r t -> lam gam r' t -> Set
data evalPat {n tn : nat} {t : type tn} {gam : vect (type tn) n} : {pn : nat} {ts : vect (type tn) pn} {b1 b2 : bool} {r1 : rawlam n b1} {rp : rawpat n} {r2 : rawlam n b2} 
  (l : fin pn) -> lam gam r1 (ts ! l) -> pat t gam rp ts -> lam gam r2 t -> Set
data eval {n} {tn} {gam} where
  EvalApp1 : {t1 t2 : type tn} {b1 b2 : bool} {r1 : rawlam n False} {r1' : rawlam n b1} {r2 : rawlam n b2} 
    {e1 : lam gam r1 (t1 => t2)} {e1' : lam gam r1' (t1 => t2)} {e2 : lam gam r2 t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type tn} {b1 b2 : bool} {r1 : rawlam (Suc n) b1} {r2 : rawlam n False} {r2' : rawlam n b2} 
    {e1 : lam (t1 :: gam) r1 t2} {e2  : lam gam r2 t1} {e2' : lam gam r2' t1} -> eval e2 e2' -> eval (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type tn} {b1 b2 : bool} {r1 : rawlam (Suc n) b1} {r2 : rawlam n True} {r3 : rawlam n b2} {sub : rawsubst FZ r1 r2 == (b2 , r3)}
    {e1 : lam (t1 :: gam) r1 t2} {e2 : lam gam r2 t1} {e3 : lam gam r3 t2} -> subst FZ e1 e2 == (b2 , r3 , sub , e3) -> eval (App (Abs e1) e2) e3
  EvalLet1 : {t1 t2 : type tn} {b1 b2 : bool} {r1 : rawlam n False} {r1' : rawlam n b1} {r2 : rawlam (Suc n) b2} 
    {e1 : lam gam r1 t1} {e1' : lam gam r1' t1} {e2 : lam (t1 :: gam) r2 t2} -> eval e1 e1' -> eval (Let e1 e2) (Let e1' e2)
  EvalLet2 : {t1 t2 : type tn} {b1 b2 : bool} {r1 : rawlam n True} {r2 : rawlam (Suc n) b1} {r3 : rawlam n b2} {sub : rawsubst FZ r2 r1 == (b2 , r3)}
    {e1 : lam gam r1 t1} {e2 : lam (t1 :: gam) r2 t2} {e3 : lam gam r3 t2} -> subst FZ e2 e1 == (b2 , r3 , sub , e3) -> eval (Let e1 e2) e3
  EvalProj1 : {rn : nat} {ts : vect (type tn) rn} {b : bool} {r : rawlam n False} {r' : rawlam n b} 
    {e : lam gam r (Tuple ts)} {e' : lam gam r' (Tuple ts)} {p : fin rn} -> eval e e' -> eval (Proj e p) (Proj e' p)
  EvalProj2 : {rn : nat} {ts : vect (type tn) rn} {b1 b2 : bool} {rr : rawrec n b1} {r2 : rawlam n b2} 
    {r : rec gam rr ts} {p : fin rn} {e : lam gam r2 (ts ! p)} {look : rr rawlookup naturalize p == Some (b2 , r2)} -> 
    r lookup p == (b2 , r2 , look , e) -> eval (Proj (Tuple r) p) e
  EvalCase1 : {pn : nat} {t : type tn} {ts : vect (type tn) pn} {b : bool} {r : rawlam n False} {r' : rawlam n b} {rp : rawpat n}
    {e : lam gam r (Variant ts)} {e' : lam gam r' (Variant ts)} {ps : pat t gam rp ts} -> eval e e' -> eval (Case e ps) (Case e' ps)
  EvalCase2 : {pn : nat} {t : type tn} {ts : vect (type tn) pn} {l : fin pn} {b1 b2 : bool} {r : rawlam n b1} {r' : rawlam n b2} {rp : rawpat n}
    {e : lam gam r (ts ! l)} {e' : lam gam r' t} {ps : pat t gam rp ts} -> evalPat l e ps e' -> eval (Case (Variant l e) ps) e'
--  EvalUnfold1 : {t : type (Suc tn)} {t2 : type tn} {b : bool} {r : rawlam n False} {r' : rawlam n b}
--    {e : lam gam r (Rec t)} {e' : lam gam r' (Rec t)} {eq : tsubst FZ (Rec t) t == t2} -> eval e e' -> eval (Unfold t e eq) (Unfold t e' eq)
--  EvalUnfold2 : {t : type (Suc tn)} {b : bool} {r : rawlam n b} {e : lam gam r (tsubst FZ (Rec t) t)} -> eval (Unfold t (Fold t e Refl) Refl) e
data evalPat {n} {tn} {t} {gam} where
  EvalPat1 :  {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} {b1 b2 b3 : bool} {r1 : rawlam n b1} {r2 : rawlam (Suc n) b2} {r3 : rawlam n b3} {rp : rawpat n} 
    {sub : rawsubst FZ r2 r1 == (b3 , r3)} {e1 : lam gam r1 t2} {e2 : lam (t2 :: gam) r2 t} {e3 : lam gam r3 t} {ps : pat t gam rp ts} ->
    subst FZ e2 e1 == (b3 , r3 , sub , e3) -> evalPat FZ e1 (Match e2 ps) e3
  EvalPat2 : {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} {l : fin pn} {b1 b2 b3 : bool} {r1 : rawlam n b1} {r2 : rawlam (Suc n) b2} {rp : rawpat n} {r' : rawlam n b3}
   {e1 : lam gam r1 (ts ! l)} {e2 : lam (t2 :: gam) r2 t} {ps : pat t gam rp ts} {e' : lam gam r' t} -> evalPat l e1 ps e' -> evalPat (FS l) e1 (Match e2 ps) e'

evaluate : {t : type Zero} {r : rawlam Zero False} (e : lam [] r t) -> bool * λ b -> rawlam Zero b * λ r' -> raweval r r' × lam [] r' t * eval e
evaluatePat : {t : type Zero} {pn : nat} {ts : vect (type Zero) pn} {b : bool} {r : rawlam Zero b} {rp : rawpat Zero} 
  (l : fin pn) (e : lam [] r (ts ! l)) (ps : pat t [] rp ts) -> bool * λ b -> rawlam Zero b * λ r' -> rawevalPat (naturalize l) r rp r' × lam [] r' t * evalPat l e ps
evaluate (Var () pf)
evaluate (App {b1 = True} {True} (Abs e1) e2)        with inspect (subst FZ e1 e2)
evaluate (App {b1 = True} {True} (Abs e1) e2)        | It (_ , _ , req , e3) eq = _ , _ , EvalApp3 req , e3 , EvalApp3 eq
evaluate (App {b1 = True} {False} (Abs e1) e2)       with evaluate e2
evaluate (App {b1 = True} {False} (Abs e1) e2)       | _ , _ , rev , e2' , ev = False , _ , EvalApp2 rev , App (Abs e1) e2' , EvalApp2 ev
evaluate (App {b1 = False} e1 e2)                    with evaluate e1 
evaluate (App {b1 = False} e1 e2)                    | _ , _ , rev , e1' , ev = False , _ , EvalApp1 rev , App e1' e2 , EvalApp1 ev
evaluate (Let {b1 = True} e1 e2)                     with inspect (subst FZ e2 e1)
evaluate (Let {b1 = True} e1 e2)                     | It (_ , _ , req , e3) eq = _ , _ , EvalLet2 req , e3 , EvalLet2 eq
evaluate (Let {b1 = False} e1 e2)                    with evaluate e1
evaluate (Let {b1 = False} e1 e2)                    | _ , _ , rev , e1' , ev = _ , _ , EvalLet1 rev , Let e1' e2 , EvalLet1 ev
evaluate (Proj {b = True} (Tuple r) p)               with inspect (r lookup p) 
evaluate (Proj {b = True} (Tuple r) p)               | It (_ , _ , req , e') eq = _ , _ , EvalProj2 req , e' , EvalProj2 eq
evaluate (Proj {b = False} e p)                      with evaluate e
evaluate (Proj {b = False} e p)                      | _ , _ , rev , e' , ev = False , _ , EvalProj1 rev , Proj e' p , EvalProj1 ev
evaluate (Case {b = True} (Variant l e) ps)          with evaluatePat l e ps 
evaluate (Case {b = True} (Variant l e) ps)          | _ , _ , rev , e' , ev = _ , _ , EvalCase2 rev , e' , EvalCase2 ev
evaluate (Case {b = False} e ps)                     with evaluate e
evaluate (Case {b = False} e ps)                     | _ , _ , rev , e' , ev = False , _ , EvalCase1 rev , Case e' ps , EvalCase1 ev
--evaluate (Unfold t {b = True} (Fold .t e Refl) Refl) = _ , _ , EvalUnfold2 , e , EvalUnfold2
--evaluate (Unfold t {b = False} e Refl)               with evaluate e
--evaluate (Unfold t {b = False} e Refl)               | _ , _ ,  rev , e' , ev = False , _ , EvalUnfold1 rev , Unfold t e' Refl , EvalUnfold1 ev
evaluatePat ()     e1 Fail
evaluatePat FZ     e1 (Match e2 p) with inspect (subst FZ e2 e1) 
evaluatePat FZ     e1 (Match e2 p) | It (b , _ , req , e') eq = b , _ , EvalPat1 req , e' , EvalPat1 eq
evaluatePat (FS l) e1 (Match e2 p) with evaluatePat l e1 p
evaluatePat (FS l) e1 (Match e2 p) | b , _ , rev , e' , ev = b , _ , EvalPat2 rev , e' , EvalPat2 ev
