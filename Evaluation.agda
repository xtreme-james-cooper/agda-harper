module Evaluation where

open import Basics
open import Fin
open import Vect
open import Type
open import Term

_lookup_ : {n tn rn : nat} {gam : vect (type tn) n} {ts : vect (type tn) rn} {b : bool} -> rec gam ts b -> (p : fin rn) -> bool * lam gam (ts ! p)
Unit         lookup ()
Field e r pf lookup FZ   = _ , e
Field e r pf lookup FS p = r lookup p

evalLemma : {n tn : nat} {t2 : type tn} (gam : vect (type tn) n) (gam' : vect (type (Suc tn)) n) -> map (tincr FZ) gam == gam' -> gam == map (tsubst FZ t2) gam'
evalLemma {Zero}  {tn} {t2} []         []                                       eq   = Refl
evalLemma {Suc n} {tn} {t2} (t :: gam) (.(tincr FZ t) :: .(map (tincr FZ) gam)) Refl rewrite tsubstIncrCollapse FZ t t2 = 
  funEq (_::_ t) (evalLemma gam (map (tincr FZ) gam) Refl)

evalLemma' : {n tn : nat} {gam : vect (type tn) n} {b : bool} (t : type (Suc tn)) {t2 : type tn} -> tsubst FZ (Rec t) t == t2 -> 
  lam gam (tsubst FZ (Rec t) t) b -> lam gam t2 b
evalLemma' t pf e rewrite pf = e

data eval {n tn : nat} {gam : vect (type tn) n} : {gam' : vect (type tn) n} {t t' : type tn} {b1 b2 : bool} {pf : gam == gam'} {pf2 : t' == t} -> 
  lam gam t b1 -> lam gam' t' b2 -> Set
data evalRec {n tn : nat} {gam : vect (type tn) n} : {rn : nat} {ts : vect (type tn) rn} {b1 b2 : bool} -> rec gam ts b1 -> rec gam ts b2 -> Set
data evalPat {n tn : nat} {t : type tn} {gam : vect (type tn) n} : {pn : nat} {ts : vect (type tn) pn} {b1 b2 : bool} (l : fin pn) -> 
  lam gam (ts ! l) b1 -> pat t gam ts -> lam gam t b2 -> Set
data eval {n} {tn} {gam} where
  EvalApp1 : {t1 t2 : type tn} {b1 b2 b3 : bool} {e1 : lam gam (t1 => t2) b1} {e1' : lam gam (t1 => t2) b2} {e2 : lam gam t1 b3} -> 
    eval {pf = Refl} {Refl} e1 e1' -> eval {pf = Refl} {Refl} (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type tn} {b1 b2 b3 : bool} {e1 : lam (t1 :: gam) t2 b1} {e2  : lam gam t1 b2} {e2' : lam gam t1 b3} -> 
    eval {pf = Refl} {Refl} e2 e2' -> eval {pf = Refl} {Refl} (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type tn} {b1 b2 : bool} {e1 : lam (t1 :: gam) t2 b1} {e2 : lam gam t1 True} {e3 : lam gam t2 b2} -> 
    (b2 , e3) == subst FZ e1 e2 -> eval {pf = Refl} {Refl} (App (Abs e1) e2) e3
  EvalLet1 : {t1 t2 : type tn} {b1 b2 b3 : bool} {e1 : lam gam t1 b1} {e1' : lam gam t1 b2} {e2 : lam (t1 :: gam) t2 b3} -> 
    eval {pf = Refl} {Refl} e1 e1' -> eval {pf = Refl} {Refl} (Let e1 e2) (Let e1' e2)
  EvalLet2 : {t1 t2 : type tn} {b1 b2 : bool} {e1 : lam gam t1 True} {e2 : lam (t1 :: gam) t2 b1} {e3 : lam gam t2 b2} -> 
    (b2 , e3) == subst FZ e2 e1 -> eval {pf = Refl} {Refl} (Let e1 e2) e3
  EvalTup : {rn : nat} {ts : vect (type tn) rn} {b1 b2 : bool} {r : rec gam ts b1} {r' : rec gam ts b2} -> evalRec r r' -> eval {pf = Refl} {Refl} (Tuple r) (Tuple r')
  EvalProj1 : {rn : nat} {ts : vect (type tn) rn} {b1 b2 : bool} {e : lam gam (Tuple ts) b1} {e' : lam gam (Tuple ts) b2} {p : fin rn} -> 
    eval {pf = Refl} {Refl} e e' -> eval {pf = Refl} {Refl} (Proj e p) (Proj e' p)
  EvalProj2 : {rn : nat} {ts : vect (type tn) rn} {r : rec gam ts True} {p : fin rn} {b : bool} {e : lam gam (ts ! p) b} -> 
    (r lookup p) == (b , e) -> eval {pf = Refl} {Refl} (Proj (Tuple r) p) e
  EvalVari : {pn : nat} {ts : vect (type tn) pn} {l : fin pn} {b1 b2 : bool} {e : lam gam (ts ! l) b1} {e' : lam gam (ts ! l) b2} -> 
    eval {pf = Refl} {Refl} e e' -> eval {pf = Refl} {Refl} (Variant {ts = ts} l e) (Variant l e')
  EvalCase1 : {pn : nat} {t : type tn} {ts : vect (type tn) pn} {b1 b2 : bool} {e : lam gam (Variant ts) b1} {e' : lam gam (Variant ts) b2} {ps : pat t gam ts} -> 
    eval {pf = Refl} {Refl} e e' -> eval {pf = Refl} {Refl} (Case e ps) (Case e' ps)
  EvalCase2 : {pn : nat} {t : type tn} {ts : vect (type tn) pn} {l : fin pn} {b : bool} {e : lam gam (ts ! l) True} {e' : lam gam t b} {ps : pat t gam ts} -> 
    evalPat l e ps e' -> eval {pf = Refl} {Refl} (Case (Variant l e) ps) e'
  EvalFold : {t : type (Suc tn)} {b1 b2 : bool} {e : lam gam (tsubst FZ (Rec t) t) b1} {e' : lam gam (tsubst FZ (Rec t) t) b2} -> 
    eval {pf = Refl} {Refl} e e' -> eval {pf = Refl} {Refl} (Fold t e Refl) (Fold t e' Refl)
  EvalUnfold1 : {t : type (Suc tn)} {t2 : type tn} {b1 b2 : bool} {e : lam gam (Rec t) b1} {e' : lam gam (Rec t) b2} {eq : tsubst FZ (Rec t) t == t2} -> 
    eval {pf = Refl} {Refl} e e' -> eval {pf = Refl} {Refl} (Unfold t e eq) (Unfold t e' eq)
  EvalUnfold2 : {t : type (Suc tn)} {t2 : type tn} {b : bool} {e : lam gam (tsubst FZ (Rec t) t) b} {eq : tsubst FZ (Rec t) t == t2} -> 
    eval {pf = Refl} {sym eq} (Unfold t (Fold t e Refl) Refl) (evalLemma' t eq e) 
  EvalTApp1 : {t1 : type (Suc tn)} {b1 b2 : bool} {e : lam gam (Forall t1) b1} {e' : lam gam (Forall t1) b2} {t2 t3 : type tn} {pf : tsubst FZ t2 t1 == t3} ->
    eval {pf = Refl} {Refl} e e' -> eval {pf = Refl} {Refl} (TApp e t2 pf) (TApp e' t2 pf)
  EvalTApp2 : {t1 : type (Suc tn)} {gam' : vect (type (Suc tn)) n} {b : bool} {e : lam gam' t1 b} {pf1 : map (tincr FZ) gam == gam'} {t2 t3 : type tn} 
    (pf2 : tsubst FZ t2 t1 == t3) -> eval {pf = evalLemma gam gam' pf1} {pf2} (TApp (TAbs e pf1) t2 pf2) (tesubst FZ t2 e)
data evalRec {n} {tn} {gam} where
  EvalRec1 : {rn : nat} {t : type tn} {ts : vect (type tn) rn} {b1 b2 b3 : bool} {e : lam gam t b1} {r : rec gam ts b2} {r' : rec gam ts b3} -> 
    evalRec r r' -> evalRec (Field e r Refl) (Field e r' Refl)
  EvalRec2 : {rn : nat} {t : type tn} {ts : vect (type tn) rn} {b1 b2 : bool} {e : lam gam t b1} {e' : lam gam t b2} {r : rec gam ts True} -> 
    eval {pf = Refl} {Refl} e e' -> evalRec (Field e r Refl) (Field e' r Refl)
data evalPat {n} {tn} {t} {gam} where
  EvalPat1 :  {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} {b1 b2 : bool} {e1 : lam gam t2 True} {e2 : lam (t2 :: gam) t b1} {e3 : lam gam t b2} 
    {ps : pat t gam ts} -> (b2 , e3) == subst FZ e2 e1 -> evalPat FZ e1 (Match e2 ps) e3
  EvalPat2 : {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} {l : fin pn} {b1 b2 b3 : bool} {e1 : lam gam (ts ! l) b1} {e2 : lam (t2 :: gam) t b2} {ps : pat t gam ts} 
   {e' : lam gam t b3} -> evalPat l e1 ps e' -> evalPat (FS l) e1 (Match e2 ps) e'

valNonEval : {t : type Zero} (e : lam [] t True) -> not (bool * (λ b -> lam [] t b * eval {pf = Refl} {Refl} e))
valNonEvalRec : {rn : nat} {ts : vect (type Zero) rn} (r : rec [] ts True) -> not (bool * (λ b -> rec [] ts b * evalRec r))
valNonEval (Abs e)          (b , (e' , ()))
valNonEval (Tuple r)        (b , (_ , EvalTup ev))  = valNonEvalRec r (b , (_ , ev))
valNonEval (Variant l e)    (b , (_ , EvalVari ev)) = valNonEval e (b , (_ , ev))
valNonEval (Fold t e .Refl) (b , (_ , EvalFold ev)) = valNonEval e (b , (_ , ev))
valNonEval (TAbs e pf)      (b , (e' , ()))
valNonEvalRec {Zero}   Unit                         (b , (r' , ()))
valNonEvalRec {Suc rn} (Field {b1 = True} e r Refl) (b , (_ , EvalRec1 ev)) = valNonEvalRec r (b , (_ , ev))
valNonEvalRec {Suc rn} (Field {b1 = True} e r Refl) (_ , (_ , EvalRec2 ev)) = valNonEval e (_ , (_ , ev))
valNonEvalRec {Suc rn} (Field {b1 = False} e r ())  (b , (r' , ev)) 

evaluate : {t : type Zero} (e : lam [] t False) -> bool * (λ b -> lam [] t b * eval {pf = Refl} {Refl} e)
evaluateRec : {rn : nat} {ts : vect (type Zero) rn} (r : rec [] ts False ) -> bool * (λ b -> rec [] ts b * evalRec r)
evaluatePat : {t : type Zero} {pn : nat} {ts : vect (type Zero) pn} (l : fin pn) (e : lam [] (ts ! l) True) (ps : pat t [] ts) -> bool * (λ b -> lam [] t b * evalPat l e ps)
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
evaluate (Tuple r)                                   with evaluateRec r
evaluate (Tuple r)                                   | _ , (r' , ev) = _ , (Tuple r' , EvalTup ev)
evaluate (Proj {b = True} (Tuple r) p)               with inspect (r lookup p) 
evaluate (Proj {b = True} (Tuple r) p)               | It (b , e') eq = b , (e' , EvalProj2 eq)
evaluate (Proj {b = False} e p)                      with evaluate e
evaluate (Proj {b = False} e p)                      | _ , (e' , ev) = False , (Proj e' p , EvalProj1 ev)
evaluate (Variant l e)                               with evaluate e
evaluate (Variant l e)                               | _ , (e' , ev) = _ , (Variant l e' , EvalVari ev)
evaluate (Case {b = True} (Variant l e) ps)          with evaluatePat l e ps 
evaluate (Case {b = True} (Variant l e) ps)          | _ , (e' , ev) = _ , (e' , EvalCase2 ev)
evaluate (Case {b = False} e ps)                     with evaluate e
evaluate (Case {b = False} e ps)                     | _ , (e' , ev) = False , (Case e' ps , EvalCase1 ev)
evaluate (Fold t e Refl)                             with evaluate e
evaluate (Fold t e Refl)                             | _ , (e' , ev) = _ , (Fold t e' Refl , EvalFold ev)
evaluate (Unfold t {b = True} (Fold .t e Refl) Refl) = True , (e , EvalUnfold2)
evaluate (Unfold t {b = False} e Refl)               with evaluate e
evaluate (Unfold t {b = False} e Refl)               | _ , (e' , ev) = False , (Unfold t e' Refl , EvalUnfold1 ev)
evaluate (TApp {b = True} (TAbs e Refl) t Refl)      = _ , (tesubst FZ t e , EvalTApp2 Refl)
evaluate (TApp {b = False} e t pf)                   with evaluate e
evaluate (TApp {b = False} e t pf)                   | _ , (e' , ev) = False , (TApp e' t pf , EvalTApp1 ev)
evaluateRec (Field {b1 = True} {True} e r ())
evaluateRec (Field {b1 = False} {True} e r Refl)  with evaluate e
evaluateRec (Field {b1 = False} {True} e r Refl)  | b , (e' , ev) = _ , (Field e' r Refl , EvalRec2 ev)
evaluateRec (Field {b1 = True} {False} e r Refl)  with evaluateRec r
evaluateRec (Field {b1 = True} {False} e r Refl)  | b , (r' , ev) = b , (Field e r' Refl , EvalRec1 ev)
evaluateRec (Field {b1 = False} {False} e r Refl) with evaluateRec r
evaluateRec (Field {b1 = False} {False} e r Refl) | b , (r' , ev) = False , (Field e r' Refl , EvalRec1 ev)
evaluatePat ()     e1 Fail
evaluatePat FZ     e1 (Match e2 p) with inspect (subst FZ e2 e1) 
evaluatePat FZ     e1 (Match e2 p) | It (b , e') eq = b , (e' , EvalPat1 (sym eq))
evaluatePat (FS l) e1 (Match e2 p) with evaluatePat l e1 p
evaluatePat (FS l) e1 (Match e2 p) | b , (e' , ev) = b , (e' , EvalPat2 ev)
