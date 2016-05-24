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

data eval {n tn : nat} {gam : vect (type tn) n} : {gam' : vect (type tn) n} {t t' : type tn} {b : bool} {pf : gam == gam'} {pf2 : t' == t} -> 
  lam gam t False -> lam gam' t' b -> Set
data evalPat {n tn : nat} {t : type tn} {gam : vect (type tn) n} : {pn : nat} {ts : vect (type tn) pn} {b1 b2 : bool} (l : fin pn) -> 
  lam gam (ts ! l) b1 -> pat t gam ts -> lam gam t b2 -> Set
data eval {n} {tn} {gam} where
  EvalApp1 : {t1 t2 : type tn} {b1 b2 : bool} {e1 : lam gam (t1 => t2) False} {e1' : lam gam (t1 => t2) b1} {e2 : lam gam t1 b2} -> 
    eval {pf = Refl} {Refl} e1 e1' -> eval {pf = Refl} {Refl} (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type tn} {b1 b2 : bool} {e1 : lam (t1 :: gam) t2 b1} {e2  : lam gam t1 False} {e2' : lam gam t1 b2} -> 
    eval {pf = Refl} {Refl} e2 e2' -> eval {pf = Refl} {Refl} (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type tn} {b1 b2 : bool} {e1 : lam (t1 :: gam) t2 b1} {e2 : lam gam t1 True} {e3 : lam gam t2 b2} -> 
    (b2 , e3) == subst FZ e1 e2 -> eval {pf = Refl} {Refl} (App (Abs e1) e2) e3
  EvalLet1 : {t1 t2 : type tn} {b1 b2 : bool} {e1 : lam gam t1 False} {e1' : lam gam t1 b1} {e2 : lam (t1 :: gam) t2 b2} -> 
    eval {pf = Refl} {Refl} e1 e1' -> eval {pf = Refl} {Refl} (Let e1 e2) (Let e1' e2)
  EvalLet2 : {t1 t2 : type tn} {b1 b2 : bool} {e1 : lam gam t1 True} {e2 : lam (t1 :: gam) t2 b1} {e3 : lam gam t2 b2} -> 
    (b2 , e3) == subst FZ e2 e1 -> eval {pf = Refl} {Refl} (Let e1 e2) e3
  EvalProj1 : {rn : nat} {ts : vect (type tn) rn} {b : bool} {e : lam gam (Tuple ts) False} {e' : lam gam (Tuple ts) b} {p : fin rn} -> 
    eval {pf = Refl} {Refl} e e' -> eval {pf = Refl} {Refl} (Proj e p) (Proj e' p)
  EvalProj2 : {rn : nat} {ts : vect (type tn) rn} {b1 b2 : bool} {r : rec gam ts b1} {p : fin rn} {e : lam gam (ts ! p) b2} -> 
    (r lookup p) == (b2 , e) -> eval {pf = Refl} {Refl} (Proj (Tuple r) p) e
  EvalCase1 : {pn : nat} {t : type tn} {ts : vect (type tn) pn} {b : bool} {e : lam gam (Variant ts) False} {e' : lam gam (Variant ts) b} {ps : pat t gam ts} -> 
    eval {pf = Refl} {Refl} e e' -> eval {pf = Refl} {Refl} (Case e ps) (Case e' ps)
  EvalCase2 : {pn : nat} {t : type tn} {ts : vect (type tn) pn} {l : fin pn} {b1 b2 : bool} {e : lam gam (ts ! l) b1} {e' : lam gam t b2} {ps : pat t gam ts} -> 
    evalPat l e ps e' -> eval {pf = Refl} {Refl} (Case (Variant l e) ps) e'
  EvalUnfold1 : {t : type (Suc tn)} {t2 : type tn} {b : bool} {e : lam gam (Rec t) False} {e' : lam gam (Rec t) b} {eq : tsubst FZ (Rec t) t == t2} -> 
    eval {pf = Refl} {Refl} e e' -> eval {pf = Refl} {Refl} (Unfold t e eq) (Unfold t e' eq)
  EvalUnfold2 : {t : type (Suc tn)} {t2 : type tn} {b : bool} {e : lam gam (tsubst FZ (Rec t) t) b} {eq : tsubst FZ (Rec t) t == t2} -> 
    eval {pf = Refl} {sym eq} (Unfold t (Fold t e Refl) Refl) (evalLemma' t eq e) 
data evalPat {n} {tn} {t} {gam} where
  EvalPat1 :  {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} {b1 b2 b3 : bool} {e1 : lam gam t2 b1} {e2 : lam (t2 :: gam) t b2} {e3 : lam gam t b3} 
    {ps : pat t gam ts} -> (b3 , e3) == subst FZ e2 e1 -> evalPat FZ e1 (Match e2 ps) e3
  EvalPat2 : {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} {l : fin pn} {b1 b2 b3 : bool} {e1 : lam gam (ts ! l) b1} {e2 : lam (t2 :: gam) t b2} {ps : pat t gam ts} 
   {e' : lam gam t b3} -> evalPat l e1 ps e' -> evalPat (FS l) e1 (Match e2 ps) e'

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
