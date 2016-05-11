module RecursiveTypes.Evaluation where

open import Basics
open import Fin
open import Vect
open import RecursiveTypes.Type
open import RecursiveTypes.Term

data isVal  {n tn : nat} {gam : vect (type tn) n} : {t : type tn} -> lam gam t -> Set
data isRecVal {n tn : nat} {gam : vect (type tn) n} : {rn : nat} {ts : vect (type tn) rn} -> rec gam ts -> Set
data isVal {n} {tn} {gam} where
  AbsVal : {t1 t2 : type tn} (e : lam (t2 :: gam) t1) -> isVal (Abs e)
  TupleVal : {rn : nat} {ts : vect (type tn) rn} (rec : rec gam ts) -> isRecVal rec -> isVal (Tuple rec)
  VariVal : {pn : nat} {ts : vect (type tn) pn} (l : fin pn) (e : lam gam (ts ! l)) -> isVal e -> isVal (Variant {ts = ts} l e)
  FoldVal : {t : type (Suc tn)} (e : lam gam (tsubst FZ (Rec t) t)) -> isVal e -> isVal (Fold t e)
data isRecVal {n} {tn} {gam} where
  UnitVal : isRecVal Unit
  FieldVal : {rn : nat} {t : type tn} {ts : vect (type tn) rn} (e : lam gam t) (r : rec gam ts) -> isVal e -> isRecVal r -> isRecVal (Field e r)

_lookup_ : {n tn rn : nat} {gam : vect (type tn) n} {ts : vect (type tn) rn} -> rec gam ts -> (p : fin rn) -> lam gam (ts ! p)
Unit      lookup ()
Field e r lookup FZ   = e
Field e r lookup FS p = r lookup p

data eval {n tn : nat} {gam : vect (type tn) n} : {t t' : type tn} {pf : t == t'} -> lam gam t -> lam gam t' -> Set
data evalRec {n tn : nat} {gam : vect (type tn) n} : {rn : nat} {ts : vect (type tn) rn} -> rec gam ts -> rec gam ts -> Set
data evalPat {n tn : nat} {t : type tn} {gam : vect (type tn) n} : {pn : nat} {ts : vect (type tn) pn} (l : fin pn) -> lam gam (ts ! l) -> pat t gam ts -> lam gam t -> Set
data eval {n} {tn} {gam} where
  EvalApp1 : {t1 t2 : type tn} {e1 e1' : lam gam (t1 => t2)} {e2 : lam gam t1} -> eval {pf = Refl} e1 e1' -> eval {pf = Refl} (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type tn} {e1 : lam (t1 :: gam) t2} {e2 e2' : lam gam t1} -> eval {pf = Refl} e2 e2' -> eval {pf = Refl} (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type tn} {e1 : lam (t1 :: gam) t2} {e2 : lam gam t1} -> isVal e2 -> eval {pf = Refl} (App (Abs e1) e2) (subst FZ e1 e2)
  EvalLet1 : {t1 t2 : type tn} {e1 e1' : lam gam t1} {e2 : lam (t1 :: gam) t2} -> eval {pf = Refl} e1 e1' -> eval {pf = Refl} (Let e1 e2) (Let e1' e2)
  EvalLet2 : {t1 t2 : type tn} {e1 : lam gam t1} {e2 : lam (t1 :: gam) t2} -> isVal e1 -> eval {pf = Refl} (Let e1 e2) (subst FZ e2 e1)
  EvalTup : {rn : nat} {ts : vect (type tn) rn} {r r' : rec gam ts} -> evalRec r r' -> eval {pf = Refl} (Tuple r) (Tuple r')
  EvalProj1 : {rn : nat} {ts : vect (type tn) rn} {e e' : lam gam (Tuple ts)} {p : fin rn} -> eval {pf = Refl} e e' -> eval {pf = Refl} (Proj e p) (Proj e' p)
  EvalProj2 : {rn : nat} {ts : vect (type tn) rn} {r : rec gam ts} {p : fin rn} -> isRecVal r -> eval {pf = Refl} (Proj (Tuple r) p) (r lookup p)
  EvalVari : {pn : nat} {ts : vect (type tn) pn} {l : fin pn} {e e' : lam gam (ts ! l)} -> eval {pf = Refl} e e' -> eval {pf = Refl} (Variant {ts = ts} l e) (Variant l e')
  EvalCase1 : {pn : nat} {t : type tn} {ts : vect (type tn) pn} {e e' : lam gam (Variant ts)} {ps : pat t gam ts} -> eval {pf = Refl} e e' -> 
    eval {pf = Refl} (Case e ps) (Case e' ps)
  EvalCase2 : {pn : nat} {t : type tn} {ts : vect (type tn) pn} {l : fin pn} {e : lam gam (ts ! l)} {e' : lam gam t} {ps : pat t gam ts} -> isVal e -> evalPat l e ps e' ->
    eval {pf = Refl} (Case (Variant l e) ps) e'
  EvalFold : {t : type (Suc tn)} {e e' : lam gam (tsubst FZ (Rec t) t)} -> eval {pf = Refl} e e' -> eval {pf = Refl} (Fold t e) (Fold t e')
  EvalUnfold1 : {t : type (Suc tn)} {t2 : type tn} {e e' : lam gam (Rec t)} {eq : tsubst FZ (Rec t) t == t2} -> eval {pf = Refl} e e' -> 
    eval {pf = Refl} (Unfold t e eq) (Unfold t e' eq)
  EvalUnfold2 : {t : type (Suc tn)} {t2 : type tn} {e : lam gam (tsubst FZ (Rec t) t)} {eq : tsubst FZ (Rec t) t == t2} -> eval {pf = sym eq} (Unfold t (Fold t e) eq) e
data evalRec {n} {tn} {gam} where
  EvalRec1 : {rn : nat} {t : type tn} {ts : vect (type tn) rn} {e : lam gam t} {r r' : rec gam ts} -> evalRec r r' -> evalRec (Field e r) (Field e r')
  EvalRec2 : {rn : nat} {t : type tn} {ts : vect (type tn) rn} {e e' : lam gam t} {r : rec gam ts} -> isRecVal r -> eval {pf = Refl} e e' -> evalRec (Field e r) (Field e' r)
data evalPat {n} {tn} {t} {gam} where
  EvalPat1 :  {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} {e1 : lam gam t2} {e2 : lam (t2 :: gam) t} {ps : pat t gam ts} -> 
    evalPat FZ e1 (Match e2 ps) (subst FZ e2 e1)
  EvalPat2 : {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} {l : fin pn} {e1 : lam gam (ts ! l)} {e2 : lam (t2 :: gam) t} {ps : pat t gam ts} {e' : lam gam t} ->
    evalPat l e1 ps e' -> evalPat (FS l) e1 (Match e2 ps) e'

evaluate : {t : type Zero} (e : lam [] t) -> isVal e \/ (lam [] t * eval e)
evaluateRec : {rn : nat} {ts : vect (type Zero) rn} (r : rec [] ts) -> isRecVal r \/ (rec [] ts * evalRec r)
evaluatePat : {t : type Zero} {pn : nat} {ts : vect (type Zero) pn} (l : fin pn) (e : lam [] (ts ! l)) (ps : pat t [] ts) -> lam [] t * evalPat l e ps
evaluate (Var () pf)
evaluate (App e1        e2)          with evaluate e1
evaluate (App .(Abs e1) e2)          | InL (AbsVal e1) with evaluate e2
evaluate (App .(Abs e1) e2)          | InL (AbsVal e1) | InL x          = InR (subst FZ e1 e2 , EvalApp3 x)
evaluate (App .(Abs e1) e2)          | InL (AbsVal e1) | InR (e2' , ev) = InR (App (Abs e1) e2' , EvalApp2 ev)
evaluate (App e1        e2)          | InR (e1' , ev)  = InR (App e1' e2 , EvalApp1 ev)
evaluate (Abs e)                     = InL (AbsVal e)
evaluate (Let e1 e2)                 with evaluate e1
evaluate (Let e1 e2)                 | InL v          = InR (subst FZ e2 e1 , EvalLet2 v)
evaluate (Let e1 e2)                 | InR (e1' , ev) = InR (Let e1' e2 , EvalLet1 ev)
evaluate (Tuple r)                   with evaluateRec r
evaluate (Tuple r)                   | InL v         = InL (TupleVal r v)
evaluate (Tuple r)                   | InR (r' , ev) = InR (Tuple r' , EvalTup ev)
evaluate (Proj e p)                  with evaluate e
evaluate (Proj .(Tuple r) p)         | InL (TupleVal r x) = InR ((r lookup p) , EvalProj2 x)
evaluate (Proj e p)                  | InR (e' , ev)      = InR (Proj e' p , EvalProj1 ev)
evaluate (Variant l e)               with evaluate e
evaluate (Variant l e)               | InL v         = InL (VariVal l e v)
evaluate (Variant l e)               | InR (e' , ev) = InR (Variant l e' , EvalVari ev)
evaluate (Case e ps)                 with evaluate e
evaluate (Case .(Variant l e) ps)    | InL (VariVal l e v) with evaluatePat l e ps 
evaluate (Case .(Variant l e) ps)    | InL (VariVal l e v) | (e' , ev) = InR (e' , EvalCase2 v ev)
evaluate (Case e ps)                 | InR (e' , ev)       = InR (Case e' ps , EvalCase1 ev)
evaluate (Fold t e)                  with evaluate e
evaluate (Fold t e)                  | InL v         = InL (FoldVal e v)
evaluate (Fold t e)                  | InR (e' , ev) = InR (Fold t e' , EvalFold ev)
evaluate (Unfold t e eq)             with evaluate e
evaluate (Unfold t .(Fold t e) Refl) | InL (FoldVal e v) = InR (e , EvalUnfold2)
evaluate (Unfold t e eq)             | InR (e' , ev)     = InR (Unfold t e' eq , EvalUnfold1 ev)
evaluateRec Unit        = InL UnitVal
evaluateRec (Field e r) with evaluateRec r
evaluateRec (Field e r) | InL v         with evaluate e
evaluateRec (Field e r) | InL v         | InL v2        = InL (FieldVal e r v2 v)
evaluateRec (Field e r) | InL v         | InR (e' , ev) = InR (Field e' r , EvalRec2 v ev)
evaluateRec (Field e r) | InR (r' , ev) = InR (Field e r' , EvalRec1 ev)
evaluatePat ()     e1 Fail
evaluatePat FZ     e1 (Match e2 ps) = (subst FZ e2 e1 , EvalPat1)
evaluatePat (FS l) e1 (Match e2 ps) with evaluatePat l e1 ps
evaluatePat (FS l) e1 (Match e2 ps) | (e' , ev) = (e' , EvalPat2 ev)
