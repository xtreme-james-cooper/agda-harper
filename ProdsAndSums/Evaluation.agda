module  ProdsAndSums.Evaluation where

open import Basics
open import Fin
open import Vect
open import ProdsAndSums.Type
open import ProdsAndSums.Term

data isVal  {n : nat} {gam : vect type n} : {t : type} -> lam gam t -> Set
data isRecVal {n : nat} {gam : vect type n} : {tn : nat} {ts : vect type tn} -> rec gam ts -> Set
data isVal {n} {gam} where
  AbsVal : {t1 t2 : type} (e : lam (t2 :: gam) t1) -> isVal (Abs e)
  TupleVal : {tn : nat} {ts : vect type tn} (rec : rec gam ts) -> isRecVal rec -> isVal (Tuple rec)
  VariVal : {tn : nat} {ts : vect type tn} (l : fin tn) (e : lam gam (ts ! l)) -> isVal e -> isVal (Variant {ts = ts} l e)
data isRecVal {n} {gam} where
  UnitVal : isRecVal Unit
  FieldVal : {tn : nat} {t : type} {ts : vect type tn} (e : lam gam t) (r : rec gam ts) -> isVal e -> isRecVal r -> isRecVal (Field e r)

_lookup_ : {n tn : nat} {gam : vect type n} {ts : vect type tn} -> rec gam ts -> (p : fin tn) -> lam gam (ts ! p)
Unit      lookup ()
Field e r lookup FZ   = e
Field e r lookup FS p = r lookup p

data eval {n : nat} {gam : vect type n} : {t : type} -> lam gam t -> lam gam t -> Set
data evalRec {n : nat} {gam : vect type n} : {tn : nat} {ts : vect type tn} -> rec gam ts -> rec gam ts -> Set
data evalPat {n : nat} {t : type} {gam : vect type n} : {tn : nat} {ts : vect type tn} (l : fin tn) -> lam gam (ts ! l) -> pat t gam ts -> lam gam t -> Set
data eval {n} {gam} where
  EvalApp1 : {t1 t2 : type} {e1 e1' : lam gam (t1 => t2)} {e2 : lam gam t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type} {e1 : lam (t1 :: gam) t2} {e2 e2' : lam gam t1} -> eval e2 e2' -> eval (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type} {e1 : lam (t1 :: gam) t2} {e2 : lam gam t1} -> isVal e2 -> eval (App (Abs e1) e2) (subst FZ e1 e2)
  EvalLet1 : {t1 t2 : type} {e1 e1' : lam gam t1} {e2 : lam (t1 :: gam) t2} -> eval e1 e1' -> eval (Let e1 e2) (Let e1' e2)
  EvalLet2 : {t1 t2 : type} {e1 : lam gam t1} {e2 : lam (t1 :: gam) t2} -> isVal e1 -> eval (Let e1 e2) (subst FZ e2 e1)
  EvalTup : {tn : nat} {ts : vect type tn} {r r' : rec gam ts} -> evalRec r r' -> eval (Tuple r) (Tuple r')
  EvalProj1 : {tn : nat} {ts : vect type tn} {e e' : lam gam (Tuple ts)} {p : fin tn} -> eval e e' -> eval (Proj e p) (Proj e' p)
  EvalProj2 : {tn : nat} {ts : vect type tn} {r : rec gam ts} {p : fin tn} -> isRecVal r -> eval (Proj (Tuple r) p) (r lookup p)
  EvalVari : {tn : nat} {ts : vect type tn} {l : fin tn} {e e' : lam gam (ts ! l)} -> eval e e' -> eval (Variant {ts = ts} l e) (Variant l e')
  EvalCase1 : {tn : nat} {t : type} {ts : vect type tn} {e e' : lam gam (Variant ts)} {ps : pat t gam ts} -> eval e e' -> eval (Case e ps) (Case e' ps)
  EvalCase2 : {tn : nat} {t : type} {ts : vect type tn} {l : fin tn} {e : lam gam (ts ! l)} {e' : lam gam t} {ps : pat t gam ts} -> isVal e -> evalPat l e ps e' ->
    eval (Case (Variant l e) ps) e'
data evalRec {n} {gam} where
  EvalRec1 : {tn : nat} {t : type} {ts : vect type tn} {e : lam gam t} {r r' : rec gam ts} -> evalRec r r' -> evalRec (Field e r) (Field e r')
  EvalRec2 : {tn : nat} {t : type} {ts : vect type tn} {e e' : lam gam t} {r : rec gam ts} -> isRecVal r -> eval e e' -> evalRec (Field e r) (Field e' r)
data evalPat {n} {t} {gam} where
  EvalPat1 :  {tn : nat} {t2 : type} {ts : vect type tn} {e1 : lam gam t2} {e2 : lam (t2 :: gam) t} {ps : pat t gam ts} -> 
    evalPat FZ e1 (Match e2 ps) (subst FZ e2 e1)
  EvalPat2 : {tn : nat} {t2 : type} {ts : vect type tn} {l : fin tn} {e1 : lam gam (ts ! l)} {e2 : lam (t2 :: gam) t} {ps : pat t gam ts} {e' : lam gam t} ->
    evalPat l e1 ps e' -> evalPat (FS l) e1 (Match e2 ps) e'

evaluate : {t : type} (e : lam [] t) -> isVal e \/ (lam [] t * eval e)
evaluateRec : {tn : nat} {ts : vect type tn} (r : rec [] ts) -> isRecVal r \/ (rec [] ts * evalRec r)
evaluatePat : {t : type} {tn : nat} {ts : vect type tn} (l : fin tn) (e : lam [] (ts ! l)) (ps : pat t [] ts) -> lam [] t * evalPat l e ps
evaluate (Var () pf)
evaluate (App e1        e2)       with evaluate e1
evaluate (App .(Abs e1) e2)       | InL (AbsVal e1) with evaluate e2
evaluate (App .(Abs e1) e2)       | InL (AbsVal e1) | InL x          = InR (subst FZ e1 e2 , EvalApp3 x)
evaluate (App .(Abs e1) e2)       | InL (AbsVal e1) | InR (e2' , ev) = InR (App (Abs e1) e2' , EvalApp2 ev)
evaluate (App e1        e2)       | InR (e1' , ev)  = InR (App e1' e2 , EvalApp1 ev)
evaluate (Abs e)                  = InL (AbsVal e)
evaluate (Let e1 e2)              with evaluate e1
evaluate (Let e1 e2)              | InL v          = InR (subst FZ e2 e1 , EvalLet2 v)
evaluate (Let e1 e2)              | InR (e1' , ev) = InR (Let e1' e2 , EvalLet1 ev)
evaluate (Tuple r)                with evaluateRec r
evaluate (Tuple r)                | InL v         = InL (TupleVal r v)
evaluate (Tuple r)                | InR (r' , ev) = InR (Tuple r' , EvalTup ev)
evaluate (Proj e p)               with evaluate e
evaluate (Proj .(Tuple r) p)      | InL (TupleVal r x) = InR ((r lookup p) , EvalProj2 x)
evaluate (Proj e p)               | InR (e' , ev)      = InR (Proj e' p , EvalProj1 ev)
evaluate (Variant l e)            with evaluate e
evaluate (Variant l e)            | InL v         = InL (VariVal l e v)
evaluate (Variant l e)            | InR (e' , ev) = InR (Variant l e' , EvalVari ev)
evaluate (Case e ps)              with evaluate e
evaluate (Case .(Variant l e) ps) | InL (VariVal l e v) with evaluatePat l e ps 
evaluate (Case .(Variant l e) ps) | InL (VariVal l e v) | (e' , ev) = InR (e' , EvalCase2 v ev)
evaluate (Case e ps)              | InR (e' , ev)       = InR (Case e' ps , EvalCase1 ev)
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

valNormal : {n : nat} {gam : vect type n} {t : type} (e : lam gam t) -> isVal e -> not (lam gam t * eval e)
valRecNormal : {n tn : nat} {gam : vect type n} {ts : vect type tn} (r : rec gam ts) -> isRecVal r -> not (rec gam ts * evalRec r)
valNormal .(Abs e)       (AbsVal e)      (e' , ())
valNormal .(Tuple r)     (TupleVal r v)  (._ , EvalTup ev)  with valRecNormal r v (_ , ev)
valNormal .(Tuple r)     (TupleVal r v)  (._ , EvalTup ev)  | ()
valNormal .(Variant l e) (VariVal l e v) (._ , EvalVari ev) with valNormal e v (_ , ev)
valNormal .(Variant l e) (VariVal l e v) (._ , EvalVari ev) | ()
valRecNormal .Unit        UnitVal                  (rec' , ())
valRecNormal .(Field e r) (FieldVal e r eval rval) (._ , EvalRec1 ev)   with valRecNormal r rval (_ , ev)
valRecNormal .(Field e r) (FieldVal e r eval rval) (._ , EvalRec1 ev)   | ()
valRecNormal .(Field e r) (FieldVal e r eval rval) (._ , EvalRec2 v ev) with valNormal e eval (_ , ev)
valRecNormal .(Field e r) (FieldVal e r eval rval) (._ , EvalRec2 v ev)   | ()

determinate : {t : type} {e e' e'' : lam [] t} (ev : eval e e') (ev' : eval e e'') -> e' == e''
determinateRec : {tn : nat} {ts : vect type tn} {r r' r'' : rec [] ts} (ev : evalRec r r') (ev' : evalRec r r'') -> r' == r''
determinatePat : {t : type} {tn : nat} {ts : vect type tn} {l : fin tn} {e : lam [] (ts ! l)} {ps : pat t [] ts} {e' e'' : lam [] t} 
  (ev : evalPat l e ps e') (ev' : evalPat l e ps e'') -> e' == e''
determinate {e = Var x pf}    ()               ev'
determinate {e = App e1 e2}   (EvalApp1 ev)    (EvalApp1 ev')     rewrite determinate ev ev' = Refl
determinate {e = App ._ e2}   (EvalApp1 ())    (EvalApp2 ev')
determinate {e = App ._ e2}   (EvalApp1 ())    (EvalApp3 x)
determinate {e = App ._ e2}   (EvalApp2 ev)    (EvalApp1 ())
determinate {e = App ._ e2}   (EvalApp2 ev)    (EvalApp2 ev')     rewrite determinate ev ev' = Refl
determinate {e = App ._ e2}   (EvalApp2 ev)    (EvalApp3 val)     with valNormal e2 val (_ , ev)
determinate {e = App ._ e2}   (EvalApp2 ev)    (EvalApp3 val)     | ()
determinate {e = App ._ e2}   (EvalApp3 val)   (EvalApp1 ())
determinate {e = App ._ e2}   (EvalApp3 val)   (EvalApp2 ev')     with valNormal e2 val (_ , ev')
determinate {e = App ._ e2}   (EvalApp3 val)   (EvalApp2 ev')     | ()
determinate {e = App ._ e2}   (EvalApp3 val)   (EvalApp3 x)       = Refl
determinate {e = Abs e}       ()               ev'
determinate {e = Let e1 e2}   (EvalLet1 ev)    (EvalLet1 ev')     rewrite determinate ev ev' = Refl
determinate {e = Let e1 e2}   (EvalLet1 ev)    (EvalLet2 val)     with valNormal e1 val (_ , ev)
determinate {e = Let e1 e2}   (EvalLet1 ev)    (EvalLet2 val)     | ()
determinate {e = Let e1 e2}   (EvalLet2 val)   (EvalLet1 ev)      with valNormal e1 val (_ , ev)
determinate {e = Let e1 e2}   (EvalLet2 val)   (EvalLet1 ev)      | ()
determinate {e = Let e1 e2}   (EvalLet2 val)   (EvalLet2 val')    = Refl
determinate {e = Tuple es}    (EvalTup ev)     (EvalTup ev')      rewrite determinateRec ev ev' = Refl
determinate {e = Proj e p}    (EvalProj1 ev)   (EvalProj1 ev')    rewrite determinate ev ev' = Refl
determinate {e = Proj ._ p}   (EvalProj1 ev)   (EvalProj2 val)    with valNormal (Tuple _) (TupleVal _ val) (_ , ev)
determinate {e = Proj ._ p}   (EvalProj1 ev)   (EvalProj2 val)    | ()
determinate {e = Proj ._ p}   (EvalProj2 val)  (EvalProj1 ev)     with valNormal (Tuple _) (TupleVal _ val) (_ , ev)
determinate {e = Proj ._ p}   (EvalProj2 val)  (EvalProj1 ev)     | ()
determinate {e = Proj ._ p}   (EvalProj2 val)  (EvalProj2 val')   = Refl
determinate {e = Variant l e} (EvalVari ev)    (EvalVari ev')     rewrite determinate ev ev' = Refl
determinate {e = Case e ps}   (EvalCase1 ev)   (EvalCase1 ev')    rewrite determinate ev ev' = Refl
determinate {e = Case ._ ps}  (EvalCase1 ev)   (EvalCase2 v ev')  with valNormal (Variant _ _) (VariVal _ _ v) (_ , ev)
determinate {e = Case ._ ps}  (EvalCase1 ev)   (EvalCase2 v ev')  | ()
determinate {e = Case ._ ps}  (EvalCase2 v ev) (EvalCase1 ev')    with valNormal (Variant _ _) (VariVal _ _ v) (_ , ev')
determinate {e = Case ._ ps}  (EvalCase2 v ev) (EvalCase1 ev')    | ()
determinate {e = Case ._ ps}  (EvalCase2 v ev) (EvalCase2 v' ev') rewrite determinatePat ev ev' = Refl
determinateRec {r = Unit}      ()              ev'
determinateRec {r = Field e r} (EvalRec1 ev)   (EvalRec1 ev')    rewrite determinateRec ev ev' = Refl
determinateRec {r = Field e r} (EvalRec1 ev)   (EvalRec2 v ev')  with valRecNormal r v (_ , ev)
determinateRec {r = Field e r} (EvalRec1 ev)   (EvalRec2 v ev')  | ()
determinateRec {r = Field e r} (EvalRec2 v ev) (EvalRec1 ev')    with valRecNormal r v (_ , ev')
determinateRec {r = Field e r} (EvalRec2 v ev) (EvalRec1 ev')    | ()
determinateRec {r = Field e r} (EvalRec2 v ev) (EvalRec2 v' ev') rewrite determinate ev ev' = Refl
determinatePat {ps = Fail}       ()            ev'
determinatePat {ps = Match x ps} EvalPat1      EvalPat1       = Refl
determinatePat {ps = Match x ps} (EvalPat2 ev) (EvalPat2 ev') rewrite determinatePat ev ev' = Refl
