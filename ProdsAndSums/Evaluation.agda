module  ProdsAndSums.Evaluation where

open import Basics
open import Fin
open import Vect
open import ProdsAndSums.Type
open import ProdsAndSums.Term

data isVal  {n : nat} {gam : vect type n} : {t : type} -> lam gam t -> Set where
  AbsVal : {t1 t2 : type} (e : lam (t2 :: gam) t1) -> isVal (Abs e)
  TupleVal : {tn : nat} {ts : vect type tn} (es : (i : fin tn) -> lam gam (ts ! i)) -> ((i : fin tn) -> isVal (es i)) -> isVal (Tuple {ts = ts} es)

data eval {n : nat} {gam : vect type n} : {t : type} -> lam gam t -> lam gam t -> Set where
  EvalApp1 : {t1 t2 : type} {e1 e1' : lam gam (t1 => t2)} {e2 : lam gam t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type} {e1 : lam (t1 :: gam) t2} {e2 e2' : lam gam t1} -> eval e2 e2' -> eval (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type} {e1 : lam (t1 :: gam) t2} {e2 : lam gam t1} -> isVal e2 -> eval (App (Abs e1) e2) (subst FZ e1 e2)
  EvalLet1 : {t1 t2 : type} {e1 e1' : lam gam t1} {e2 : lam (t1 :: gam) t2} -> eval e1 e1' -> eval (Let e1 e2) (Let e1' e2)
  EvalLet2 : {t1 t2 : type} {e1 : lam gam t1} {e2 : lam (t1 :: gam) t2} -> isVal e1 -> eval (Let e1 e2) (subst FZ e2 e1)
  EvalTup : {tn : nat} {ts : vect type tn} {es es' : (i : fin tn) -> lam gam (ts ! i)} (k : fin tn) -> 
    ((i : fin tn) -> k >=F i -> not (k == i) -> isVal (es i)) -> ((i : fin tn) -> not (k == i) -> es i == es' i) -> eval (es k) (es' k) -> 
      eval (Tuple {ts = ts} es) (Tuple es')
  EvalProj1 : {tn : nat} {ts : vect type tn} {e e' : lam gam (Tuple ts)} {p : fin tn} -> eval e e' -> eval (Proj e p) (Proj e' p)
  EvalProj2 : {tn : nat} {ts : vect type tn} {es : (i : fin tn) -> lam gam (ts ! i)} {p : fin tn} -> ((i : fin tn) -> isVal (es i)) ->
    eval (Proj (Tuple {ts = ts} es) p) (es p)

evaluate : {t : type} (e : lam [] t) -> isVal e \/ (lam [] t * eval e)
evaluate (Var () pf)
evaluate (App e1        e2) with evaluate e1
evaluate (App .(Abs e1) e2) | InL (AbsVal e1) with evaluate e2
evaluate (App .(Abs e1) e2) | InL (AbsVal e1) | InL x          = InR (subst FZ e1 e2 , EvalApp3 x)
evaluate (App .(Abs e1) e2) | InL (AbsVal e1) | InR (e2' , ev) = InR (App (Abs e1) e2' , EvalApp2 ev)
evaluate (App e1        e2) | InR (e1' , ev)  = InR (App e1' e2 , EvalApp1 ev)
evaluate (Abs e)            = InL (AbsVal e)
evaluate (Let e1 e2)        with evaluate e1
evaluate (Let e1 e2)        | InL v          = InR (subst FZ e2 e1 , EvalLet2 v)
evaluate (Let e1 e2)        | InR (e1' , ev) = InR (Let e1' e2 , EvalLet1 ev)
evaluate (Tuple es)         = {!!}
evaluate (Proj e p)         = {!!}

valNormal : {n : nat} {gam : vect type n} {t : type} (e : lam gam t) -> isVal e -> not (lam gam t * eval e)
valNormal .(Abs e)    (AbsVal e)       (e' , ())
valNormal .(Tuple es) (TupleVal es vs) (Tuple es' , EvalTup k vals eqs ev) with valNormal (es k) (vs k) (es' k , ev)
valNormal .(Tuple es) (TupleVal es vs) (Tuple es' , EvalTup k vals eqs ev) | ()

determinate : {t : type} {e e' e'' : lam [] t} (ev : eval e e') (ev' : eval e e'') -> e' == e''
determinate {e = Var x pf}  ()             ev'
determinate {e = App e1 e2} (EvalApp1 ev)  (EvalApp1 ev')  rewrite determinate ev ev' = Refl
determinate {e = App ._ e2} (EvalApp1 ())  (EvalApp2 ev')
determinate {e = App ._ e2} (EvalApp1 ())  (EvalApp3 x)
determinate {e = App ._ e2} (EvalApp2 ev)  (EvalApp1 ())
determinate {e = App ._ e2} (EvalApp2 ev)  (EvalApp2 ev')  rewrite determinate ev ev' = Refl
determinate {e = App ._ e2} (EvalApp2 ev)  (EvalApp3 val)  with valNormal e2 val (_ , ev)
determinate {e = App ._ e2} (EvalApp2 ev)  (EvalApp3 val)  | ()
determinate {e = App ._ e2} (EvalApp3 val) (EvalApp1 ())
determinate {e = App ._ e2} (EvalApp3 val) (EvalApp2 ev')  with valNormal e2 val (_ , ev')
determinate {e = App ._ e2} (EvalApp3 val) (EvalApp2 ev')  | ()
determinate {e = App ._ e2} (EvalApp3 val) (EvalApp3 x)    = Refl
determinate {e = Abs e}     ()             ev'
determinate {e = Let e1 e2} (EvalLet1 ev)  (EvalLet1 ev')  rewrite determinate  ev ev' = Refl
determinate {e = Let e1 e2} (EvalLet1 ev)  (EvalLet2 val)  with valNormal e1 val (_ , ev)
determinate {e = Let e1 e2} (EvalLet1 ev)  (EvalLet2 val)  | ()
determinate {e = Let e1 e2} (EvalLet2 val) (EvalLet1 ev)   with valNormal e1 val (_ , ev)
determinate {e = Let e1 e2} (EvalLet2 val) (EvalLet1 ev)   | ()
determinate {e = Let e1 e2} (EvalLet2 val) (EvalLet2 val') = Refl
determinate {e = Tuple es}  ev ev' = {!!}
determinate {e = Proj e p}  ev ev' = {!!}

