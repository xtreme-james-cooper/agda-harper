module LambdaEval where

open import Basics
open import LambdaType
open import LambdaTerm

data isVal  {n tn : nat} {gam : vect (type tn) n} : {t : type tn} -> lam gam t -> Set where
  AbsVal : {t1 t2 : type tn} (e : lam (t2 :: gam) t1) -> isVal (Abs e)
  TAbsVal : {t : type (Suc tn)} {gam' : vect (type (Suc tn)) n} (e : lam gam' t) (pf : map (tincr FZ) gam == gam') -> isVal (TAbs e pf)

data eval {n tn : nat} {gam : vect (type tn) n} : {t : type tn} -> lam gam t -> lam gam t -> Set where
  EvalApp1 : {t1 t2 : type tn} {e1 e1' : lam gam (t1 => t2)} {e2 : lam gam t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type tn} {e1 : lam (t1 :: gam) t2} {e2 e2' : lam gam t1} -> eval e2 e2' -> eval (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type tn} {e1 : lam (t1 :: gam) t2} {e2 : lam gam t1} -> isVal e2 -> eval (App (Abs e1) e2) (subst FZ e1 e2)
  EvalTApp1 : {t1 : type (Suc tn)} {e e' : lam gam (Forall t1)} {t2 t3 : type tn} {pf : tsubst FZ t2 t1 == t3} -> eval e e' -> eval (TApp e t2 pf) (TApp e' t2 pf)
  EvalTApp2 : {t1 : type (Suc tn)} {gam' : vect (type (Suc tn)) n} {e : lam gam' t1} {pf1 : map (tincr FZ) gam == gam'} {t2 t3 : type tn} {pf2 : tsubst FZ t2 t1 == t3} -> 
    eval (TApp (TAbs e pf1) t2 pf2) (tesubst FZ t2 e)

evaluate : {t : type Zero} (e : lam [] t) -> isVal e \/ (lam [] t * eval e)
evaluate (Var () pf)
evaluate (App e1           e2)      with evaluate e1
evaluate (App .(Abs e1)    e2)      | InL (AbsVal e1) with evaluate e2
evaluate (App .(Abs e1)    e2)      | InL (AbsVal e1) | InL x          = InR (subst FZ e1 e2 , EvalApp3 x)
evaluate (App .(Abs e1)    e2)      | InL (AbsVal e1) | InR (e2' , ev) = InR (App (Abs e1) e2' , EvalApp2 ev)
evaluate (App e1           e2)      | InR (e1' , ev)  = InR (App e1' e2 , EvalApp1 ev)
evaluate (Abs e)                    = InL (AbsVal e)
evaluate (TApp e t pf)              with evaluate e
evaluate (TApp .(TAbs e pf) t pf2)  | InL (TAbsVal e pf) = {!!}
evaluate (TApp e t pf)              | InR (e' , ev) = InR (TApp e' t pf , EvalTApp1 ev)
evaluate (TAbs e pf)                = InL (TAbsVal e pf)
