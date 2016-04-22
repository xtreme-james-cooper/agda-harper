module LambdaEval where

open import Basics
open import Fin
open import Vect
open import LambdaType
open import LambdaTerm

data isVal  {n tn : nat} {gam : vect (type tn) n} : {t : type tn} -> lam gam t -> Set where
  AbsVal : {t1 t2 : type tn} (e : lam (t2 :: gam) t1) -> isVal (Abs e)
  TAbsVal : {t : type (Suc tn)} {gam' : vect (type (Suc tn)) n} (e : lam gam' t) (pf : map (tincr FZ) gam == gam') -> isVal (TAbs e pf)

evalLemma : {n tn : nat} {t2 : type tn} (gam : vect (type tn) n) (gam' : vect (type (Suc tn)) n) -> map (tincr FZ) gam == gam' -> gam == map (tsubst FZ t2) gam'
evalLemma {Zero}  {tn} {t2} []         []                                       eq   = Refl
evalLemma {Suc n} {tn} {t2} (t :: gam) (.(tincr FZ t) :: .(map (tincr FZ) gam)) Refl rewrite tsubstIncrCollapse FZ t t2 = 
  funEq (_::_ t) (evalLemma gam (map (tincr FZ) gam) Refl)

data eval {n tn : nat} {gam : vect (type tn) n} : {gam' : vect (type tn) n} {t t' : type tn} {pf : gam == gam'} {pf2 : t' == t} -> lam gam t -> lam gam' t' -> Set where
  EvalApp1 : {t1 t2 : type tn} {e1 e1' : lam gam (t1 => t2)} {e2 : lam gam t1} -> eval {pf = Refl} {Refl} e1 e1' -> eval {pf = Refl} {Refl} (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type tn} {e1 : lam (t1 :: gam) t2} {e2 e2' : lam gam t1} -> eval {pf = Refl} {Refl} e2 e2' -> 
    eval {pf = Refl} {Refl} (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type tn} {e1 : lam (t1 :: gam) t2} {e2 : lam gam t1} -> isVal e2 -> eval {pf = Refl} {Refl} (App (Abs e1) e2) (subst FZ e1 e2)
  EvalTApp1 : {t1 : type (Suc tn)} {e e' : lam gam (Forall t1)} {t2 t3 : type tn} {pf : tsubst FZ t2 t1 == t3} -> eval {pf = Refl} {Refl} e e' -> 
    eval {pf = Refl} {Refl} (TApp e t2 pf) (TApp e' t2 pf)
  EvalTApp2 : {t1 : type (Suc tn)} {gam' : vect (type (Suc tn)) n} {e : lam gam' t1} {pf1 : map (tincr FZ) gam == gam'} {t2 t3 : type tn} (pf2 : tsubst FZ t2 t1 == t3) -> 
    eval {pf = evalLemma gam gam' pf1} {pf2} (TApp (TAbs e pf1) t2 pf2) (tesubst FZ t2 e)

evaluate : {t : type Zero} (e : lam [] t) -> isVal e \/ (lam [] t * eval e)
evaluate (Var () pf)
evaluate (App e1           e2)                               with evaluate e1
evaluate (App .(Abs e1)    e2)                               | InL (AbsVal e1) with evaluate e2
evaluate (App .(Abs e1)    e2)                               | InL (AbsVal e1) | InL x          = InR (subst FZ e1 e2 , EvalApp3 x)
evaluate (App .(Abs e1)    e2)                               | InL (AbsVal e1) | InR (e2' , ev) = InR (App (Abs e1) e2' , EvalApp2 ev)
evaluate (App e1           e2)                               | InR (e1' , ev)  = InR (App e1' e2 , EvalApp1 ev)
evaluate (Abs e)                                             = InL (AbsVal e)
evaluate (TApp {t1} e t {t2} pf)                             with evaluate e
evaluate (TApp {t1} .(TAbs e pf) t {.(tsubst FZ t t1)} Refl) | InL (TAbsVal {gam' = []} e pf) = InR (tesubst FZ t e , EvalTApp2 Refl)
evaluate (TApp {t1} e t {t2} pf)                             | InR (e' , ev)      = InR (TApp e' t pf , EvalTApp1 ev)
evaluate (TAbs e pf)                                         = InL (TAbsVal e pf)
