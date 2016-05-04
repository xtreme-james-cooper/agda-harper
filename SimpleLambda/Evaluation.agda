module SimpleLambda.Evaluation where

open import Basics
open import Fin
open import Vect
open import SimpleLambda.Type
open import SimpleLambda.Term

data isVal  {n : nat} {gam : vect type n} : {t : type} -> lam gam t -> Set where
  AbsVal : {t1 t2 : type} (e : lam (t2 :: gam) t1) -> isVal (Abs e)
  TrueVal : isVal True
  FalseVal : isVal False

data eval {n : nat} {gam : vect type n} : {t : type} -> lam gam t -> lam gam t -> Set where
  EvalApp1 : {t1 t2 : type} {e1 e1' : lam gam (t1 => t2)} {e2 : lam gam t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type} {e1 : lam (t1 :: gam) t2} {e2 e2' : lam gam t1} -> eval e2 e2' -> eval (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type} {e1 : lam (t1 :: gam) t2} {e2 : lam gam t1} -> isVal e2 -> eval (App (Abs e1) e2) (subst FZ e1 e2)
  EvalIf1 : {t1 : type} {b b' : lam gam Bool} {t f : lam gam t1} -> eval b b' -> eval (If b t f) (If b' t f)
  EvalIf2 : {t1 : type} {t f : lam gam t1} -> eval (If True t f) t
  EvalIf3 : {t1 : type} {t f : lam gam t1} -> eval (If False t f) f

evaluate : {t : type} (e : lam [] t) -> isVal e \/ (lam [] t * eval e)
evaluate (Var () pf)
evaluate (App e1        e2) with evaluate e1
evaluate (App .(Abs e1) e2) | InL (AbsVal e1) with evaluate e2
evaluate (App .(Abs e1) e2) | InL (AbsVal e1) | InL x          = InR (subst FZ e1 e2 , EvalApp3 x)
evaluate (App .(Abs e1) e2) | InL (AbsVal e1) | InR (e2' , ev) = InR (App (Abs e1) e2' , EvalApp2 ev)
evaluate (App e1        e2) | InR (e1' , ev)  = InR (App e1' e2 , EvalApp1 ev)
evaluate (Abs e)            = InL (AbsVal e)
evaluate True               = InL TrueVal
evaluate False              = InL FalseVal
evaluate (If b t f)         with evaluate b
evaluate (If .True t f)     | InL TrueVal   = InR (t , EvalIf2)
evaluate (If .False t f)    | InL FalseVal  = InR (f , EvalIf3)
evaluate (If b t f)         | InR (b' , ev) = InR (If b' t f , EvalIf1 ev)
