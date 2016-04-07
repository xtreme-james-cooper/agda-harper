module LambdaEval where

open import Basics
open import LambdaType
open import LambdaTerm

data isVal  {n tn : nat} {gam : vect (type tn) n} : {t : type tn} -> lam gam t -> Set where
  AbsVal : {t1 t2 : type tn} (e : lam (t2 :: gam) t1) -> isVal (Abs e)
  TrivVal : isVal Triv
  PairVal : {t1 t2 : type tn} (e1 : lam gam t1) (e2 : lam gam t2) -> isVal e1 -> isVal e2 -> isVal (Pair e1 e2)
  InjVal : {t1 t2 : type tn} (d : direction) (e : lam gam (proj d t1 t2)) -> isVal e -> isVal (Inj d e)
  FoldVal : {t : type (Suc tn)} {pf : postype FZ t} {e : lam gam (tsubst FZ t pf (Ind t))} -> isVal (Fold pf e)
  GenVal : {t : type (Suc tn)} {t2 : type tn} {pf : postype FZ t} {e0 : lam (t2 :: gam) (tsubst FZ t pf t2)} {e : lam gam t2} -> isVal (Gen pf e0 e)

data eval {n tn : nat} {gam : vect (type tn) n} : {t : type tn} -> lam gam t -> lam gam t -> Set where
  EvalApp1 : {t1 t2 : type tn} {e1 e1' : lam gam (t1 => t2)} {e2 : lam gam t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type tn} {e1 : lam (t1 :: gam) t2} {e2 e2' : lam gam t1} -> eval e2 e2' -> eval (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type tn} {e1 : lam (t1 :: gam) t2} {e2 : lam gam t1} -> isVal e2 -> eval (App (Abs e1) e2) (subst FZ e1 e2)
  EvalPair1 : {t1 t2 : type tn} {e1 e1' : lam gam t1} {e2 : lam gam t2} -> eval e1 e1' -> eval (Pair e1 e2) (Pair e1' e2)
  EvalPair2 : {t1 t2 : type tn} {e1 : lam gam t1} {e2 e2' : lam gam t2} -> isVal e1 -> eval e2 e2' -> eval (Pair e1 e2) (Pair e1 e2')
  EvalProj1 : {t1 t2 : type tn} {d : direction} {e e' : lam gam (t1 X t2)} -> eval e e' -> eval (Proj d e) (Proj d e')
  EvalProj2 : {t1 t2 : type tn} {e1 : lam gam t1} {e2 : lam gam t2} -> isVal e1 -> isVal e2 -> eval (Proj L (Pair e1 e2)) e1
  EvalProj3 : {t1 t2 : type tn} {e1 : lam gam t1} {e2 : lam gam t2} -> isVal e1 -> isVal e2 -> eval (Proj R (Pair e1 e2)) e2
  EvalAbort : {t : type tn} {e e' : lam gam Void} -> eval e e' -> eval {t = t} (Abort e) (Abort e')
  EvalInj : {t1 t2 : type tn} {d : direction} {e e' : lam gam (proj d t1 t2)} -> eval e e' -> eval (Inj d e) (Inj d e')
  EvalCase1 : {t1 t2 t : type tn} {e e' : lam gam (t1 + t2)} {el : lam (t1 :: gam) t} {er : lam (t2 :: gam) t} -> eval e e' -> eval (Case e el er) (Case e' el er)
  EvalCase2 : {t1 t2 t : type tn} {e : lam gam t1} {el : lam (t1 :: gam) t} {er : lam (t2 :: gam) t} -> isVal e -> eval (Case (Inj L e) el er) (subst FZ el e)
  EvalCase3 : {t1 t2 t : type tn} {e : lam gam t2} {el : lam (t1 :: gam) t} {er : lam (t2 :: gam) t} -> isVal e -> eval (Case (Inj R e) el er) (subst FZ er e)
  EvalRec1 : {t : type (Suc tn)} {t2 : type tn} {pf : postype FZ t} {e0 : lam (tsubst FZ t pf t2 :: gam) t2} {e e' : lam gam (Ind t)} -> eval e e' -> 
    eval (Rec pf e0 e) (Rec pf e0 e')
  EvalRec2 : {t : type (Suc tn)} {t2 : type tn} {pf : postype FZ t} {e0 : lam (tsubst FZ t pf t2 :: gam) t2} {e2 : lam gam (tsubst FZ t pf (Ind t))} ->
    eval (Rec pf e0 (Fold pf e2)) (subst FZ e0 (Map FZ t pf (Rec pf (incr (FS FZ) e0) (Var FZ (Refl (Ind t)))) e2))
  EvalMapVar : {tv : fin (Suc tn)} {t1 t2 : type tn} {e : lam gam t1} {f : lam (t1 :: gam) t2} -> eval (Map tv (TyVar tv) PosVar f e) (subst FZ f e)
  EvalMapUnit : {tv : fin (Suc tn)} {t1 t2 : type tn} {e : lam gam Unit} {f : lam (t1 :: gam) t2} -> eval (Map tv Unit PosUnit f e) e
  EvalMapX : {tv : fin (Suc tn)} {t1 t2 : type (Suc tn)} {t3 t4 : type tn} {pf1 : postype tv t1} {pf2 : postype tv t2} 
    {e : lam gam (tsubst tv t1 pf1 t3 X tsubst tv t2 pf2 t3)} {f : lam (t3 :: gam) t4} -> 
      eval (Map tv (t1 X t2) (PosX pf1 pf2) f e) (Pair (Map tv t1 pf1 f (Proj L e)) (Map tv t2 pf2 f (Proj R e)))
  EvalMapVoid : {tv : fin (Suc tn)} {t1 t2 : type tn} {e : lam gam Void} {f : lam (t2 :: gam) t1} -> eval (Map tv Void PosVoid f e) (Abort e)
  EvalMap+ : {tv : fin (Suc tn)} {t1 t2 : type (Suc tn)} {t3 t4 : type tn} {pf1 : postype tv t1} {pf2 : postype tv t2} 
    {e : lam gam (tsubst tv t1 pf1 t3 + tsubst tv t2 pf2 t3)} {f : lam (t3 :: gam) t4} -> 
      eval (Map tv (t1 + t2) (Pos+ pf1 pf2) f e) 
           (Case e (Inj L (Map tv t1 pf1 (incr (FS FZ) f) (Var FZ (Refl (tsubst tv t1 pf1 t3))))) 
                   (Inj R (Map tv t2 pf2 (incr (FS FZ) f) (Var FZ (Refl (tsubst tv t2 pf2 t3))))))
  EvalMap=> : {tv : fin (Suc tn)} {t1 t2 : type (Suc tn)} {t3 t4 : type tn} {pf1 : varFree tv t1} {pf2 : postype tv t2} 
    {e : lam gam (squashOut tv t1 pf1 => tsubst tv t2 pf2 t3)} {f : lam (t3 :: gam) t4} -> 
      eval (Map tv (t1 => t2) (Pos=> pf1 pf2) f e) (Abs (Map tv t2 pf2 (incr (FS FZ) f) (App (incr FZ e) (Var FZ (Refl (squashOut tv t1 pf1))))))

evaluate : {t : type Zero} (e : lam [] t) -> isVal e \/ (lam [] t * eval e)
evaluate (Var () pf)
evaluate (App e1           e2)    with evaluate e1
evaluate (App .(Abs e1)    e2)    | InL (AbsVal e1) with evaluate e2
evaluate (App .(Abs e1)    e2)    | InL (AbsVal e1) | InL x          = InR (subst FZ e1 e2 , EvalApp3 x)
evaluate (App .(Abs e1)    e2)    | InL (AbsVal e1) | InR (e2' , ev) = InR (App (Abs e1) e2' , EvalApp2 ev)
evaluate (App e1           e2)    | InR (e1' , ev)  = InR (App e1' e2 , EvalApp1 ev)
evaluate (Abs e)                  = InL (AbsVal e)
evaluate Triv                     = InL TrivVal
evaluate (Pair e1 e2)             with evaluate e1
evaluate (Pair e1 e2)             | InL x          with evaluate e2
evaluate (Pair e1 e2)             | InL x          | InL y          = InL (PairVal e1 e2 x y)
evaluate (Pair e1 e2)             | InL x          | InR (e2' , ev) = InR (Pair e1 e2' , EvalPair2 x ev)
evaluate (Pair e1 e2)             | InR (e1' , ev) = InR (Pair e1' e2 , EvalPair1 ev)
evaluate (Proj d e)               with evaluate e
evaluate (Proj L .(Pair e1 e2))   | InL (PairVal e1 e2 x y) = InR (e1 , EvalProj2 x y)
evaluate (Proj R .(Pair e1 e2))   | InL (PairVal e1 e2 x y) = InR (e2 , EvalProj3 x y)
evaluate (Proj d e)               | InR (e' , ev)           = InR (Proj d e' , EvalProj1 ev)
evaluate (Abort e)                with evaluate e
evaluate (Abort e)                | InL ()
evaluate (Abort e)                | InR (e' , ev) = InR (Abort e' , EvalAbort ev)
evaluate (Inj d e)                with evaluate e
evaluate (Inj d e)                | InL x         = InL (InjVal d e x)
evaluate (Inj d e)                | InR (e' , ev) = InR (Inj d e' , EvalInj ev)
evaluate (Case e          el er)  with evaluate e
evaluate (Case .(Inj L e) el er)  | InL (InjVal L e x) = InR (subst FZ el e , EvalCase2 x)
evaluate (Case .(Inj R e) el er)  | InL (InjVal R e x) = InR (subst FZ er e , EvalCase3 x)
evaluate (Case e          el er)  | InR (e' , ev)      = InR (Case e' el er , EvalCase1 ev)
evaluate (Fold pf e)              = InL FoldVal
evaluate (Rec pf e0 e)            with evaluate e
evaluate (Rec pf e0 (Fold pf2 e)) | InL FoldVal   with postypeIden pf pf2
evaluate (Rec pf e0 (Fold .pf e)) | InL FoldVal | Refl .pf = InR (subst FZ e0 (Map FZ _ pf (Rec pf (incr (FS FZ) e0) (Var FZ _)) e) , EvalRec2)
evaluate (Rec pf e0 e)            | InR (e' , ev) = InR (Rec pf e0 e' , EvalRec1 ev)
evaluate (Unfold pf e)            = {!!}
evaluate (Gen pf e0 e)            = InL GenVal
evaluate (Map tv Unit        PosUnit         e0 e) = InR (e , EvalMapUnit)
evaluate (Map tv (t1 X t2)   (PosX pf1 pf2)  e0 e) = InR (Pair (Map tv t1 pf1 e0 (Proj L e)) (Map tv t2 pf2 e0 (Proj R e)) , EvalMapX)
evaluate (Map tv Void        PosVoid         e0 e) = InR (Abort e , EvalMapVoid)
evaluate (Map tv (t1 + t2)   (Pos+ pf1 pf2)  e0 e) = InR (Case e leftarg rightarg , EvalMap+)
  where 
    leftarg =  Inj L (Map tv t1 pf1 (incr (FS FZ) e0) (Var FZ _))
    rightarg = Inj R (Map tv t2 pf2 (incr (FS FZ) e0) (Var FZ _))
evaluate (Map tv (TyVar .tv) PosVar          e0 e) = InR (subst FZ e0 e , EvalMapVar)
evaluate (Map tv (t1 => t2)  (Pos=> pf1 pf2) e0 e) = InR (Abs (Map tv t2 pf2 (incr (FS FZ) e0) (App (incr FZ e) (Var FZ (Refl (squashOut tv t1 pf1))))) , EvalMap=>)
