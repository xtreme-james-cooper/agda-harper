module Lambda where

open import Basics

data type : nat -> Set where
  N : {tn : nat} -> type tn
  _=>_ : {tn : nat} -> type tn -> type tn -> type tn
  Unit : {tn : nat} -> type tn
  _X_ : {tn : nat} -> type tn -> type tn -> type tn
  Void : {tn : nat} -> type tn
  _+_ : {tn : nat} -> type tn -> type tn -> type tn
  TyVar : {tn : nat} -> fin tn -> type tn

data direction : Set where
  L : direction
  R : direction

proj : {tn : nat} -> direction -> type tn -> type tn -> type tn
proj L t1 t2 = t1
proj R t1 t2 = t2

data lam {n tn : nat} (gam : vect (type tn) n) : type tn -> Set where
  Var : {t : type tn} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type tn} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type tn} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)
  Zero : lam gam N
  Succ : lam gam N -> lam gam N
  Rec : {t : type tn} -> lam gam t -> lam (t :: (N :: gam)) t -> lam gam N -> lam gam t
  Triv : lam gam Unit
  Pair : {t1 t2 : type tn} -> lam gam t1 -> lam gam t2 -> lam gam (t1 X t2)
  Proj : {t1 t2 : type tn} (d : direction) -> lam gam (t1 X t2) -> lam gam (proj d t1 t2)
  Abort : {t : type tn} -> lam gam Void -> lam gam t
  Inj : {t1 t2 : type tn} (d : direction) -> lam gam (proj d t1 t2) -> lam gam (t1 + t2)
  Case : {t1 t2 t : type tn} -> lam gam (t1 + t2) -> lam (t1 :: gam) t -> lam (t2 :: gam) t -> lam gam t

incr : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam gam t2 -> lam  (insertAt x gam t1) t2
incr {gam = gam} x (Var y (Refl .(gam ! y))) = Var (fincr y x) (insertAtFincr gam y x _)
incr             x (App e1 e2)               = App (incr x e1) (incr x e2)
incr             x (Abs e)                   = Abs (incr (fincr x FZ) e)
incr             x Zero                      = Zero
incr             x (Succ e)                  = Succ (incr x e)
incr             x (Rec e0 es e)             = Rec (incr x e0) (incr (fincr (fincr x FZ) FZ) es) (incr x e)
incr             x Triv                      = Triv
incr             x (Pair e1 e2)              = Pair (incr x e1) (incr x e2)
incr             x (Proj d e)                = Proj d (incr x e)
incr             x (Abort e)                 = Abort (incr x e)
incr             x (Inj d e)                 = Inj d (incr x e)
incr             x (Case e el er)            = Case (incr x e) (incr (fincr x FZ) el) (incr (fincr x FZ) er)

subst : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
subst x (Var y pf)         v with fin_eq y x
subst x (Var .x (Refl ._)) v | Yes (Refl .x) = v castTo (funEq (lam _) (flip (lookupInsertAt _ x _)))
subst x (Var y pf)         v | No npf        = Var (fdecr y x npf) (insertAtFdecr npf pf)
subst x (App e1 e2)        v = App (subst x e1 v) (subst x e2 v)
subst x (Abs e)            v = Abs (subst (fincr x FZ) e (incr FZ v))
subst x Zero               v = Zero
subst x (Succ e)           v = Succ (subst x e v)
subst x (Rec e0 es e)      v = Rec (subst x e0 v) (subst (fincr (fincr x FZ) FZ) es (incr FZ (incr FZ v))) (subst x e v)
subst x Triv               v = Triv
subst x (Pair e1 e2)       v = Pair (subst x e1 v) (subst x e2 v)
subst x (Proj d e)         v = Proj d (subst x e v)
subst x (Abort e)          v = Abort (subst x e v)
subst x (Inj d e)          v = Inj d (subst x e v)
subst x (Case e el er)     v = Case (subst x e v) (subst (fincr x FZ) el (incr FZ v)) (subst (fincr x FZ) er (incr FZ v))

data isVal {n tn : nat} {gam : vect (type tn) n} : {t : type tn} -> lam gam t -> Set where
  AbsVal : {t1 t2 : type tn} (e : lam (t2 :: gam) t1) -> isVal (Abs e)
  ZeroVal : isVal Zero
  SuccVal : (e : lam gam N) -> isVal e -> isVal (Succ e)
  TrivVal : isVal Triv
  PairVal : {t1 t2 : type tn} (e1 : lam gam t1) (e2 : lam gam t2) -> isVal e1 -> isVal e2 -> isVal (Pair e1 e2)
  InjVal : {t1 t2 : type tn} (d : direction) (e : lam gam (proj d t1 t2)) -> isVal e -> isVal (Inj d e)

data eval {n tn : nat} {gam : vect (type tn) n} : {t : type tn} -> lam gam t -> lam gam t -> Set where
  EvalApp1 : {t1 t2 : type tn} {e1 e1' : lam gam (t1 => t2)} {e2 : lam gam t1} -> eval e1 e1' -> eval (App e1 e2) (App e1' e2)
  EvalApp2 : {t1 t2 : type tn} {e1 : lam (t1 :: gam) t2} {e2 e2' : lam gam t1} -> eval e2 e2' -> eval (App (Abs e1) e2) (App (Abs e1) e2')
  EvalApp3 : {t1 t2 : type tn} {e1 : lam (t1 :: gam) t2} {e2 : lam gam t1} -> isVal e2 -> eval (App (Abs e1) e2) (subst FZ e1 e2)
  EvalSucc : {e e' : lam gam N} -> eval e e' -> eval (Succ e) (Succ e')
  EvalRec1 : {t : type tn} {e e' : lam gam N} {e0 : lam gam t} {es : lam (t :: (N :: gam)) t} -> eval e e' -> eval (Rec e0 es e) (Rec e0 es e')
  EvalRec2 : {t : type tn} {e0 : lam gam t} {es : lam (t :: (N :: gam)) t} -> eval (Rec e0 es Zero) e0
  EvalRec3 : {t : type tn} {e : lam gam N} {e0 : lam gam t} {es : lam (t :: (N :: gam)) t} -> isVal e -> 
    eval (Rec e0 es (Succ e)) (subst FZ (subst FZ es (incr FZ (Rec e0 es e))) e)
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

evaluate : {t : type Zero} (e : lam [] t) -> isVal e \/ (lam [] t * eval e)
evaluate (Var () pf)
evaluate (App e1           e2)   with evaluate e1
evaluate (App .(Abs e1)    e2)   | InL (AbsVal e1) with evaluate e2
evaluate (App .(Abs e1)    e2)   | InL (AbsVal e1) | InL x          = InR (subst FZ e1 e2 , EvalApp3 x)
evaluate (App .(Abs e1)    e2)   | InL (AbsVal e1) | InR (e2' , ev) = InR (App (Abs e1) e2' , EvalApp2 ev)
evaluate (App e1           e2)   | InR (e1' , ev)  = InR (App e1' e2 , EvalApp1 ev)
evaluate (Abs e)                 = InL (AbsVal e)
evaluate Zero                    = InL ZeroVal
evaluate (Succ e)                with evaluate e
evaluate (Succ e)                | InL x         = InL (SuccVal e x)
evaluate (Succ e)                | InR (e' , ev) = InR (Succ e' , EvalSucc ev)
evaluate (Rec e0 es e)           with evaluate e
evaluate (Rec e0 es .Zero)       | InL ZeroVal       = InR (e0 , EvalRec2)
evaluate (Rec e0 es .(Succ e))   | InL (SuccVal e x) = InR (subst FZ (subst FZ es (incr FZ (Rec e0 es e))) e , EvalRec3 x)
evaluate (Rec e0 es e)           | InR (e' , ev)     = InR (Rec e0 es e' , EvalRec1 ev)
evaluate Triv                    = InL TrivVal
evaluate (Pair e1 e2)            with evaluate e1
evaluate (Pair e1 e2)            | InL x          with evaluate e2
evaluate (Pair e1 e2)            | InL x          | InL y          = InL (PairVal e1 e2 x y)
evaluate (Pair e1 e2)            | InL x          | InR (e2' , ev) = InR (Pair e1 e2' , EvalPair2 x ev)
evaluate (Pair e1 e2)            | InR (e1' , ev) = InR (Pair e1' e2 , EvalPair1 ev)
evaluate (Proj d e)              with evaluate e
evaluate (Proj L .(Pair e1 e2))  | InL (PairVal e1 e2 x y) = InR (e1 , EvalProj2 x y)
evaluate (Proj R .(Pair e1 e2))  | InL (PairVal e1 e2 x y) = InR (e2 , EvalProj3 x y)
evaluate (Proj d e)              | InR (e' , ev)           = InR (Proj d e' , EvalProj1 ev)
evaluate (Abort e)               with evaluate e
evaluate (Abort e)               | InL ()
evaluate (Abort e)               | InR (e' , ev) = InR (Abort e' , EvalAbort ev)
evaluate (Inj d e)               with evaluate e
evaluate (Inj d e)               | InL x         = InL (InjVal d e x)
evaluate (Inj d e)               | InR (e' , ev) = InR (Inj d e' , EvalInj ev)
evaluate (Case e el er)          with evaluate e
evaluate (Case .(Inj L e) el er) | InL (InjVal L e x) = InR (subst FZ el e , EvalCase2 x)
evaluate (Case .(Inj R e) el er) | InL (InjVal R e x) = InR (subst FZ er e , EvalCase3 x)
evaluate (Case e el er)          | InR (e' , ev) = InR (Case e' el er , EvalCase1 ev)
