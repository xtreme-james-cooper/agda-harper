module Lambda where

open import Basics

data type (tn : nat) : Set where
  _=>_ : type tn -> type tn -> type tn
  Unit : type tn
  _X_ : type tn -> type tn -> type tn
  Void : type tn
  _+_ : type tn -> type tn -> type tn
  TyVar : fin tn -> type tn
  Ind : type (Suc tn) -> type tn
  CoInd : type (Suc tn) -> type tn

data varFree {tn : nat} (tv : fin tn) : type tn -> Set where
  VarFree=> : {t1 t2 : type tn} -> varFree tv t1 -> varFree tv t2 -> varFree tv (t1 => t2)
  VarFreeUnit : varFree tv Unit
  VarFreeX : {t1 t2 : type tn} -> varFree tv t1 -> varFree tv t2 -> varFree tv (t1 X t2)
  VarFreeVoid : varFree tv Void
  VarFree+ : {t1 t2 : type tn} -> varFree tv t1 -> varFree tv t2 -> varFree tv (t1 + t2)
  VarFreeVar : {tv' : fin tn} -> not (tv' == tv) -> varFree tv (TyVar tv')
  VarFreeInd : {t : type (Suc tn)} -> varFree (fincr tv FZ) t -> varFree tv (Ind t)
  VarFreeCoInd : {t : type (Suc tn)} -> varFree (fincr tv FZ) t -> varFree tv (CoInd t)

checkFreeness : {tn : nat} (tv : fin tn) (t : type tn) -> decide (varFree tv t) 
checkFreeness tv (t1 => t2) with checkFreeness tv t1
checkFreeness tv (t1 => t2) | Yes pf1 with checkFreeness tv t2
checkFreeness tv (t1 => t2) | Yes pf1 | Yes pf2 = Yes (VarFree=> pf1 pf2)
checkFreeness tv (t1 => t2) | Yes pf1 | No npf  = No (ck=>2 npf)
  where
    ck=>2 : {tn : nat} {tv : fin tn} {t1 t2 : type tn} -> not (varFree tv t2) -> not (varFree tv (t1 => t2))
    ck=>2 npf (VarFree=> pf1 pf2) = npf pf2
checkFreeness tv (t1 => t2) | No npf  = No (ck=>1 npf)
  where
    ck=>1 : {tn : nat} {tv : fin tn} {t1 t2 : type tn} -> not (varFree tv t1) -> not (varFree tv (t1 => t2))
    ck=>1 npf (VarFree=> pf1 pf2) = npf pf1
checkFreeness tv Unit = Yes VarFreeUnit
checkFreeness tv (t1 X t2) with checkFreeness tv t1
checkFreeness tv (t1 X t2) | Yes pf1 with checkFreeness tv t2
checkFreeness tv (t1 X t2) | Yes pf1 | Yes pf2 = Yes (VarFreeX pf1 pf2)
checkFreeness tv (t1 X t2) | Yes pf1 | No npf  = No (ckX2 npf)
  where
    ckX2 : {tn : nat} {tv : fin tn} {t1 t2 : type tn} -> not (varFree tv t2) -> not (varFree tv (t1 X t2))
    ckX2 npf (VarFreeX pf1 pf2) = npf pf2
checkFreeness tv (t1 X t2) | No npf  = No (ckX1 npf)
  where
    ckX1 : {tn : nat} {tv : fin tn} {t1 t2 : type tn} -> not (varFree tv t1) -> not (varFree tv (t1 X t2))
    ckX1 npf (VarFreeX pf1 pf2) = npf pf1
checkFreeness tv Void = Yes VarFreeVoid
checkFreeness tv (t1 + t2) with checkFreeness tv t1
checkFreeness tv (t1 + t2) | Yes pf1 with checkFreeness tv t2
checkFreeness tv (t1 + t2) | Yes pf1 | Yes pf2 = Yes (VarFree+ pf1 pf2)
checkFreeness tv (t1 + t2) | Yes pf1 | No npf  = No (ck+2 npf)
  where
    ck+2 : {tn : nat} {tv : fin tn} {t1 t2 : type tn} -> not (varFree tv t2) -> not (varFree tv (t1 + t2))
    ck+2 npf (VarFree+ pf1 pf2) = npf pf2
checkFreeness tv (t1 + t2) | No npf  = No (ck+1 npf)
  where
    ck+1 : {tn : nat} {tv : fin tn} {t1 t2 : type tn} -> not (varFree tv t1) -> not (varFree tv (t1 + t2))
    ck+1 npf (VarFree+ pf1 pf2) = npf pf1
checkFreeness tv (TyVar tv') with fin_eq tv' tv
checkFreeness tv (TyVar .tv) | Yes (Refl .tv) = No (ckVar tv)
  where
    ckVar : {tn : nat} (tv : fin tn) -> not (varFree tv (TyVar tv))
    ckVar tv (VarFreeVar npf) = npf (Refl tv)
checkFreeness tv (TyVar tv') | No npf         = Yes (VarFreeVar npf)
checkFreeness tv (Ind t) with checkFreeness (fincr tv FZ) t
checkFreeness tv (Ind t) | Yes pf = Yes (VarFreeInd pf)
checkFreeness tv (Ind t) | No npf = No (ckIn npf)
  where
    ckIn : {tn : nat} {tv : fin tn} {t : type (Suc tn)} -> not (varFree (fincr tv FZ) t) -> not (varFree tv (Ind t))
    ckIn npf (VarFreeInd pf) = npf pf
checkFreeness tv (CoInd t) with checkFreeness (fincr tv FZ) t
checkFreeness tv (CoInd t) | Yes pf = Yes (VarFreeCoInd pf)
checkFreeness tv (CoInd t) | No npf = No (ckCo npf)
  where
    ckCo : {tn : nat} {tv : fin tn} {t : type (Suc tn)} -> not (varFree (fincr tv FZ) t) -> not (varFree tv (CoInd t))
    ckCo npf (VarFreeCoInd pf) = npf pf

data postype {tn : nat} (tv : fin tn) : type tn -> Set where
  Pos=> : {t1 t2 : type tn} -> varFree tv t1 -> postype tv t2 -> postype tv (t1 => t2)
  PosUnit : postype tv Unit
  PosX : {t1 t2 : type tn} -> postype tv t1 -> postype tv t2 -> postype tv (t1 X t2)
  PosVoid : postype tv Void
  Pos+ : {t1 t2 : type tn} -> postype tv t1 -> postype tv t2 -> postype tv (t1 + t2)
  PosVar : postype tv (TyVar tv)

squashOut : {n : nat} (tv : fin (Suc n)) (t : type (Suc n)) -> varFree tv t -> type n
squashOut tv (t1 => t2)  (VarFree=> pf1 pf2) = squashOut tv t1 pf1 => squashOut tv t2 pf2
squashOut tv Unit        pf                  = Unit
squashOut tv (t1 X t2)   (VarFreeX pf1 pf2)  = squashOut tv t1 pf1 X squashOut tv t2 pf2
squashOut tv Void        pf                  = Void
squashOut tv (t1 + t2)   (VarFree+ pf1 pf2)  = squashOut tv t1 pf1 + squashOut tv t2 pf2
squashOut tv (TyVar tv') (VarFreeVar npf)    = TyVar (fdecr tv' tv npf)
squashOut tv (Ind t)     (VarFreeInd pf)     = Ind (squashOut (fincr tv FZ) t pf)
squashOut tv (CoInd t)   (VarFreeCoInd pf)   = Ind (squashOut (fincr tv FZ) t pf)

tsubst : {n : nat} (tv : fin (Suc n)) (t : type (Suc n)) -> postype tv t -> type n -> type n
tsubst tv Unit        PosUnit         v = Unit
tsubst tv (t1 X t2)   (PosX pf1 pf2)  v = tsubst tv t1 pf1 v X tsubst tv t2 pf2 v
tsubst tv Void        PosVoid         v = Void
tsubst tv (t1 + t2)   (Pos+ pf1 pf2)  v = tsubst tv t1 pf1 v + tsubst tv t2 pf2 v
tsubst tv (TyVar .tv) PosVar          v = v
tsubst tv (t1 => t2)  (Pos=> pf1 pf2) v = squashOut tv t1 pf1 => tsubst tv t2 pf2 v

data direction : Set where
  L : direction
  R : direction

proj : {A : Set} -> direction -> A -> A -> A
proj L t1 t2 = t1
proj R t1 t2 = t2

data lam {n tn : nat} (gam : vect (type tn) n) : type tn -> Set where
  Var : {t : type tn} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type tn} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type tn} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)
  Triv : lam gam Unit
  Pair : {t1 t2 : type tn} -> lam gam t1 -> lam gam t2 -> lam gam (t1 X t2)
  Proj : {t1 t2 : type tn} (d : direction) -> lam gam (t1 X t2) -> lam gam (proj d t1 t2)
  Abort : {t : type tn} -> lam gam Void -> lam gam t
  Inj : {t1 t2 : type tn} (d : direction) -> lam gam (proj d t1 t2) -> lam gam (t1 + t2)
  Case : {t1 t2 t : type tn} -> lam gam (t1 + t2) -> lam (t1 :: gam) t -> lam (t2 :: gam) t -> lam gam t
  Map : {rh rh' : type tn} (tv : fin (Suc tn)) (t : type (Suc tn)) (pf : postype tv t) -> lam (rh :: gam) rh' -> lam gam (tsubst tv t pf rh) -> 
    lam gam (tsubst tv t pf rh')
  Fold : {t : type (Suc tn)} (pf : postype FZ t) -> lam gam (tsubst FZ t pf (Ind t)) -> lam gam (Ind t)
  Rec : {t : type (Suc tn)} {t2 : type tn} (pf : postype FZ t) -> lam (tsubst FZ t pf t2 :: gam) t2 -> lam gam (Ind t) -> lam gam t2
  Unfold : {t : type (Suc tn)} (pf : postype FZ t) -> lam gam (CoInd t) -> lam gam (tsubst FZ t pf (CoInd t))
  Gen : {t : type (Suc tn)} {t2 : type tn} (pf : postype FZ t) -> lam (t2 :: gam) (tsubst FZ t pf t2) -> lam gam t2 -> lam gam (CoInd t)

incr : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam gam t2 -> lam  (insertAt x gam t1) t2
incr {gam = gam} x (Var y (Refl .(gam ! y))) = Var (fincr y x) (insertAtFincr gam y x _)
incr             x (App e1 e2)               = App (incr x e1) (incr x e2)
incr             x (Abs e)                   = Abs (incr (fincr x FZ) e)
incr             x Triv                      = Triv
incr             x (Pair e1 e2)              = Pair (incr x e1) (incr x e2)
incr             x (Proj d e)                = Proj d (incr x e)
incr             x (Abort e)                 = Abort (incr x e)
incr             x (Inj d e)                 = Inj d (incr x e)
incr             x (Case e el er)            = Case (incr x e) (incr (fincr x FZ) el) (incr (fincr x FZ) er)
incr             x (Map tv t pf e0 e)        = Map tv t pf (incr (fincr x FZ) e0) (incr x e)
incr             x (Fold pf e)               = Fold pf (incr x e)
incr             x (Rec pf e0 e)             = Rec pf (incr (fincr x FZ) e0) (incr x e)
incr             x (Unfold pf e)             = Unfold pf (incr x e)
incr             x (Gen pf e0 e)             = Gen pf (incr (fincr x FZ) e0) (incr x e)

subst : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
subst x (Var y pf)         v with fin_eq y x
subst x (Var .x (Refl ._)) v | Yes (Refl .x) = v castTo (funEq (lam _) (flip (lookupInsertAt _ x _)))
subst x (Var y pf)         v | No npf        = Var (fdecr y x npf) (insertAtFdecr npf pf)
subst x (App e1 e2)        v = App (subst x e1 v) (subst x e2 v)
subst x (Abs e)            v = Abs (subst (fincr x FZ) e (incr FZ v))
subst x Triv               v = Triv
subst x (Pair e1 e2)       v = Pair (subst x e1 v) (subst x e2 v)
subst x (Proj d e)         v = Proj d (subst x e v)
subst x (Abort e)          v = Abort (subst x e v)
subst x (Inj d e)          v = Inj d (subst x e v)
subst x (Case e el er)     v = Case (subst x e v) (subst (fincr x FZ) el (incr FZ v)) (subst (fincr x FZ) er (incr FZ v))
subst x (Map tv t pf e0 e) v = Map tv t pf (subst (fincr x FZ) e0 (incr FZ v)) (subst x e v)
subst x (Fold pf e)        v = Fold pf (subst x e v)
subst x (Rec pf e0 e)      v = Rec pf (subst (fincr x FZ) e0 (incr FZ v)) (subst x e v)
subst x (Unfold pf e)      v = Unfold pf (subst x e v)
subst x (Gen pf e0 e)      v = Gen pf (subst (fincr x FZ) e0 (incr FZ v)) (subst x e v)

data isVal {n tn : nat} {gam : vect (type tn) n} : {t : type tn} -> lam gam t -> Set where
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
  EvalRec2 : {t : type (Suc tn)} {t2 : type tn} {pf1 pf2 : postype FZ t} {e0 : lam (tsubst FZ t pf1 t2 :: gam) t2} {e2 : lam gam (tsubst FZ t pf2 (Ind t))} ->
    eval (Rec pf1 e0 (Fold pf2 e2)) (subst FZ e0 (Map FZ t {!!} (Rec pf1 (incr (FS FZ) e0) (Var FZ (Refl (Ind t)))) e2))
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
evaluate (Rec pf e0 (Fold pf2 e)) | InL FoldVal   = InR ({!!} , EvalRec2)
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
