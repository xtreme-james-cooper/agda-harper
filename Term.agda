module Term where

open import Basics
open import Fin
open import Vect
open import Type

data lam {n tn : nat} (gam : vect (type tn) n) : type tn -> bool -> Set
data rec {n tn : nat} (gam : vect (type tn) n) : {rn : nat} -> vect (type tn) rn -> bool -> Set
data pat {n tn : nat} (t : type tn) (gam : vect (type tn) n) : {pn : nat} -> vect (type tn) pn -> Set
data lam {n} {tn} gam where
  Var : {t : type tn} (x : fin n) -> (gam ! x) == t -> lam gam t False
  App : {t1 t2 : type tn} {b1 b2 : bool} -> lam gam (t1 => t2) b1 -> lam gam t1 b2 -> lam gam t2 False
  Abs : {t1 t2 : type tn} {b : bool} -> lam (t1 :: gam) t2 b -> lam gam (t1 => t2) True
  Let : {t1 t2 : type tn} {b1 b2 : bool} -> lam gam t1 b1 -> lam (t1 :: gam) t2 b2 -> lam gam t2 False
  Tuple : {rn : nat} {ts : vect (type tn) rn} {b : bool} -> rec gam ts b -> lam gam (Tuple ts) b
  Proj : {rn : nat} {ts : vect (type tn) rn} {b : bool} -> lam gam (Tuple ts) b -> (p : fin rn) -> lam gam (ts ! p) False
  Variant : {pn : nat} {ts : vect (type tn) pn} {b : bool} (l : fin pn) -> lam gam (ts ! l) b -> lam gam (Variant ts) b
  Case : {pn : nat} {t : type tn} {ts : vect (type tn) pn} {b : bool} -> lam gam (Variant ts) b -> pat t gam ts -> lam gam t False
  Fold : (t : type (Suc tn)) {t2 : type tn} {b : bool} -> lam gam t2 b -> tsubst FZ (Rec t) t == t2 -> lam gam (Rec t) b
  Unfold : (t : type (Suc tn)) {t2 : type tn} {b : bool} -> lam gam (Rec t) b -> tsubst FZ (Rec t) t == t2 -> lam gam t2 False
  TApp : {t1 : type (Suc tn)} {b : bool} -> lam gam (Forall t1) b -> (t2 : type tn) {t3 : type tn} -> tsubst FZ t2 t1 == t3 -> lam gam t3 False
  TAbs : {t : type (Suc tn)} {gam' : vect (type (Suc tn)) n} {b : bool} -> lam gam' t b -> map (tincr FZ) gam == gam' -> lam gam (Forall t) True
data rec {n} {tn} gam where
  Unit : rec gam [] True
  Field : {rn : nat} {t : type tn} {ts : vect (type tn) rn} {b1 b2 b3 : bool} -> lam gam t b1 -> rec gam ts b2 -> (b1 and b2) == b3 -> rec gam (t :: ts) b3
data pat {n} {tn} t gam where
  Fail : pat t gam []
  Match : {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} {b : bool} -> lam (t2 :: gam) t b -> pat t gam ts -> pat t gam (t2 :: ts)

teincr : {n tn : nat} {t : type tn} {gam : vect (type tn) n} {b : bool} (x : fin (Suc tn)) -> lam gam t b -> lam (map (tincr x) gam) (tincr x t) b
teincrRec : {n tn rn : nat} {ts : vect (type tn) rn} {gam : vect (type tn) n} {b : bool} (x : fin (Suc tn)) -> rec gam ts b -> rec (map (tincr x) gam) (tincrVect x ts) b
teincrPat : {n tn pn : nat} {t : type tn} {ts : vect (type tn) pn} {gam : vect (type tn) n} (x : fin (Suc tn)) -> pat t gam ts -> 
  pat (tincr x t) (map (tincr x) gam) (tincrVect x ts)
teincr {gam = gam} x (Var y Refl)            = Var y (mapLookup (tincr x) gam y)
teincr             x (App e1 e2)             = App (teincr x e1) (teincr x e2)
teincr             x (Abs e)                 = Abs (teincr x e)
teincr             x (Let e1 e2)             = Let (teincr x e1) (teincr x e2)
teincr             x (Tuple rec)             = Tuple (teincrRec x rec)
teincr             x (Proj {ts = ts} e p)    rewrite sym (tincrIdx x ts p) = Proj (teincr x e) p
teincr             x (Variant {ts = ts} l e) with teincr x e
teincr             x (Variant {ts = ts} l e) | e' rewrite sym (tincrIdx x ts l) = Variant l e'
teincr             x (Case e ps)             = Case (teincr x e) (teincrPat x ps)
teincr             x (Fold t {t2} e eq)      rewrite sym eq = Fold (tincr (FS x) t) (teincr x e) (tsubstIncr (Rec t) t x FZ >=FZ)
teincr             x (Unfold t {t2} e eq)    rewrite sym eq = Unfold (tincr (FS x) t) (teincr x e) (tsubstIncr (Rec t) t x FZ >=FZ)
teincr             x (TApp {t1} e t Refl)    = TApp (teincr x e) (tincr x t) (tsubstIncr t t1 x FZ >=FZ)
teincr {gam = gam} x (TAbs e Refl)           = TAbs (teincr (FS x) e) (teincrLemma x gam)
  where
    teincrLemma : {n tn : nat} (x : fin (Suc tn)) (gam : vect (type tn) n) -> map (tincr FZ) (map (tincr x) gam) == map (tincr (FS x)) (map (tincr FZ) gam)
    teincrLemma x []         = Refl
    teincrLemma x (t :: gam) rewrite tincrSwap t x FZ >=FZ | teincrLemma x gam = Refl 
teincrRec x Unit            = Unit
teincrRec x (Field e rs pf) = Field (teincr x e) (teincrRec x rs) pf
teincrPat x Fail         = Fail
teincrPat x (Match e ps) = Match (teincr x e) (teincrPat x ps)

tesubst : {n tn : nat} {t1 : type (Suc tn)} {gam : vect (type (Suc tn)) n} {b : bool} (x : fin (Suc tn)) (t2 : type tn) -> lam gam t1 b -> 
  lam (map (tsubst x t2) gam) (tsubst x t2 t1) b
tesubstRec : {n tn rn : nat} {ts : vect (type (Suc tn)) rn} {gam : vect (type (Suc tn)) n} {b : bool} (x : fin (Suc tn)) (t2 : type tn) -> rec gam ts b -> 
  rec (map (tsubst x t2) gam) (tsubstVect x t2 ts) b
tesubstPat : {n tn pn : nat} {t : type (Suc tn)} {ts : vect (type (Suc tn)) pn} {gam : vect (type (Suc tn)) n} (x : fin (Suc tn)) (t2 : type tn) -> pat t gam ts -> 
  pat (tsubst x t2 t) (map (tsubst x t2) gam) (tsubstVect x t2 ts)
tesubst {gam = gam} x t2 (Var y Refl)            = Var y (mapLookup (tsubst x t2) gam y)
tesubst             x t2 (App e1 e2)             = App (tesubst x t2 e1) (tesubst x t2 e2)
tesubst             x t2 (Abs e)                 = Abs (tesubst x t2 e)
tesubst             x t2 (Let e1 e2)             = Let (tesubst x t2 e1) (tesubst x t2 e2)
tesubst             x t2 (Tuple rec)             = Tuple (tesubstRec x t2 rec)
tesubst             x t2 (Proj {ts = ts} e p)    rewrite sym (tsubstIdx x t2 ts p) = Proj (tesubst x t2 e) p
tesubst             x t2 (Variant {ts = ts} l e) with (tesubst x t2 e)
tesubst             x t2 (Variant {ts = ts} l e) | e' rewrite sym (tsubstIdx x t2 ts l) = Variant l e'
tesubst             x t2 (Case e ps)             = Case (tesubst x t2 e) (tesubstPat x t2 ps)
tesubst             x t2 (Fold t e eq)           rewrite sym eq = Fold (tsubst (FS x) (tincr FZ t2) t) (tesubst x t2 e) (tsubstSwap t t2 (Rec t) x FZ >=FZ)
tesubst             x t2 (Unfold t e eq)         rewrite sym eq = Unfold (tsubst (FS x) (tincr FZ t2) t) (tesubst x t2 e) (tsubstSwap t t2 (Rec t) x FZ >=FZ)
tesubst {gam = gam} x t2 (TApp {t1} e t Refl)    = TApp (tesubst x t2 e) (tsubst x t2 t) (tsubstSwap t1 t2 t x FZ >=FZ)
tesubst {gam = gam} x t2 (TAbs {t} e Refl)       = TAbs (tesubst (FS x) (tincr FZ t2) e) (tesubstLemma x t2 gam)
  where
    tesubstLemma : {n tn : nat} (x : fin (Suc tn)) (t : type tn) (gam : vect (type (Suc tn)) n) -> 
      map (tincr FZ) (map (tsubst x t) gam) == map (tsubst (FS x) (tincr FZ t)) (map (tincr FZ) gam)
    tesubstLemma x t []          = Refl
    tesubstLemma x t (t1 :: gam) rewrite tesubstLemma x t gam | tincrSubst t t1 FZ x >=FZ = Refl
tesubstRec x t2 Unit            = Unit
tesubstRec x t2 (Field t ts pf) = Field (tesubst x t2 t) (tesubstRec x t2 ts) pf
tesubstPat x t2 Fail         = Fail
tesubstPat x t2 (Match t ts) = Match (tesubst x t2 t) (tesubstPat x t2 ts)

incr : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} {b : bool} (x : fin (Suc n)) -> lam gam t2 b -> lam (insertAt x gam t1) t2 b
incrRec : {n tn rn : nat} {gam : vect (type tn) n} {t : type tn} {ts : vect (type tn) rn} {b : bool} (x : fin (Suc n)) -> rec gam ts b -> rec (insertAt x gam t) ts b
incrPat : {n tn pn : nat} {gam : vect (type tn) n} {t t2 : type tn} {ts : vect (type tn) pn} (x : fin (Suc n)) -> pat t gam ts -> pat t (insertAt x gam t2) ts
incr {gam = gam} x (Var y Refl)    = Var (fincr x y) (insertAtFincr gam y x _)
incr             x (App e1 e2)     = App (incr x e1) (incr x e2)
incr             x (Abs e)         = Abs (incr (FS x) e)
incr             x (Let e1 e2)     = Let (incr x e1) (incr (FS x) e2)
incr             x (Tuple rec)     = Tuple (incrRec x rec)
incr             x (Proj e p)      = Proj (incr x e) p
incr             x (Variant l e)   = Variant l (incr x e)
incr             x (Case e ps)     = Case (incr x e) (incrPat x ps)
incr             x (Fold t e eq)   = Fold t (incr x e) eq
incr             x (Unfold t e eq) = Unfold t (incr x e) eq
incr             x (TApp e t pf)   = TApp (incr x e) t pf
incr {gam = gam} x (TAbs e Refl)   = TAbs (incr x e) (mapInsertAt gam _ (tincr FZ) x)
incrRec x Unit           = Unit
incrRec x (Field e r pf) = Field (incr x e) (incrRec x r) pf
incrPat x Fail         = Fail
incrPat x (Match e ps) = Match (incr (FS x) e) (incrPat x ps)

subst : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} {b : bool} (x : fin (Suc n)) -> 
  lam (insertAt x gam t1) t2 b -> lam gam t1 True -> bool * lam gam t2
substRec : {n tn rn : nat} {gam : vect (type tn) n} {t : type tn} {ts : vect (type tn) rn} {b : bool} (x : fin (Suc n)) -> 
  rec (insertAt x gam t) ts b -> lam gam t True -> bool * rec gam ts
substPat : {n tn pn : nat} {gam : vect (type tn) n} {t t2 : type tn} {ts : vect (type tn) pn} (x : fin (Suc n)) -> 
  pat t (insertAt x gam t2) ts -> lam gam t2 True -> pat t gam ts
subst                  x (Var y pf)      v with finEq y x
subst {gam = gam} {t1} x (Var .x Refl)   v | Yes Refl rewrite lookupInsertAt gam x t1 = _ , v
subst                  x (Var y pf)      v | No npf   = _ , Var (fdecr x y npf) (insertAtFdecr npf pf)
subst                  x (App e1 e2)     v with subst x e1 v | subst x e2 v
subst                  x (App e1 e2)     v | _ , e1' | _ , e2' = _ , App e1' e2'
subst                  x (Abs e)         v with subst (fincr FZ x) e (incr FZ v) 
subst                  x (Abs e)         v | _ , e' = _ , Abs e'
subst                  x (Let e1 e2)     v with subst x e1 v | subst (fincr FZ x) e2 (incr FZ v) 
subst                  x (Let e1 e2)     v | _ , e1' | _ , e2' = _ , Let e1' e2'
subst                  x (Tuple rec)     v with substRec x rec v 
subst                  x (Tuple rec)     v | _ , rec' = _ , Tuple rec'
subst                  x (Proj e p)      v with subst x e v 
subst                  x (Proj e p)      v | _ , e' = _ , Proj e' p
subst                  x (Variant l e)   v with subst x e v 
subst                  x (Variant l e)   v | _ , e' = _ , Variant l e'
subst                  x (Case e ps)     v with subst x e v 
subst                  x (Case e ps)     v | _ , e' = _ , Case e' (substPat x ps v)
subst                  x (Fold t e eq)   v with subst x e v 
subst                  x (Fold t e eq)   v | _ , e' = _ , Fold t e' eq
subst                  x (Unfold t e eq) v with subst x e v 
subst                  x (Unfold t e eq) v | _ , e' =  _ , Unfold t e' eq
subst                  x (TApp e t pf)   v with subst x e v 
subst                  x (TApp e t pf)   v | _ , e' = _ , TApp e' t pf
subst {gam = gam} {t1} x (TAbs e Refl)   v rewrite mapInsertAt gam t1 (tincr FZ) x with subst x e (teincr FZ v)
subst                  x (TAbs e Refl)   v | _ , e'  = _ , TAbs e' Refl
substRec x Unit           v = _ , Unit
substRec x (Field e r pf) v with subst x e v | substRec x r v
substRec x (Field e r pf) v | b1 , e' | b2 , rec' = (b1 and b2) , Field e' rec' Refl
substPat x Fail         v = Fail
substPat x (Match e ps) v with subst (fincr FZ x) e (incr FZ v) 
substPat x (Match e ps) v | _ , e' = Match e' (substPat x ps v)

-- abbreviations

unitE : {n tn : nat} {gam : vect (type tn) n} -> lam gam unitT True
unitE = Tuple Unit

abortE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} {b : bool} -> lam gam voidT b -> lam gam t False
abortE e = Case e Fail

zeroE : {n tn : nat} {gam : vect (type tn) n} -> lam gam natT True
zeroE = Fold natT' (Variant FZ unitE) Refl

succE : {n tn : nat} {gam : vect (type tn) n} {b : bool} -> lam gam natT b -> lam gam natT b
succE e = Fold natT' (Variant (FS FZ) e) Refl

natcaseE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} {b1 b2 b3 : bool} -> lam gam natT b1 -> lam gam t b2 -> lam (natT :: gam) t b3 -> lam gam t False
natcaseE e e0 es = Case (Unfold natT' e Refl) (Match (incr FZ e0) (Match es Fail))

nilE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} -> lam gam (listT t) True
nilE {t = t} = Fold (listT' t) (Variant FZ unitE) Refl

listTLemma : {tn : nat} (t : type tn) -> tsubst FZ (listT t) (tincr FZ t) == t
listTLemma t = tsubstIncrCollapse FZ t (listT t)

consE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} {b1 b2 : bool} -> lam gam t b1 -> lam gam (listT t) b2 -> lam gam (listT t) (b1 and b2)
consE {n} {tn} {gam} {t} {b1} a as rewrite listTLemma t = Fold (listT' t) (Variant (FS FZ) (Tuple (Field a' (Field as Unit andTrue) Refl))) Refl
  where
    a' : lam gam (tsubst FZ (listT t) (tincr FZ t)) b1
    a' rewrite listTLemma t = a

listcaseE : {n tn : nat} {gam : vect (type tn) n} {a t : type tn} {b1 b2 b3 : bool} -> lam gam (listT a) b1 -> lam gam t b2 -> lam (listT a :: (a :: gam)) t b3 -> 
  lam gam t False
listcaseE {n} {tn} {gam} {a} {t} e en ec = 
  Case (Unfold (listT' a) e Refl) (Match (incr FZ en) (Match (App (App (incr FZ (Abs (Abs ec))) (Proj (Var FZ eq) FZ)) (Proj (Var FZ Refl) (FS FZ))) Fail))
  where
    eq : Tuple (tsubst FZ (listT a) (tincr FZ a) :: (listT a :: [])) == Tuple (a :: (listT a :: []))
    eq = funEq (λ x -> Tuple (x :: (listT a :: []))) (listTLemma a)
