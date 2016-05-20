module Term where

open import Basics
open import Fin
open import Vect
open import Type

data lam {n tn : nat} (gam : vect (type tn) n) : type tn -> Set
data rec {n tn : nat} (gam : vect (type tn) n) : {rn : nat} -> vect (type tn) rn -> Set
data pat {n tn : nat} (t : type tn) (gam : vect (type tn) n) : {pn : nat} -> vect (type tn) pn -> Set
data lam {n} {tn} gam where
  Var : {t : type tn} (x : fin n) -> (gam ! x) == t -> lam gam t
  App : {t1 t2 : type tn} -> lam gam (t1 => t2) -> lam gam t1 -> lam gam t2
  Abs : {t1 t2 : type tn} -> lam (t1 :: gam) t2 -> lam gam (t1 => t2)
  Let : {t1 t2 : type tn} -> lam gam t1 -> lam (t1 :: gam) t2 -> lam gam t2
  Tuple : {rn : nat} {ts : vect (type tn) rn} -> rec gam ts -> lam gam (Tuple ts)
  Proj : {rn : nat} {ts : vect (type tn) rn} -> lam gam (Tuple ts) -> (p : fin rn) -> lam gam (ts ! p)
  Variant : {pn : nat} {ts : vect (type tn) pn} (l : fin pn) -> lam gam (ts ! l) -> lam gam (Variant ts)
  Case : {pn : nat} {t : type tn} {ts : vect (type tn) pn} -> lam gam (Variant ts) -> pat t gam ts -> lam gam t
  Fold : (t : type (Suc tn)) {t2 : type tn} -> lam gam t2 -> tsubst FZ (Rec t) t == t2 -> lam gam (Rec t)
  Unfold : (t : type (Suc tn)) {t2 : type tn} -> lam gam (Rec t) -> tsubst FZ (Rec t) t == t2 -> lam gam t2
  TApp : {t1 : type (Suc tn)} -> lam gam (Forall t1) -> (t2 : type tn) {t3 : type tn} -> tsubst FZ t2 t1 == t3 -> lam gam t3
  TAbs : {t : type (Suc tn)} {gam' : vect (type (Suc tn)) n} -> lam gam' t -> map (tincr FZ) gam == gam' -> lam gam (Forall t)
data rec {n} {tn} gam where
  Unit : rec gam []
  Field : {rn : nat} {t : type tn} {ts : vect (type tn) rn} -> lam gam t -> rec gam ts -> rec gam (t :: ts)
data pat {n} {tn} t gam where
  Fail : pat t gam []
  Match : {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} -> lam (t2 :: gam) t -> pat t gam ts -> pat t gam (t2 :: ts)

teincr : {n tn : nat} {t : type tn} {gam : vect (type tn) n} (x : fin (Suc tn)) -> lam gam t -> lam (map (tincr x) gam) (tincr x t)
teincrRec : {n tn rn : nat} {ts : vect (type tn) rn} {gam : vect (type tn) n} (x : fin (Suc tn)) -> rec gam ts -> rec (map (tincr x) gam) (tincrVect x ts)
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
teincrRec x Unit         = Unit
teincrRec x (Field e rs) = Field (teincr x e) (teincrRec x rs)
teincrPat x Fail         = Fail
teincrPat x (Match e ps) = Match (teincr x e) (teincrPat x ps)

tesubst : {n tn : nat} {t1 : type (Suc tn)} {gam : vect (type (Suc tn)) n} (x : fin (Suc tn)) (t2 : type tn) -> lam gam t1 -> 
  lam (map (tsubst x t2) gam) (tsubst x t2 t1)
tesubstRec : {n tn rn : nat} {ts : vect (type (Suc tn)) rn} {gam : vect (type (Suc tn)) n} (x : fin (Suc tn)) (t2 : type tn) -> rec gam ts -> 
  rec (map (tsubst x t2) gam) (tsubstVect x t2 ts)
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
tesubstRec x t2 Unit         = Unit
tesubstRec x t2 (Field t ts) = Field (tesubst x t2 t) (tesubstRec x t2 ts)
tesubstPat x t2 Fail         = Fail
tesubstPat x t2 (Match t ts) = Match (tesubst x t2 t) (tesubstPat x t2 ts)

incr : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam gam t2 -> lam (insertAt x gam t1) t2
incrRec : {n tn rn : nat} {gam : vect (type tn) n} {t : type tn} {ts : vect (type tn) rn} (x : fin (Suc n)) -> rec gam ts -> rec (insertAt x gam t) ts
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
incrRec x Unit        = Unit
incrRec x (Field e r) = Field (incr x e) (incrRec x r)
incrPat x Fail         = Fail
incrPat x (Match e ps) = Match (incr (FS x) e) (incrPat x ps)

subst : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} (x : fin (Suc n)) -> lam (insertAt x gam t1) t2 -> lam gam t1 -> lam gam t2
substRec : {n tn rn : nat} {gam : vect (type tn) n} {t : type tn} {ts : vect (type tn) rn} (x : fin (Suc n)) -> rec (insertAt x gam t) ts -> lam gam t -> rec gam ts
substPat : {n tn pn : nat} {gam : vect (type tn) n} {t t2 : type tn} {ts : vect (type tn) pn} (x : fin (Suc n)) -> pat t (insertAt x gam t2) ts -> lam gam t2 -> pat t gam ts
subst                       x (Var y pf)      v with finEq y x
subst {gam = gam} {t1 = t1} x (Var .x Refl)   v | Yes Refl rewrite lookupInsertAt gam x t1 = v
subst                       x (Var y pf)      v | No npf   = Var (fdecr x y npf) (insertAtFdecr npf pf)
subst                       x (App e1 e2)     v = App (subst x e1 v) (subst x e2 v)
subst                       x (Abs e)         v = Abs (subst (fincr FZ x) e (incr FZ v))
subst                       x (Let e1 e2)     v = Let (subst x e1 v) (subst (fincr FZ x) e2 (incr FZ v))
subst                       x (Tuple rec)     v = Tuple (substRec x rec v)
subst                       x (Proj e p)      v = Proj (subst x e v) p
subst                       x (Variant l e)   v = Variant l (subst x e v)
subst                       x (Case e ps)     v = Case (subst x e v) (substPat x ps v)
subst                       x (Fold t e eq)   v = Fold t (subst x e v) eq
subst                       x (Unfold t e eq) v = Unfold t (subst x e v) eq
subst                       x (TApp e t pf) v = TApp (subst x e v) t pf
subst {n} {tn} {gam} {t1}   x (TAbs {t} {.(map (tincr FZ) (insertAt x gam t1))} e Refl) v rewrite mapInsertAt gam t1 (tincr FZ) x = 
  TAbs (subst {gam = map (tincr FZ) gam} {tincr FZ t1} x e (teincr FZ v)) Refl
substRec x Unit        v = Unit
substRec x (Field e r) v = Field (subst x e v) (substRec x r v)
substPat x Fail         v = Fail
substPat x (Match e ps) v = Match (subst (fincr FZ x) e (incr FZ v)) (substPat x ps v)

-- abbreviations

unitE : {n tn : nat} {gam : vect (type tn) n} -> lam gam unitT
unitE = Tuple Unit

abortE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} -> lam gam voidT -> lam gam t
abortE e = Case e Fail

zeroE : {n tn : nat} {gam : vect (type tn) n} -> lam gam natT
zeroE = Fold natT' (Variant FZ unitE) Refl

succE : {n tn : nat} {gam : vect (type tn) n} -> lam gam natT -> lam gam natT
succE e = Fold natT' (Variant (FS FZ) e) Refl

natcaseE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} -> lam gam natT -> lam gam t -> lam (natT :: gam) t -> lam gam t
natcaseE e e0 es = Case (Unfold natT' e Refl) (Match (incr FZ e0) (Match es Fail))

nilE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} -> lam gam (listT t)
nilE {t = t} = Fold (listT' t) (Variant FZ unitE) Refl

listTLemma : {tn : nat} (t : type tn) -> tsubst FZ (listT t) (tincr FZ t) == t
listTLemma t = tsubstIncrCollapse FZ t (listT t)

consE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} -> lam gam t -> lam gam (listT t) -> lam gam (listT t)
consE {n} {tn} {gam} {t} a as rewrite listTLemma t = Fold (listT' t) (Variant (FS FZ) (Tuple (Field a' (Field as Unit)))) Refl
  where
    a' : lam gam (tsubst FZ (listT t) (tincr FZ t))
    a' rewrite listTLemma t = a

listcaseE : {n tn : nat} {gam : vect (type tn) n} {a t : type tn} -> lam gam (listT a) -> lam gam t -> lam (listT a :: (a :: gam)) t -> lam gam t
listcaseE {n} {tn} {gam} {a} {t} e en ec = 
  Case (Unfold (listT' a) e Refl) (Match (incr FZ en) (Match (App (App (incr FZ (Abs (Abs ec))) (Proj (Var FZ eq) FZ)) (Proj (Var FZ Refl) (FS FZ))) Fail))
  where
    eq : Tuple (tsubst FZ (listT a) (tincr FZ a) :: (listT a :: [])) == Tuple (a :: (listT a :: []))
    eq = funEq (λ x -> Tuple (x :: (listT a :: []))) (listTLemma a)
