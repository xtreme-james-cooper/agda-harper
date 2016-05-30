module Term where

open import Basics
open import Fin
open import Vect
open import Type
open import RawTerm

data lam {n tn : nat} (gam : vect (type tn) n) : {b : bool} -> rawlam n b -> type tn -> Set
data rec {n tn : nat} (gam : vect (type tn) n) : {b : bool} -> rawrec n b -> {rn : nat} -> vect (type tn) rn -> Set
data pat {n tn : nat} (t : type tn) (gam : vect (type tn) n) : rawpat n -> {pn : nat} -> vect (type tn) pn -> Set
data lam {n} {tn} gam where
  Var : {t : type tn} (x : fin n) -> (gam ! x) == t -> lam gam (Var x) t
  App : {t1 t2 : type tn} {b1 b2 : bool} {r1 : rawlam n b1} {r2 : rawlam n b2} -> lam gam r1 (t1 => t2) -> lam gam r2 t1 -> lam gam (App r1 r2) t2
  Abs : {t1 t2 : type tn} {b : bool} {r : rawlam (Suc n) b} -> lam (t1 :: gam) r t2 -> lam gam (Abs r) (t1 => t2)
  Let : {t1 t2 : type tn} {b1 b2 : bool} {r1 : rawlam n b1} {r2 : rawlam (Suc n) b2} -> lam gam r1 t1 -> lam (t1 :: gam) r2 t2 -> lam gam (Let r1 r2) t2
  Tuple : {rn : nat} {ts : vect (type tn) rn} {b : bool} {r : rawrec n b} -> rec gam r ts -> lam gam (Tuple r) (Tuple ts)
  Proj : {rn : nat} {ts : vect (type tn) rn} {b : bool} {r : rawlam n b} -> lam gam r (Tuple ts) -> (p : fin rn) -> lam gam (Proj r (naturalize p)) (ts ! p)
  Variant : {pn : nat} {ts : vect (type tn) pn} {b : bool} {r : rawlam n b} (l : fin pn) -> lam gam r (ts ! l) -> lam gam (Variant (naturalize l) r) (Variant ts)
  Case : {pn : nat} {t : type tn} {ts : vect (type tn) pn} {b : bool} {r : rawlam n b} {rp : rawpat n} -> 
    lam gam r (Variant ts) -> pat t gam rp ts -> lam gam (Case r rp) t
  Fold : (t : type (Suc tn)) {t2 : type tn} {b : bool} {r : rawlam n b} -> lam gam r t2 -> tsubst FZ (Rec t) t == t2 -> lam gam (Fold r) (Rec t)
  Unfold : (t : type (Suc tn)) {t2 : type tn} {b : bool} {r : rawlam n b} -> lam gam r (Rec t) -> tsubst FZ (Rec t) t == t2 -> lam gam (Unfold r) t2
data rec {n} {tn} gam where
  Unit : rec gam Unit []
  Field : {rn : nat} {t : type tn} {ts : vect (type tn) rn} {b1 b2 b3 : bool} {r : rawlam n b1} {rr : rawrec n b2} -> 
    lam gam r t -> rec gam rr ts -> (pf : (b1 and b2) == b3) -> rec gam (Field r rr pf) (t :: ts)
data pat {n} {tn} t gam where
  Fail : pat t gam Fail []
  Match : {pn : nat} {t2 : type tn} {ts : vect (type tn) pn} {b : bool} {r : rawlam (Suc n) b} {rp : rawpat n} -> 
    lam (t2 :: gam) r t -> pat t gam rp ts -> pat t gam (Match r rp) (t2 :: ts)

teincr : {n tn : nat} {t : type tn} {gam : vect (type tn) n} {b : bool} {r : rawlam n b} (x : fin (Suc tn)) -> lam gam r t -> lam (map (tincr x) gam) r (tincr x t)
teincrRec : {n tn rn : nat} {ts : vect (type tn) rn} {gam : vect (type tn) n} {b : bool} {r : rawrec n b} (x : fin (Suc tn)) -> rec gam r ts -> 
  rec (map (tincr x) gam) r (tincrVect x ts)
teincrPat : {n tn pn : nat} {t : type tn} {ts : vect (type tn) pn} {gam : vect (type tn) n} {r : rawpat n} (x : fin (Suc tn)) -> pat t gam r ts -> 
  pat (tincr x t) (map (tincr x) gam) r (tincrVect x ts)
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
teincrRec x Unit            = Unit
teincrRec x (Field e rs pf) = Field (teincr x e) (teincrRec x rs) pf
teincrPat x Fail         = Fail
teincrPat x (Match e ps) = Match (teincr x e) (teincrPat x ps)

tesubst : {n tn : nat} {t1 : type (Suc tn)} {gam : vect (type (Suc tn)) n} {b : bool} {r : rawlam n b} (x : fin (Suc tn)) (t2 : type tn) -> lam gam r t1 -> 
  lam (map (tsubst x t2) gam) r (tsubst x t2 t1)
tesubstRec : {n tn rn : nat} {ts : vect (type (Suc tn)) rn} {gam : vect (type (Suc tn)) n} {b : bool} {r : rawrec n b} 
  (x : fin (Suc tn)) (t2 : type tn) -> rec gam r ts -> rec (map (tsubst x t2) gam) r (tsubstVect x t2 ts)
tesubstPat : {n tn pn : nat} {t : type (Suc tn)} {ts : vect (type (Suc tn)) pn} {gam : vect (type (Suc tn)) n} {r : rawpat n} 
  (x : fin (Suc tn)) (t2 : type tn) -> pat t gam r ts -> pat (tsubst x t2 t) (map (tsubst x t2) gam) r (tsubstVect x t2 ts)
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
tesubstRec x t2 Unit            = Unit
tesubstRec x t2 (Field t ts pf) = Field (tesubst x t2 t) (tesubstRec x t2 ts) pf
tesubstPat x t2 Fail         = Fail
tesubstPat x t2 (Match t ts) = Match (tesubst x t2 t) (tesubstPat x t2 ts)

incr : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} {b : bool} {r : rawlam n b} (x : fin (Suc n)) -> lam gam r t2 -> lam (insertAt x gam t1) (rawincr x r) t2 
incrRec : {n tn rn : nat} {gam : vect (type tn) n} {t : type tn} {ts : vect (type tn) rn} {b : bool} {r : rawrec n b} (x : fin (Suc n)) -> 
  rec gam r ts -> rec (insertAt x gam t) (rawincrRec x r) ts
incrPat : {n tn pn : nat} {gam : vect (type tn) n} {t t2 : type tn} {ts : vect (type tn) pn} {r : rawpat n} (x : fin (Suc n)) -> 
  pat t gam r ts -> pat t (insertAt x gam t2) (rawincrPat x r) ts
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
incrRec x Unit           = Unit
incrRec x (Field e r pf) = Field (incr x e) (incrRec x r) pf
incrPat x Fail         = Fail
incrPat x (Match e ps) = Match (incr (FS x) e) (incrPat x ps)

subst : {n tn : nat} {gam : vect (type tn) n} {t1 t2 : type tn} {b1 b2 : bool} {r : rawlam (Suc n) b1} {rv : rawlam n b2} (x : fin (Suc n)) -> 
  lam (insertAt x gam t1) r t2 -> lam gam rv t1 -> bool * (λ b -> rawlam n b * (λ r' -> (rawsubst x r rv == (b , r')) × lam gam r' t2))
substRec : {n tn rn : nat} {gam : vect (type tn) n} {t : type tn} {ts : vect (type tn) rn} {b1 b2 : bool} {r : rawrec (Suc n) b1} {rv : rawlam n b2} (x : fin (Suc n)) -> 
  rec (insertAt x gam t) r ts -> lam gam rv t -> bool * (λ b -> rawrec n b * (λ r' -> (rawsubstRec x r rv == (b , r')) × rec gam r' ts))
substPat : {n tn pn : nat} {gam : vect (type tn) n} {t t2 : type tn} {ts : vect (type tn) pn} {b : bool} {r : rawpat (Suc n)} {rv : rawlam n b} (x : fin (Suc n)) -> 
  pat t (insertAt x gam t2) r ts -> lam gam rv t2 -> pat t gam (rawsubstPat x r rv) ts
subst                  x (Var y Refl)    v with finEq y x
subst {gam = gam} {t1} x (Var .x Refl)   v | Yes Refl rewrite lookupInsertAt gam x t1 = _ , (_ , (Refl , v))
subst {gam = gam} {t1} x (Var y Refl)    v | No npf   = _ , (_ , (Refl , Var (fdecr x y npf) (sym (lookupInsertAtNeq gam x y t1 npf))))
subst                  x (App e1 e2)     v with subst x e1 v | subst x e2 v
subst                  x (App e1 e2)     v | _ , (_ , (eq1 , e1')) | _ , (_ , (eq2 , e2')) rewrite eq1 | eq2 = _ , (_ , (Refl , App e1' e2'))
subst                  x (Abs e)         v with subst (fincr FZ x) e (incr FZ v) 
subst                  x (Abs e)         v | _ , (_ , (eq , e')) rewrite eq = _ , (_ , (Refl , Abs e'))
subst                  x (Let e1 e2)     v with subst x e1 v | subst (fincr FZ x) e2 (incr FZ v) 
subst                  x (Let e1 e2)     v | _ , (_ , (eq1 , e1')) | _ , (_ , (eq2 , e2')) rewrite eq1 | eq2 = _ , (_ , (Refl , Let e1' e2'))
subst                  x (Tuple rec)     v with substRec x rec v 
subst                  x (Tuple rec)     v | _ , (_ , (eq , rec')) rewrite eq = _ , (_ , (Refl , Tuple rec'))
subst                  x (Proj e p)      v with subst x e v 
subst                  x (Proj e p)      v | _ , (_ , (eq , e')) rewrite eq = _ , (_ , (Refl , Proj e' p))
subst                  x (Variant l e)   v with subst x e v 
subst                  x (Variant l e)   v | _ , (_ , (eq , e')) rewrite eq = _ , (_ , (Refl , Variant l e'))
subst                  x (Case e ps)     v with subst x e v 
subst                  x (Case e ps)     v | _ , (_ , (eq , e')) rewrite eq = _ , (_ , (Refl , Case e' (substPat x ps v)))
subst                  x (Fold t e eq)   v with subst x e v 
subst                  x (Fold t e eq)   v | _ , (_ , (eq' , e')) rewrite eq' = _ , (_ , (Refl , Fold t e' eq))
subst                  x (Unfold t e eq) v with subst x e v 
subst                  x (Unfold t e eq) v | _ , (_ , (eq' , e')) rewrite eq' = _ , (_ , (Refl , Unfold t e' eq))
substRec x Unit           v = _ , (_ , (Refl , Unit))
substRec x (Field e r pf) v with subst x e v | substRec x r v
substRec x (Field e r pf) v | b1 , (_ , (eq1 , e')) | b2 , (_ , (eq2 , rec')) rewrite eq1 | eq2 = _ , (_ , (Refl , Field e' rec' Refl))
substPat x Fail         v = Fail
substPat x (Match e ps) v with subst (fincr FZ x) e (incr FZ v) 
substPat x (Match e ps) v | _ , (_ , (eq , e')) rewrite eq = Match e' (substPat x ps v)

-- abbreviations

unitE : {n tn : nat} {gam : vect (type tn) n} -> lam gam rawunitE unitT
unitE = Tuple Unit

abortE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} {b : bool} {r : rawlam n b} -> lam gam r voidT -> lam gam (rawabortE r) t
abortE e = Case e Fail

zeroE : {n tn : nat} {gam : vect (type tn) n} -> lam gam rawzeroE natT
zeroE = Fold natT' (Variant FZ unitE) Refl

succE : {n tn : nat} {gam : vect (type tn) n} {b : bool} {r : rawlam n b} -> lam gam r natT -> lam gam (rawsuccE r) natT
succE e = Fold natT' (Variant (FS FZ) e) Refl

natcaseE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} {b1 b2 b3 : bool} {r1 : rawlam n b1} {r2 : rawlam n b2} {r3 : rawlam (Suc n) b3} -> 
  lam gam r1 natT -> lam gam r2 t -> lam (natT :: gam) r3 t -> lam gam (rawnatcaseE r1 r2 r3) t
natcaseE e e0 es = Case (Unfold natT' e Refl) (Match (incr FZ e0) (Match es Fail))

nilE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} -> lam gam rawnilE (listT t)
nilE {t = t} = Fold (listT' t) (Variant FZ unitE) Refl

listTLemma : {tn : nat} (t : type tn) -> tsubst FZ (listT t) (tincr FZ t) == t
listTLemma t = tsubstIncrCollapse FZ t (listT t)

consE : {n tn : nat} {gam : vect (type tn) n} {t : type tn} {b1 b2 : bool} {r1 : rawlam n b1} {r2 : rawlam n b2} -> 
  lam gam r1 t -> lam gam r2 (listT t) -> lam gam (rawconsE r1 r2) (listT t)
consE {n} {tn} {gam} {t} {b1} {b2} {r1} a as rewrite listTLemma t = Fold (listT' t) (Variant (FS FZ) (Tuple (Field a' (Field as Unit Refl) Refl))) Refl
  where
    a' : lam gam r1 (tsubst FZ (listT t) (tincr FZ t))
    a' rewrite listTLemma t = a

listcaseE : {n tn : nat} {gam : vect (type tn) n} {a t : type tn} {b1 b2 b3 : bool} {r1 : rawlam n b1} {r2 : rawlam n b2} {r3 : rawlam (Suc (Suc n)) b3} -> 
  lam gam r1 (listT a) -> lam gam r2 t -> lam (listT a :: (a :: gam)) r3 t -> lam gam (rawlistcaseE r1 r2 r3) t
listcaseE {n} {tn} {gam} {a} {t} e en ec = 
  Case (Unfold (listT' a) e Refl) (Match (incr FZ en) (Match (App (App (incr FZ (Abs (Abs ec))) (Proj (Var FZ eq) FZ)) (Proj (Var FZ Refl) (FS FZ))) Fail))
  where
    eq : Tuple (tsubst FZ (listT a) (tincr FZ a) :: (listT a :: [])) == Tuple (a :: (listT a :: []))
    eq = funEq (λ x -> Tuple (x :: (listT a :: []))) (listTLemma a)
