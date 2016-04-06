module LambdaType where

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