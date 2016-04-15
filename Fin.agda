module Fin where

open import Basics


data fin : nat -> Set where
  FZ : {n : nat} -> fin (Suc n)
  FS : {n : nat} -> fin n -> fin (Suc n)

eqFSBackwards : {n : nat} {x y : fin n} -> FS x == FS y -> x == y
eqFSBackwards {n} {x} {.x} Refl = Refl

neqFSBackwards : {n : nat} {x y : fin n} -> not (FS x == FS y) -> not (x == y)
neqFSBackwards {n} {x} {.x} npf Refl = npf Refl

finEq : {n : nat} (x y : fin n) -> equals? x y
finEq FZ FZ          = Yes Refl
finEq FZ (FS y)      = No (λ ())
finEq (FS x) FZ      = No (λ ())
finEq (FS x) (FS y)  with finEq x y
finEq (FS x) (FS .x) | Yes Refl = Yes Refl
finEq (FS x) (FS y)  | No npf   = No (neqFS npf)
  where
    neqFS : {n : nat} {x y : fin n} -> not (x == y) -> not (FS x == FS y)
    neqFS npf Refl = npf Refl

data finNeq : {n : nat} -> fin n -> fin n -> Set where
  ZNeqS : {n : nat} {f : fin n} -> finNeq FZ (FS f)
  SNeqZ : {n : nat} {f : fin n} -> finNeq (FS f) FZ
  SNeqS : {n : nat} {f g : fin n} -> finNeq f g -> finNeq (FS f) (FS g)

finNeqIden : {n : nat} {x y : fin n} (pf1 pf2 : finNeq x y) -> pf1 == pf2
finNeqIden ZNeqS       ZNeqS        = Refl
finNeqIden SNeqZ       SNeqZ        = Refl
finNeqIden (SNeqS pf1) (SNeqS pf2)  with finNeqIden pf1 pf2
finNeqIden (SNeqS pf1) (SNeqS .pf1) | Refl = Refl

neqToNeq : {n : nat} {x y : fin n} -> finNeq x y -> not (x == y)
neqToNeq ZNeqS       ()
neqToNeq SNeqZ       ()
neqToNeq (SNeqS neq) Refl = neqToNeq neq Refl

neqToNeq' : {n : nat} {x y : fin n} -> not (x == y) -> finNeq x y
neqToNeq' {Suc n} {FZ}   {FZ}   npf with npf Refl
neqToNeq' {Suc n} {FZ}   {FZ}   npf | ()
neqToNeq' {Suc n} {FZ}   {FS y} npf = ZNeqS
neqToNeq' {Suc n} {FS x} {FZ}   npf = SNeqZ
neqToNeq' {Suc n} {FS x} {FS y} npf with neqToNeq' (neqFSBackwards npf)
neqToNeq' {Suc n} {FS x} {FS y} npf | pf = SNeqS pf

weaken : {n : nat} -> fin n -> fin (Suc n)
weaken FZ = FZ
weaken (FS x) = FS (weaken x)

weakenEq : {n : nat} {x y : fin n} -> weaken x == weaken y -> x == y
weakenEq {Suc n} {FZ}   {FZ}   pf = Refl
weakenEq {Suc n} {FZ}   {FS y} ()
weakenEq {Suc n} {FS x} {FZ}   ()
weakenEq {Suc n} {FS x} {FS y} pf rewrite weakenEq {n} {x} {y} (eqFSBackwards pf) = Refl

fincr : {n : nat} -> fin n -> fin (Suc n) -> fin (Suc n)
fincr x      FZ     = FS x
fincr FZ     (FS y) = FZ
fincr (FS x) (FS y) = FS (fincr x y)

fdecr : {n : nat} (x y : fin (Suc n)) -> not (x == y) -> fin n
fdecr {n}     FZ      FZ      npf with npf Refl
fdecr {n}     FZ      FZ      npf | ()
fdecr {Zero}  FZ      (FS ()) npf
fdecr {Zero}  (FS ()) y       npf
fdecr {Suc n} FZ      (FS y)  npf = FZ
fdecr {Suc n} (FS x)  FZ      npf = x
fdecr {Suc n} (FS x)  (FS y)  npf = FS (fdecr x y (neqFSBackwards npf))

data _>=F_ : {n : nat} -> fin n -> fin n -> Set where
  Z>=Z : {n : nat} -> FZ {n} >=F FZ
  S>=Z : {n : nat} {x : fin n} -> FS x >=F FZ
  S>=S : {n : nat} {x y : fin n} -> x >=F y -> FS x >=F FS y

>=FRefl : {n : nat} {x : fin n} -> x >=F x
>=FRefl {Suc n} {FZ}   = Z>=Z
>=FRefl {Suc n} {FS x} = S>=S >=FRefl

>=FZ : {n : nat} {x : fin (Suc n)} -> x >=F FZ
>=FZ {n} {FZ}   = Z>=Z
>=FZ {n} {FS x} = S>=Z

finComp : {n : nat} (x y : fin n) -> decide (x >=F y)
finComp FZ     FZ     = Yes Z>=Z
finComp FZ     (FS y) = No (λ ())
finComp (FS x) FZ     = Yes S>=Z
finComp (FS x) (FS y) with finComp x y 
finComp (FS x) (FS y) | Yes gt = Yes (S>=S gt)
finComp (FS x) (FS y) | No ngt = No (λ { (S>=S gt) -> ngt gt })

finTric : {n : nat} (x y : fin n) -> not (x >=F y) -> not (y == x) -> y >=F x
finTric FZ     FZ     ngt neq with neq Refl
finTric FZ     FZ     ngt neq | ()
finTric FZ     (FS y) ngt neq = S>=Z
finTric (FS x) FZ     ngt neq with ngt S>=Z
finTric (FS x) FZ     ngt neq | ()
finTric (FS x) (FS y) ngt neq with finTric x y (λ gt -> ngt (S>=S gt)) (neqFSBackwards neq)
finTric (FS x) (FS y) ngt neq | lt = S>=S lt

fgtTrans : {n : nat} (x y z : fin n) -> x >=F y -> y >=F z -> x >=F z
fgtTrans x      FZ     FZ     gt1        Z>=Z       = gt1
fgtTrans (FS x) (FS y) FZ     (S>=S gt1) S>=Z       = S>=Z
fgtTrans (FS x) (FS y) (FS z) (S>=S gt1) (S>=S gt2) = S>=S (fgtTrans x y z gt1 gt2)

fincrFdecrSwap : {tn : nat} (x y z : fin (Suc tn)) (neq : not (fincr z (FS x) == weaken y)) (neq2 : not (z == y)) -> x >=F y -> 
  fdecr (fincr z (FS x)) (weaken y) neq == fincr (fdecr z y neq2) x
fincrFdecrSwap {tn}     x       FZ      FZ      neq neq2 gt with neq Refl
fincrFdecrSwap {tn}     x       FZ      FZ      neq neq2 gt | ()
fincrFdecrSwap {tn}     FZ      (FS y)  FZ      neq neq2 ()
fincrFdecrSwap {Zero}   (FS x)  (FS ()) FZ      neq neq2 gt
fincrFdecrSwap {Suc tn} (FS x)  (FS y)  FZ      neq neq2 gt = Refl
fincrFdecrSwap {Zero}   x       FZ      (FS ()) neq neq2 gt
fincrFdecrSwap {Suc tn} x       FZ      (FS z)  neq neq2 gt = Refl
fincrFdecrSwap {tn}     FZ      (FS y)  (FS z)  neq neq2 ()
fincrFdecrSwap {Zero}   (FS ()) (FS y)  (FS z)  neq neq2 gt
fincrFdecrSwap {Suc tn} (FS x)  (FS y)  (FS z)  neq neq2 (S>=S gt) rewrite fincrFdecrSwap x y z (neqFSBackwards neq) (neqFSBackwards neq2) gt = Refl

fincrSwap : {tn : nat} (t : fin tn) (x y : fin (Suc tn)) -> x >=F y -> fincr (fincr t x) (weaken y) == fincr (fincr t y) (FS x)
fincrSwap t      FZ     FZ     gt        = Refl
fincrSwap t      FZ     (FS y) ()
fincrSwap t      (FS x) FZ     gt        = Refl
fincrSwap FZ     (FS x) (FS y) (S>=S gt) = Refl
fincrSwap (FS t) (FS x) (FS y) (S>=S gt) rewrite fincrSwap t x y gt = Refl
 
fincrAbove : {n : nat} (x y : fin n) -> x >=F y -> fincr y (FS x) == weaken y
fincrAbove FZ     FZ     Z>=Z      = Refl
fincrAbove (FS x) FZ     S>=Z      = Refl
fincrAbove (FS x) (FS y) (S>=S gt) rewrite fincrAbove x y gt = Refl

fincrBelow : {n : nat} (x y : fin n) -> y >=F x -> not (y == x) -> fincr y (FS x) == FS y
fincrBelow FZ     FZ     Z>=Z      neq with neq Refl
fincrBelow FZ     FZ     Z>=Z      neq | ()
fincrBelow FZ     (FS y) S>=Z      neq = Refl
fincrBelow (FS x) (FS y) (S>=S gt) neq rewrite fincrBelow x y gt (neqFSBackwards neq) = Refl

