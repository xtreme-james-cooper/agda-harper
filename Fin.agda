module Fin where

open import Basics

data fin : nat -> Set where
  FZ : {n : nat} -> fin (Suc n)
  FS : {n : nat} -> fin n -> fin (Suc n)

eqFSBackwards : {n : nat} {x y : fin n} -> FS x == FS y -> x == y
eqFSBackwards {n} {x} {.x} Refl = Refl

neqFSBackwards : {n : nat} {x y : fin n} -> not (FS x == FS y) -> not (x == y)
neqFSBackwards {n} {x} {.x} npf Refl = npf Refl

neqFS : {n : nat} {x y : fin n} -> not (x == y) -> not (FS x == FS y)
neqFS npf Refl = npf Refl

finEq : {n : nat} (x y : fin n) -> equals? x y
finEq FZ FZ          = Yes Refl
finEq FZ (FS y)      = No (λ ())
finEq (FS x) FZ      = No (λ ())
finEq (FS x) (FS y)  with finEq x y
finEq (FS x) (FS .x) | Yes Refl = Yes Refl
finEq (FS x) (FS y)  | No npf   = No (neqFS npf)
  
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

fincr : {n : nat} -> fin (Suc n) -> fin n -> fin (Suc n)
fincr FZ     x      = FS x
fincr (FS y) FZ     = FZ
fincr (FS y) (FS x) = FS (fincr y x)

fincrNeq : {n : nat} (x : fin (Suc n)) (y : fin n) -> not (fincr x y == x)
fincrNeq FZ     y      ()
fincrNeq (FS x) FZ     ()
fincrNeq (FS x) (FS y) pf = fincrNeq x y (eqFSBackwards pf)

fdecr : {n : nat} (x y : fin (Suc n)) -> not (y == x) -> fin n
fdecr {n}     FZ      FZ      npf with npf Refl
fdecr {n}     FZ      FZ      npf | ()
fdecr {Zero}  FZ      (FS ()) npf
fdecr {Zero}  (FS ()) y       npf
fdecr {Suc n} FZ      (FS y)  npf = y
fdecr {Suc n} (FS x)  FZ      npf = FZ
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

data _comp_ {n : nat} (x y : fin n) : Set where
  GT : x >=F y -> not (x == y) -> x comp y
  EQ : x == y -> x comp y
  LT : y >=F x -> not (x == y) -> x comp y

finComp : {n : nat} (x y : fin n) -> x comp y
finComp FZ     FZ      = EQ Refl
finComp FZ     (FS y)  = LT S>=Z (λ ())
finComp (FS x) FZ      = GT S>=Z (λ ())
finComp (FS x) (FS y)  with finComp x y 
finComp (FS x) (FS y)  | GT gt neq = GT (S>=S gt) (neqFS neq)
finComp (FS x) (FS .x) | EQ Refl   = EQ Refl
finComp (FS x) (FS y)  | LT lt neq = LT (S>=S lt) (neqFS neq)

finTric : {n : nat} (x y : fin n) -> not (x >=F y) -> not (y == x) -> y >=F x
finTric FZ     FZ     ngt neq with neq Refl
finTric FZ     FZ     ngt neq | ()
finTric FZ     (FS y) ngt neq = S>=Z
finTric (FS x) FZ     ngt neq with ngt S>=Z
finTric (FS x) FZ     ngt neq | ()
finTric (FS x) (FS y) ngt neq with finTric x y (λ gt -> ngt (S>=S gt)) (neqFSBackwards neq)
finTric (FS x) (FS y) ngt neq | lt = S>=S lt

finTric' : {n : nat} (x y : fin n) -> x >=F y -> not (y == x) -> not (y >=F x)
finTric' FZ     FZ     gt        neq pf        = neq Refl
finTric' FZ     (FS y) ()        neq pf
finTric' (FS x) FZ     gt        neq ()
finTric' (FS x) (FS y) (S>=S gt) neq (S>=S pf) = finTric' x y gt (neqFSBackwards neq) pf

fgtTrans : {n : nat} (x y z : fin n) -> x >=F y -> y >=F z -> x >=F z
fgtTrans x      FZ     FZ     gt1        Z>=Z       = gt1
fgtTrans (FS x) (FS y) FZ     (S>=S gt1) S>=Z       = S>=Z
fgtTrans (FS x) (FS y) (FS z) (S>=S gt1) (S>=S gt2) = S>=S (fgtTrans x y z gt1 gt2)

fincrFdecrSwap : {tn : nat} (x y z : fin (Suc tn)) (neq : not (fincr (FS x) z == weaken y)) (neq2 : not (z == y)) -> x >=F y -> 
  fdecr (weaken y) (fincr (FS x) z) neq == fincr x (fdecr y z neq2)
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

fdecrFincrSwap : {tn : nat} (x y z : fin (Suc tn)) (neq : not (fincr (weaken x) z == FS y)) (neq2 : not (z == y)) -> y >=F x ->
  fdecr (FS y) (fincr (weaken x) z) neq == fincr x (fdecr y z neq2)
fdecrFincrSwap {tn}     FZ      y       z       neq neq2 lt = Refl
fdecrFincrSwap {tn}     (FS x)  FZ      FZ      neq neq2 lt with neq2 Refl
fdecrFincrSwap {tn}     (FS x)  FZ      FZ      neq neq2 lt | ()
fdecrFincrSwap {tn}     (FS x)  FZ      (FS z)  neq neq2 ()
fdecrFincrSwap {Zero}   (FS ()) (FS y)  x       neq neq2 lt
fdecrFincrSwap {Suc tn} (FS x)  (FS y)  FZ      neq neq2 lt = Refl
fdecrFincrSwap {Suc tn} (FS x)  (FS y)  (FS z)  neq neq2 (S>=S lt) rewrite fdecrFincrSwap x y z (neqFSBackwards neq) (neqFSBackwards neq2) lt = Refl

fdecrFincrRefl : {tn : nat} (x : fin (Suc tn)) (y : fin tn) (neq : not (fincr x y == x)) -> fdecr x (fincr x y) neq == y
fdecrFincrRefl FZ     FZ     neq = Refl
fdecrFincrRefl FZ     (FS y) neq = Refl
fdecrFincrRefl (FS x) FZ     neq = Refl
fdecrFincrRefl (FS x) (FS y) neq rewrite fdecrFincrRefl x y (neqFSBackwards neq) = Refl

fincrSwap : {tn : nat} (t : fin tn) (x y : fin (Suc tn)) -> x >=F y -> fincr (weaken y) (fincr x t) == fincr (FS x) (fincr y t) 
fincrSwap t      FZ     FZ     gt        = Refl
fincrSwap t      FZ     (FS y) ()
fincrSwap t      (FS x) FZ     gt        = Refl
fincrSwap FZ     (FS x) (FS y) (S>=S gt) = Refl
fincrSwap (FS t) (FS x) (FS y) (S>=S gt) rewrite fincrSwap t x y gt = Refl
 
fincrAbove : {n : nat} (x y : fin n) -> x >=F y -> fincr (FS x) y == weaken y
fincrAbove FZ     FZ     Z>=Z      = Refl
fincrAbove (FS x) FZ     S>=Z      = Refl
fincrAbove (FS x) (FS y) (S>=S gt) rewrite fincrAbove x y gt = Refl

fincrAbove' : {n : nat} (x y : fin n) -> x >=F y -> not (y == x) -> fincr (weaken x) y == weaken y
fincrAbove' FZ     FZ     Z>=Z      neq with neq Refl
fincrAbove' FZ     FZ     Z>=Z      neq | ()
fincrAbove' (FS x) FZ     S>=Z      neq = Refl
fincrAbove' (FS x) (FS y) (S>=S gt) neq rewrite fincrAbove' x y gt (neqFSBackwards neq) = Refl

fincrBelow : {n : nat} (x y : fin n) -> y >=F x -> not (y == x) -> fincr (FS x) y == FS y
fincrBelow FZ     FZ     Z>=Z      neq with neq Refl
fincrBelow FZ     FZ     Z>=Z      neq | ()
fincrBelow FZ     (FS y) S>=Z      neq = Refl
fincrBelow (FS x) (FS y) (S>=S gt) neq rewrite fincrBelow x y gt (neqFSBackwards neq) = Refl

fincrBelow' : {n : nat} (x y : fin n) -> y >=F x -> fincr (weaken x) y == FS y
fincrBelow' FZ     FZ     Z>=Z      = Refl
fincrBelow' FZ     (FS y) S>=Z      = Refl
fincrBelow' (FS x) (FS y) (S>=S gt) rewrite fincrBelow' x y gt = Refl

fdecrPfIrrel : {n : nat} (x y : fin (Suc n)) (neq neq2 : not (y == x)) -> fdecr x y neq == fdecr x y neq2
fdecrPfIrrel {n} FZ FZ neq neq2 with neq Refl
fdecrPfIrrel {n} FZ FZ neq neq2 | ()
fdecrPfIrrel {Zero} x (FS ()) neq neq2
fdecrPfIrrel {Zero} (FS ()) y neq neq2
fdecrPfIrrel {Suc n} FZ (FS y) neq neq2 = Refl
fdecrPfIrrel {Suc n} (FS x) FZ neq neq2 = Refl
fdecrPfIrrel {Suc n} (FS x) (FS y) neq neq2 = funEq FS (fdecrPfIrrel x y (neqFSBackwards neq) (neqFSBackwards neq2))

fdecrSwap : {n : nat} (x y : fin (Suc n)) (z : fin (Suc (Suc n))) (neq : not (z == FS x)) (neq2 : not (z == weaken y)) 
  (neq3 : not (fdecr (FS x) z neq == y)) (neq4 : not (fdecr (weaken y) z neq2 == x)) -> x >=F y -> 
    fdecr y (fdecr (FS x) z neq) neq3 == fdecr x (fdecr (weaken y) z neq2) neq4
fdecrSwap {n} FZ FZ FZ neq neq2 neq3 neq4 Z>=Z with neq2 Refl
fdecrSwap {n} FZ FZ FZ neq neq2 neq3 neq4 Z>=Z | ()
fdecrSwap {Zero} FZ FZ (FS FZ) neq neq2 neq3 neq4 Z>=Z with neq Refl
fdecrSwap {Zero} FZ FZ (FS FZ) neq neq2 neq3 neq4 Z>=Z | ()
fdecrSwap {Zero} FZ FZ (FS (FS ())) neq neq2 neq3 neq4 Z>=Z
fdecrSwap {Suc n} FZ FZ (FS z) neq neq2 neq3 neq4 Z>=Z = fdecrPfIrrel FZ z (neqFSBackwards neq) neq4
fdecrSwap {n} (FS x) FZ FZ neq neq2 neq3 neq4 S>=Z with neq2 Refl
fdecrSwap {n} (FS x) FZ FZ neq neq2 neq3 neq4 S>=Z | ()
fdecrSwap {Zero} (FS ()) FZ (FS FZ) neq neq2 neq3 neq4 S>=Z
fdecrSwap {Zero} (FS x) FZ (FS (FS ())) neq neq2 neq3 neq4 S>=Z
fdecrSwap {Suc n} (FS x) FZ (FS z) neq neq2 neq3 neq4 S>=Z = fdecrPfIrrel (FS x) z (neqFSBackwards neq) neq4
fdecrSwap {Zero} (FS ()) (FS y) FZ neq neq2 neq3 neq4 (S>=S gt)
fdecrSwap {Suc n} (FS x) (FS y) FZ neq neq2 neq3 neq4 (S>=S gt) = Refl
fdecrSwap {Zero} (FS ()) (FS y) (FS z) neq neq2 neq3 neq4 (S>=S gt)
fdecrSwap {Suc n} (FS x) (FS y) (FS z) neq neq2 neq3 neq4 (S>=S gt)
  rewrite fdecrSwap x y z (neqFSBackwards neq) (neqFSBackwards neq2) (neqFSBackwards neq3) (neqFSBackwards neq4) gt = Refl

fdecrAbove : {n : nat} (x y : fin n) (neq : not (weaken y == FS x)) -> x >=F y -> fdecr (FS x) (weaken y) neq == y
fdecrAbove x      FZ     neq gt = Refl
fdecrAbove FZ     (FS y) neq ()
fdecrAbove (FS x) (FS y) neq (S>=S gt) rewrite fdecrAbove x y (neqFSBackwards neq) gt = Refl

fdecrAbove' : {n : nat} (x y : fin n) (neq : not (weaken y == weaken x)) -> x >=F y -> fdecr (weaken x) (weaken y) neq == y
fdecrAbove' FZ     FZ     neq Z>=Z      with neq Refl
fdecrAbove' FZ     FZ     neq Z>=Z      | ()
fdecrAbove' (FS x) FZ     neq S>=Z      = Refl
fdecrAbove' (FS x) (FS y) neq (S>=S gt) rewrite fdecrAbove' x y (neqFSBackwards neq) gt = Refl

fdecrBelow : {n : nat} (x y : fin n) (neq : not (FS x == weaken y)) -> x >=F y -> fdecr (weaken y) (FS x) neq == x
fdecrBelow x      FZ     neq gt = Refl
fdecrBelow FZ     (FS y) neq ()
fdecrBelow (FS x) (FS y) neq (S>=S gt) rewrite fdecrBelow x y (neqFSBackwards neq) gt = Refl
