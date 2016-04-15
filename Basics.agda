module Basics where

open import Agda.Primitive

data Falsity : Set where

not : Set -> Set
not x = x -> Falsity

data Truth : Set where
  tt : Truth

data _==_ {i : Level} {A : Set i} (a : A) : A -> Set i where
  Refl : a == a

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL Refl #-}

sym : {A : Set} {a b : A} -> a == b -> b == a
sym Refl = Refl

funEq : {i j : Level} {A : Set i} {B : Set j} {a b : A} (f : A -> B) -> a == b -> f a == f b
funEq f Refl = Refl

data decide (A : Set) : Set where
  Yes : A -> decide A
  No : not A -> decide A

equals? : {A : Set} -> A -> A -> Set
equals? x y = decide (x == y)

data bool : Set where
  True : bool
  False : bool

boolEq : (x y : bool) -> equals? x y
boolEq True  True  = Yes Refl
boolEq True  False = No (λ ())
boolEq False True  = No (λ ())
boolEq False False = Yes Refl

data _\/_ (A B : Set) : Set where
  InL : A -> A \/ B
  InR : B -> A \/ B

pairEq : {A B : Set} -> ((a b : A) -> equals? a b) -> ((a b : B) -> equals? a b) -> (x y : A \/ B) -> equals? x y
pairEq A_eq B_eq (InL x) (InL y)  with A_eq x y
pairEq A_eq B_eq (InL x) (InL .x) | Yes Refl = Yes Refl
pairEq A_eq B_eq (InL x) (InL y)  | No npf   = No (neqInL npf)
  where
    neqInL : {A B : Set} {x y : A} -> not (x == y) -> not (InL {A} {B} x == InL y)
    neqInL npf Refl = npf Refl
pairEq A_eq B_eq (InL x) (InR y)  = No (λ ())
pairEq A_eq B_eq (InR x) (InL y)  = No (λ ())
pairEq A_eq B_eq (InR x) (InR y)  with B_eq x y
pairEq A_eq B_eq (InR x) (InR .x) | Yes Refl = Yes Refl
pairEq A_eq B_eq (InR x) (InR y)  | No npf    = No (neqInR npf)
  where
    neqInR : {A B : Set} {x y : B} -> not (x == y) -> not (InR {A} {B} x == InR y)
    neqInR npf Refl = npf Refl

data _*_ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) (b : B a) -> A * B

prodEq : {A : Set} {B : A -> Set} -> ((a b : A) -> equals? a b) -> ({c : A} (a b : B c) -> equals? a b) -> (x y : A * B) -> equals? x y
prodEq A_eq B_eq (a , b) (a' , b') with A_eq a a'
prodEq A_eq B_eq (a , b) (.a , b') | Yes Refl with B_eq b b'
prodEq A_eq B_eq (a , b) (.a , .b) | Yes Refl | Yes Refl = Yes Refl
prodEq A_eq B_eq (a , b) (.a , b') | Yes Refl | No npf   = No (neqSnd npf)
  where
    neqSnd : {A : Set} {B : A -> Set} {x : A} {y z : B x} -> not (y == z) -> not ((_,_ {A} {B} x y) == (x , z))
    neqSnd npf Refl = npf Refl
prodEq A_eq B_eq (a , b) (a' , b') | No npf   = No (neqFst npf)
  where
    neqFst : {A : Set} {B : A -> Set} {x y : A} {z : B x} {w : B y} -> not (x == y) -> not ((x , z) == (y , w))
    neqFst npf Refl = npf Refl

data option (A : Set) : Set where
  None : option A
  [_] : A -> option A

optEq : {A : Set} -> ((a b : A) -> equals? a b) -> (x y : option A) -> equals? x y
optEq A_eq None  None   = Yes Refl
optEq A_eq None  [ y ]  = No (λ ())
optEq A_eq [ x ] None   = No (λ ())
optEq A_eq [ x ] [ y ]  with A_eq x y
optEq A_eq [ x ] [ .x ] | Yes Refl = Yes Refl
optEq A_eq [ x ] [ y ]  | No npf   = No (neqSome npf)
  where
    neqSome : {A : Set} {x y : A} -> not (x == y) -> not ([ x ] == [ y ])
    neqSome npf Refl = npf Refl

data nat : Set where
  Zero : nat
  Suc : nat -> nat

natEq : (x y : nat) -> equals? x y
natEq Zero    Zero     = Yes Refl
natEq Zero    (Suc y)  = No (λ ())
natEq (Suc x) Zero     = No (λ ())
natEq (Suc x) (Suc y)  with natEq x y
natEq (Suc x) (Suc .x) | Yes Refl = Yes Refl
natEq (Suc x) (Suc y)  | No npf   = No (neqSuc npf)
  where    
    neqSuc : {x y : nat} -> not (x == y) -> not (Suc x == Suc y)
    neqSuc npf Refl = npf Refl

data fin : nat -> Set where
  FZ : {n : nat} -> fin (Suc n)
  FS : {n : nat} -> fin n -> fin (Suc n)

neqFSBackwards : {n : nat} (x y : fin n) -> not (FS x == FS y) -> not (x == y)
neqFSBackwards x .x npf Refl = npf Refl

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
neqToNeq' {Suc n} {FS x} {FS y} npf with neqToNeq' (neqFSBackwards x y npf)
neqToNeq' {Suc n} {FS x} {FS y} npf | pf = SNeqS pf

weaken : {n : nat} -> fin n -> fin (Suc n)
weaken FZ = FZ
weaken (FS x) = FS (weaken x)

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
fdecr {Suc n} (FS x)  (FS y)  npf = FS (fdecr x y (neqFSBackwards x y npf))

data _>F_ : {n : nat} -> fin n -> fin n -> Set where
  S>Z : {n : nat} {x : fin n} -> FS x >F FZ
  S>S : {n : nat} {x y : fin n} -> x >F y -> FS x >F FS y

fincrFdecrSwap : {tn : nat} (x y z : fin (Suc tn)) (neq : not (fincr z (FS x) == weaken y)) (neq2 : not (z == y)) -> x >F y -> 
  fdecr (fincr z (FS x)) (weaken y) neq == fincr (fdecr z y neq2) x
fincrFdecrSwap {tn}     x      FZ      FZ     neq neq2 gt with neq Refl
fincrFdecrSwap {tn}     x      FZ      FZ     neq neq2 gt | ()
fincrFdecrSwap {tn}     FZ     (FS y)  FZ     neq neq2 ()
fincrFdecrSwap {Zero}   (FS x) (FS ()) FZ     neq neq2 gt
fincrFdecrSwap {Suc tn} (FS x) (FS y)  FZ     neq neq2 gt = Refl
fincrFdecrSwap {Zero} x FZ (FS ()) neq neq2 gt
fincrFdecrSwap {Suc tn} x FZ (FS z) neq neq2 gt = Refl
fincrFdecrSwap {tn} FZ (FS y) (FS z) neq neq2 ()
fincrFdecrSwap {Zero} (FS ()) (FS y) (FS z) neq neq2 gt
fincrFdecrSwap {Suc tn} (FS x) (FS y) (FS z) neq neq2 (S>S gt) 
  rewrite fincrFdecrSwap x y z (neqFSBackwards (fincr z (FS x)) (weaken y) neq) (neqFSBackwards z y neq2) gt = Refl

fincrSwap : {tn : nat} (t : fin tn) (x y : fin (Suc tn)) -> x >F y -> fincr (fincr t x) (weaken y) == fincr (fincr t y) (FS x)
fincrSwap t      FZ     FZ     gt       = Refl
fincrSwap t      FZ     (FS y) ()
fincrSwap t      (FS x) FZ     gt       = Refl
fincrSwap FZ     (FS x) (FS y) (S>S gt) = Refl
fincrSwap (FS t) (FS x) (FS y) (S>S gt) rewrite fincrSwap t x y gt = Refl

data vect (A : Set) : nat -> Set where
  [] : vect A Zero
  _::_ : {n : nat} -> A -> vect A n -> vect A (Suc n)

vectEq : {A : Set} {n : nat} -> ((a b : A) -> equals? a b) -> (x y : vect A n) -> equals? x y 
vectEq A_eq [] []                 = Yes Refl
vectEq A_eq (a :: as) (b :: bs)   with A_eq a b
vectEq A_eq (a :: as) (.a :: bs)  | Yes Refl with vectEq A_eq as bs
vectEq A_eq (a :: as) (.a :: .as) | Yes Refl | Yes Refl = Yes Refl
vectEq A_eq (a :: as) (.a :: bs)  | Yes Refl | No npf   = No (neqTl npf)
  where
    neqTl : {A : Set} {n : nat} {a b : A} {as bs : vect A n} -> not (as == bs) -> not ((a :: as) == (b :: bs))
    neqTl npf Refl = npf Refl

vectEq A_eq (a :: as) (b :: bs)   | No npf   = No (neqHd npf)
  where
    neqHd : {A : Set} {n : nat} {a b : A} {as bs : vect A n} -> not (a == b) -> not ((a :: as) == (b :: bs))
    neqHd npf Refl = npf Refl

_!_ : {A : Set} {n : nat} -> vect A n -> fin n -> A
[]       ! ()
(x :: v) ! FZ     = x
(x :: v) ! (FS f) = v ! f

insertAt : {A : Set} {n : nat} -> fin (Suc n) -> vect A n -> A -> vect A (Suc n)
insertAt FZ      vect        a = a :: vect
insertAt (FS ()) []          a
insertAt (FS f)  (b :: vect) a = b :: (insertAt f vect a)

lookupInsertAt : {A : Set} {n : nat} (vs : vect A n) (x : fin (Suc n)) (v : A) -> (insertAt x vs v ! x) == v
lookupInsertAt vs        FZ      v = Refl
lookupInsertAt []        (FS ()) v
lookupInsertAt (x :: vs) (FS y)  v = lookupInsertAt vs y v

insertAtFincr : {A : Set} {n : nat} (gam : vect A n) (x : fin n) (y : fin (Suc n)) (a : A) -> (insertAt y gam a ! fincr x y) == (gam ! x)
insertAtFincr (b :: gam) FZ     FZ     a = Refl
insertAtFincr (b :: gam) FZ     (FS y) a = Refl
insertAtFincr (b :: gam) (FS x) FZ     a = Refl
insertAtFincr (b :: gam) (FS x) (FS y) a = insertAtFincr gam x y a

insertAtFdecr : {A : Set} {n : nat} {vs : vect A n} {x y : fin (Suc n)} {a b : A} -> (npf : not (y == x)) -> (insertAt x vs a ! y) == b -> (vs ! fdecr y x npf) == b
insertAtFdecr {A} {n}     {vs}      {FZ}    {FZ}    npf Refl with npf Refl
insertAtFdecr {A} {n}     {vs}      {FZ}    {FZ}    npf Refl | ()
insertAtFdecr {A} {.Zero} {[]}      {FZ}    {FS ()} npf Refl
insertAtFdecr {A} {.Zero} {[]}      {FS ()} {y}     npf Refl
insertAtFdecr {A} {Suc n} {v :: vs} {FZ}    {FS y}  npf Refl = Refl
insertAtFdecr {A} {Suc n} {v :: vs} {FS x}  {FZ}    npf Refl = Refl
insertAtFdecr {A} {Suc n} {v :: vs} {FS x}  {FS y}  npf Refl = insertAtFdecr (neqFSBackwards y x npf) Refl

map : {A B : Set} {n : nat} -> (A -> B) -> vect A n -> vect B n
map f []        = []
map f (a :: as) = f a :: map f as

mapLookup : {A B : Set} {n : nat} (f : A -> B) (as : vect A n) (x : fin n) -> (map f as ! x) == f (as ! x)
mapLookup f (a :: as) FZ     = Refl
mapLookup f (a :: as) (FS x) = mapLookup f as x

mapInsertAt : {A B : Set} {n : nat} (as : vect A n) (a : A) (f : A -> B) (x : fin (Suc n)) -> map f (insertAt x as a) == insertAt x (map f as) (f a)
mapInsertAt []        b f FZ      = Refl
mapInsertAt []        b f (FS ())
mapInsertAt (a :: as) b f FZ      = Refl
mapInsertAt (a :: as) b f (FS x)  = funEq (λ bs -> f a :: bs) (mapInsertAt as b f x)

