module Basics where

open import Agda.Primitive

data Falsity : Set where

not : Set -> Set
not x = x -> Falsity

data Truth : Set where
  tt : Truth

data _==_ {i : Level} {A : Set i} : A -> A -> Set i where
  Refl : (a : A) -> a == a

_castTo_ : {A B : Set} -> A -> A == B -> B
a castTo (Refl A) = a

flip : {A : Set} {a b : A} -> a == b -> b == a
flip (Refl a) = Refl a

funEq : {i j : Level} {A : Set i} {B : Set j} {a b : A} (f : A -> B) -> a == b -> f a == f b
funEq f (Refl a) = Refl (f a)

data decide (A : Set) : Set where
  Yes : A -> decide A
  No : not A -> decide A

equals? : {A : Set} -> A -> A -> Set
equals? x y = decide (x == y)

data bool : Set where
  True : bool
  False : bool

bool_eq : (x y : bool) -> equals? x y
bool_eq True  True  = Yes (Refl True)
bool_eq True  False = No (λ ())
bool_eq False True  = No (λ ())
bool_eq False False = Yes (Refl False)

data _\/_ (A B : Set) : Set where
  InL : A -> A \/ B
  InR : B -> A \/ B

pair_eq : {A B : Set} -> ((a b : A) -> equals? a b) -> ((a b : B) -> equals? a b) -> (x y : A \/ B) -> equals? x y
pair_eq A_eq B_eq (InL x) (InL y)  with A_eq x y
pair_eq A_eq B_eq (InL x) (InL .x) | Yes (Refl .x) = Yes (Refl (InL x))
pair_eq A_eq B_eq (InL x) (InL y)  | No npf        = No (neqInL x y npf)
  where
    neqInL : {A B : Set} (x y : A) -> not (x == y) -> not (InL {A} {B} x == InL y)
    neqInL x .x npf (Refl .(InL x)) = npf (Refl x)
pair_eq A_eq B_eq (InL x) (InR y)  = No (λ ())
pair_eq A_eq B_eq (InR x) (InL y)  = No (λ ())
pair_eq A_eq B_eq (InR x) (InR y)  with B_eq x y
pair_eq A_eq B_eq (InR x) (InR .x) | Yes (Refl .x) = Yes (Refl (InR x))
pair_eq A_eq B_eq (InR x) (InR y)  | No npf        = No (neqInR x y npf)
  where
    neqInR : {A B : Set} (x y : B) -> not (x == y) -> not (InR {A} {B} x == InR y)
    neqInR x .x npf (Refl .(InR x)) = npf (Refl x)

data _*_ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) (b : B a) -> A * B

prod_eq : {A : Set} {B : A -> Set} -> ((a b : A) -> equals? a b) -> ({c : A} (a b : B c) -> equals? a b) -> (x y : A * B) -> equals? x y
prod_eq A_eq B_eq (a , b) (a' , b') with A_eq a a'
prod_eq A_eq B_eq (a , b) (.a , b') | Yes (Refl .a) with B_eq b b'
prod_eq A_eq B_eq (a , b) (.a , .b) | Yes (Refl .a) | Yes (Refl .b) = Yes (Refl (a , b))
prod_eq A_eq B_eq (a , b) (.a , b') | Yes (Refl .a) | No npf        = No (neqSnd a b b' npf)
  where
    neqSnd : {A : Set} {B : A -> Set} (x : A) (y z : B x) -> not (y == z) -> not ((_,_ {A} {B} x y) == (x , z))
    neqSnd x y .y npf (Refl .(x , y)) = npf (Refl y)
prod_eq A_eq B_eq (a , b) (a' , b') | No npf        = No (neqFst a a' b b' npf)
  where
    neqFst : {A : Set} {B : A -> Set} (x y : A) (z : B x) (w : B y) -> not (x == y) -> not ((x , z) == (y , w))
    neqFst x .x z .z npf (Refl .(x , z)) = npf (Refl x)

data option (A : Set) : Set where
  None : option A
  [_] : A -> option A

opt_eq : {A : Set} -> ((a b : A) -> equals? a b) -> (x y : option A) -> equals? x y
opt_eq A_eq None  None   = Yes (Refl None)
opt_eq A_eq None  [ y ]  = No (λ ())
opt_eq A_eq [ x ] None   = No (λ ())
opt_eq A_eq [ x ] [ y ]  with A_eq x y
opt_eq A_eq [ x ] [ .x ] | Yes (Refl .x) = Yes (Refl [ x ])
opt_eq A_eq [ x ] [ y ]  | No npf        = No (neqSome x y npf)
  where
    neqSome : {A : Set} (x y : A) -> not (x == y) -> not ([ x ] == [ y ])
    neqSome x .x npf (Refl .([ x ])) = npf (Refl x)

data nat : Set where
  Zero : nat
  Suc : nat -> nat

nat_eq : (x y : nat) -> equals? x y
nat_eq Zero    Zero     = Yes (Refl Zero)
nat_eq Zero    (Suc y)  = No (λ ())
nat_eq (Suc x) Zero     = No (λ ())
nat_eq (Suc x) (Suc y)  with nat_eq x y
nat_eq (Suc x) (Suc .x) | Yes (Refl .x) = Yes (Refl (Suc x))
nat_eq (Suc x) (Suc y)  | No npf        = No(neqSuc x y npf)
  where    
    neqSuc : (x y : nat) -> not (x == y) -> not (Suc x == Suc y)
    neqSuc x .x npf (Refl .(Suc x)) = npf (Refl x)

data fin : nat -> Set where
  FZ : {n : nat} -> fin (Suc n)
  FS : {n : nat} -> fin n -> fin (Suc n)

neqFS_backwards : {n : nat} (x y : fin n) -> not (FS x == FS y) -> not (x == y)
neqFS_backwards x .x npf (Refl .x) = npf (Refl (FS x))

fin_eq : {n : nat} (x y : fin n) -> equals? x y
fin_eq FZ FZ          = Yes (Refl FZ)
fin_eq FZ (FS y)      = No (λ ())
fin_eq (FS x) FZ      = No (λ ())
fin_eq (FS x) (FS y)  with fin_eq x y
fin_eq (FS x) (FS .x) | Yes (Refl .x) = Yes (Refl (FS x))
fin_eq (FS x) (FS y)  | No npf        = No (neqFS x y npf)
  where
    neqFS : {n : nat} (x y : fin n) -> not (x == y) -> not (FS x == FS y)
    neqFS x .x npf (Refl .(FS x)) = npf (Refl x)

data finNeq : {n : nat} -> fin n -> fin n -> Set where
  ZNeqS : {n : nat} {f : fin n} -> finNeq FZ (FS f)
  SNeqZ : {n : nat} {f : fin n} -> finNeq (FS f) FZ
  SNeqS : {n : nat} {f g : fin n} -> finNeq f g -> finNeq (FS f) (FS g)

finNeqIden : {n : nat} {x y : fin n} (pf1 pf2 : finNeq x y) -> pf1 == pf2
finNeqIden ZNeqS       ZNeqS        = Refl ZNeqS
finNeqIden SNeqZ       SNeqZ        = Refl SNeqZ
finNeqIden (SNeqS pf1) (SNeqS pf2)  with finNeqIden pf1 pf2
finNeqIden (SNeqS pf1) (SNeqS .pf1) | Refl .pf1 = Refl (SNeqS pf1)

neqToNeq : {n : nat} {x y : fin n} -> finNeq x y -> not (x == y)
neqToNeq            ZNeqS       ()
neqToNeq            SNeqZ       ()
neqToNeq {x = FS x} (SNeqS neq) (Refl .(FS x)) = neqToNeq neq (Refl x)

neqToNeq' : {n : nat} {x y : fin n} -> not (x == y) -> finNeq x y
neqToNeq' {Suc n} {FZ}   {FZ}   npf with npf (Refl FZ)
neqToNeq' {Suc n} {FZ}   {FZ}   npf | ()
neqToNeq' {Suc n} {FZ}   {FS y} npf = ZNeqS
neqToNeq' {Suc n} {FS x} {FZ}   npf = SNeqZ
neqToNeq' {Suc n} {FS x} {FS y} npf with neqToNeq' (neqFS_backwards x y npf)
neqToNeq' {Suc n} {FS x} {FS y} npf | pf = SNeqS pf

fincr : {n : nat} -> fin n -> fin (Suc n) -> fin (Suc n)
fincr x      FZ     = FS x
fincr FZ     (FS y) = FZ
fincr (FS x) (FS y) = FS (fincr x y)

fdecr : {n : nat} (x y : fin (Suc n)) -> not (x == y) -> fin n
fdecr         FZ      FZ      npf with npf (Refl FZ)
fdecr         FZ      FZ      npf | ()
fdecr {Zero}  FZ      (FS ()) npf
fdecr {Zero}  (FS ()) y       npf
fdecr {Suc n} FZ      (FS y)  npf = FZ
fdecr {Suc n} (FS x)  FZ      npf = x
fdecr {Suc n} (FS x)  (FS y)  npf = FS (fdecr x y (neqFS_backwards x y npf))

data vect (A : Set) : nat -> Set where
  [] : vect A Zero
  _::_ : {n : nat} -> A -> vect A n -> vect A (Suc n)

vect_eq : {A : Set} {n : nat} -> ((a b : A) -> equals? a b) -> (x y : vect A n) -> equals? x y 
vect_eq A_eq [] []                 = Yes (Refl [])
vect_eq A_eq (a :: as) (b :: bs)   with A_eq a b
vect_eq A_eq (a :: as) (.a :: bs)  | Yes (Refl .a) with vect_eq A_eq as bs
vect_eq A_eq (a :: as) (.a :: .as) | Yes (Refl .a) | Yes (Refl .as) = Yes (Refl (a :: as))
vect_eq A_eq (a :: as) (.a :: bs)  | Yes (Refl .a) | No npf         = No (neqTl a a as bs npf)
  where
    neqTl : {A : Set} {n : nat} (a b : A) (as bs : vect A n) -> not (as == bs) -> not ((a :: as) == (b :: bs))
    neqTl a .a as .as npf (Refl .(a :: as)) = npf (Refl as)

vect_eq A_eq (a :: as) (b :: bs)   | No npf        = No (neqHd a b as bs npf)
  where
    neqHd : {A : Set} {n : nat} (a b : A) (as bs : vect A n) -> not (a == b) -> not ((a :: as) == (b :: bs))
    neqHd a .a as .as npf (Refl .(a :: as)) = npf (Refl a)

_!_ : {A : Set} {n : nat} -> vect A n -> fin n -> A
[]       ! ()
(x :: v) ! FZ     = x
(x :: v) ! (FS f) = v ! f

insertAt : {A : Set} {n : nat} -> fin (Suc n) -> vect A n -> A -> vect A (Suc n)
insertAt FZ      vect        a = a :: vect
insertAt (FS ()) []          a
insertAt (FS f)  (b :: vect) a = b :: (insertAt f vect a)

lookupInsertAt : {A : Set} {n : nat} (vs : vect A n) (x : fin (Suc n)) (v : A) -> (insertAt x vs v ! x) == v
lookupInsertAt vs        FZ      v = Refl v
lookupInsertAt []        (FS ()) v
lookupInsertAt (x :: vs) (FS y)  v = lookupInsertAt vs y v

insertAtFincr : {A : Set} {n : nat} (gam : vect A n) (x : fin n) (y : fin (Suc n)) (a : A) -> (insertAt y gam a ! fincr x y) == (gam ! x)
insertAtFincr (b :: gam) FZ     FZ     a = Refl b
insertAtFincr (b :: gam) FZ     (FS y) a = Refl b
insertAtFincr (b :: gam) (FS x) FZ     a = Refl (gam ! x)
insertAtFincr (b :: gam) (FS x) (FS y) a = insertAtFincr gam x y a

insertAtFdecr : {A : Set} {n : nat} {vs : vect A n} {x y : fin (Suc n)} {a b : A} -> (npf : not (y == x)) -> (insertAt x vs a ! y) == b -> (vs ! fdecr y x npf) == b
insertAtFdecr {A} {n} {vs} {FZ} {FZ} {a} npf (Refl .a) with npf (Refl FZ)
insertAtFdecr {A} {n} {vs} {FZ} {FZ} {a} npf (Refl .a) | ()
insertAtFdecr {A} {.Zero} {[]} {FZ} {FS ()} npf (Refl ._)
insertAtFdecr {A} {.Zero} {[]} {FS ()} {y} npf (Refl ._)
insertAtFdecr {A} {Suc n} {v :: vs} {FZ} {FS y} npf (Refl .((v :: vs) ! y)) = Refl ((v :: vs) ! y)
insertAtFdecr {A} {Suc n} {v :: vs} {FS x} {FZ} npf (Refl .v) = Refl v
insertAtFdecr {A} {Suc n} {v :: vs} {FS x} {FS y} {a} npf (Refl .(insertAt x vs a ! y)) = insertAtFdecr (neqFS_backwards y x npf) (Refl (insertAt x vs a ! y))
