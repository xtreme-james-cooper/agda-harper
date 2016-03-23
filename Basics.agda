module Basics where

data Falsity : Set where

not : Set -> Set
not x = x -> Falsity

data Truth : Set where
  tt : Truth

data _==_ {i} {A : Set i} : A -> A -> Set i where
  Refl : (a : A) -> a == a

cast : {A B : Set} -> A -> A == B -> B
cast a (Refl A) = a

data Equals? {A : Set} : A -> A -> Set where
  Eq : {x y : A} -> x == y -> Equals? x y
  NEq : {x y : A} -> not (x == y) -> Equals? x y

data bool : Set where
  True : bool
  False : bool

bool_eq : (x y : bool) -> Equals? x y
bool_eq True  True  = Eq (Refl True)
bool_eq True  False = NEq (λ ())
bool_eq False True  = NEq (λ ())
bool_eq False False = Eq (Refl False)

_&_ : bool -> bool -> bool
True  & True  = True
True  & False = False
False & y     = False

data _+_ (A B : Set) : Set where
  InL : A -> A + B
  InR : B -> A + B

neqInL : {A B : Set} (x y : A) -> not (x == y) -> not (InL {A} {B} x == InL y)
neqInL x .x npf (Refl .(InL x)) = npf (Refl x)

neqInR : {A B : Set} (x y : B) -> not (x == y) -> not (InR {A} {B} x == InR y)
neqInR x .x npf (Refl .(InR x)) = npf (Refl x)

pair_eq : {A B : Set} -> ((a b : A) -> Equals? a b) -> ((a b : B) -> Equals? a b) -> (x y : A + B) -> Equals? x y
pair_eq A_eq B_eq (InL x) (InL y)  with A_eq x y
pair_eq A_eq B_eq (InL x) (InL .x) | Eq (Refl .x) = Eq (Refl (InL x))
pair_eq A_eq B_eq (InL x) (InL y)  | NEq npf = NEq (neqInL x y npf)
pair_eq A_eq B_eq (InL x) (InR y)  = NEq (λ ())
pair_eq A_eq B_eq (InR x) (InL y)  = NEq (λ ())
pair_eq A_eq B_eq (InR x) (InR y)  with B_eq x y
pair_eq A_eq B_eq (InR x) (InR .x) | Eq (Refl .x) = Eq (Refl (InR x))
pair_eq A_eq B_eq (InR x) (InR y)  | NEq npf = NEq (neqInR x y npf)

data _*_ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) (b : B a) -> A * B

neqFst : {A : Set} {B : A -> Set} (x y : A) (z : B x) (w : B y) -> not (x == y) -> not ((x , z) == (y , w))
neqFst x .x z .z npf (Refl .(x , z)) = npf (Refl x)

neqSnd : {A : Set} {B : A -> Set} (x : A) (y z : B x) -> not (y == z) -> not ((_,_ {A} {B} x y) == (x , z))
neqSnd x y .y npf (Refl .(x , y)) = npf (Refl y)

prod_eq : {A : Set} {B : A -> Set} -> ((a b : A) -> Equals? a b) -> ({c : A} (a b : B c) -> Equals? a b) -> (x y : A * B) -> Equals? x y
prod_eq A_eq B_eq (a , b) (a' , b') with A_eq a a'
prod_eq A_eq B_eq (a , b) (.a , b') | Eq (Refl .a) with B_eq b b'
prod_eq A_eq B_eq (a , b) (.a , .b) | Eq (Refl .a) | Eq (Refl .b) = Eq (Refl (a , b))
prod_eq A_eq B_eq (a , b) (.a , b') | Eq (Refl .a) | NEq npf = NEq (neqSnd a b b' npf)
prod_eq A_eq B_eq (a , b) (a' , b') | NEq npf      = NEq (neqFst a a' b b' npf)

data option (A : Set) : Set where
  None : option A
  [_] : A -> option A

neqSome : {A : Set} (x y : A) -> not (x == y) -> not ([ x ] == [ y ])
neqSome x .x npf (Refl .([ x ])) = npf (Refl x)

opt_eq : {A : Set} -> ((a b : A) -> Equals? a b) -> (x y : option A) -> Equals? x y
opt_eq A_eq None  None   = Eq (Refl None)
opt_eq A_eq None  [ y ]  = NEq (λ ())
opt_eq A_eq [ x ] None   = NEq (λ ())
opt_eq A_eq [ x ] [ y ]  with A_eq x y
opt_eq A_eq [ x ] [ .x ] | Eq (Refl .x) = Eq (Refl [ x ])
opt_eq A_eq [ x ] [ y ]  | NEq npf      = NEq (neqSome x y npf)

data nat : Set where
  Zero : nat
  Suc : nat -> nat

neqSuc : (x y : nat) -> not (x == y) -> not (Suc x == Suc y)
neqSuc x .x npf (Refl .(Suc x)) = npf (Refl x)

nat_eq : (x y : nat) -> Equals? x y
nat_eq Zero     Zero    = Eq (Refl Zero)
nat_eq Zero    (Suc y)  = NEq (λ ())
nat_eq (Suc x) Zero     = NEq (λ ())
nat_eq (Suc x) (Suc y)  with nat_eq x y
nat_eq (Suc x) (Suc .x) | Eq (Refl .x) = Eq (Refl (Suc x))
nat_eq (Suc x) (Suc y)  | NEq npf      = NEq (neqSuc x y npf)

data fin : nat -> Set where
  FZ : {n : nat} -> fin (Suc n)
  FS : {n : nat} -> fin n -> fin (Suc n)

neqFS : {n : nat} (x y : fin n) -> not (x == y) -> not (FS x == FS y)
neqFS x .x npf (Refl .(FS x)) = npf (Refl x)

fin_eq : {n : nat} (x y : fin n) -> Equals? x y
fin_eq FZ FZ          = Eq (Refl FZ)
fin_eq FZ (FS y)      = NEq (λ ())
fin_eq (FS x) FZ      = NEq (λ ())
fin_eq (FS x) (FS y)  with fin_eq x y
fin_eq (FS x) (FS .x) | Eq (Refl .x) = Eq (Refl (FS x))
fin_eq (FS x) (FS y)  | NEq npf      = NEq (neqFS x y npf)

fincr : {n : nat} -> fin n -> fin (Suc n) -> fin (Suc n)
fincr x      FZ     = FS x
fincr FZ     (FS y) = FZ
fincr (FS x) (FS y) = FS (fincr x y)

data vect (A : Set) : nat -> Set where
  [] : vect A Zero
  _::_ : {n : nat} -> A -> vect A n -> vect A (Suc n)

neqHd : {A : Set} {n : nat} (a b : A) (as bs : vect A n) -> not (a == b) -> not ((a :: as) == (b :: bs))
neqHd a .a as .as npf (Refl .(a :: as)) = npf (Refl a)

neqTl : {A : Set} {n : nat} (a b : A) (as bs : vect A n) -> not (as == bs) -> not ((a :: as) == (b :: bs))
neqTl a .a as .as npf (Refl .(a :: as)) = npf (Refl as)

vect_eq : {A : Set} {n : nat} -> ((a b : A) -> Equals? a b) -> (x y : vect A n) -> Equals? x y 
vect_eq A_eq [] []                 = Eq (Refl [])
vect_eq A_eq (a :: as) (b :: bs)   with A_eq a b
vect_eq A_eq (a :: as) (.a :: bs)  | Eq (Refl .a) with vect_eq A_eq as bs
vect_eq A_eq (a :: as) (.a :: .as) | Eq (Refl .a) | Eq (Refl .as) = Eq (Refl (a :: as))
vect_eq A_eq (a :: as) (.a :: bs)  | Eq (Refl .a) | NEq npf       = NEq (neqTl a a as bs npf)
vect_eq A_eq (a :: as) (b :: bs)   | NEq npf      = NEq (neqHd a b as bs npf)

_!_ : {A : Set} {n : nat} -> vect A n -> fin n -> A
[]       ! ()
(x :: v) ! FZ     = x
(x :: v) ! (FS f) = v ! f

insertAt : {A : Set} {n : nat} -> fin (Suc n) -> vect A n -> A -> vect A (Suc n)
insertAt FZ      vect        a = a :: vect
insertAt (FS ()) []          a
insertAt (FS f)  (b :: vect) a = b :: (insertAt f vect a)

insertAtFincr : {A : Set} {n : nat} (gam : vect A n) (x : fin n) (y : fin (Suc n)) (a : A) -> (insertAt y gam a ! fincr x y) == (gam ! x)
insertAtFincr (b :: gam) FZ     FZ     a = Refl b
insertAtFincr (b :: gam) FZ     (FS y) a = Refl b
insertAtFincr (b :: gam) (FS x) FZ     a = Refl (gam ! x)
insertAtFincr (b :: gam) (FS x) (FS y) a = insertAtFincr gam x y a

find : {A : Set} {n : nat} -> (A -> bool) -> vect A n -> (fin n)
find P as = {!!}
