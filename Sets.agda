module Sets where

open import Basics
open import Nat
open import Fin
open import Vect

_∈_ : {A : Set} {n : nat} (a : A) (as : vect A n) -> Set
_∈_ {A} {n} a as = fin n * (λ i -> (as ! i) == a)

infix 50 _∈_

ninUp : {A : Set} {n : nat} {a b : A} {as : vect A n} -> not (b == a) -> not (a ∈ as) -> not (a ∈ b :: as)
ninUp neq nin (FZ , i)    = neq i
ninUp neq nin (FS ix , i) = nin (ix , i)

ninDown : {A : Set} {n : nat} {a b : A} {as : vect A n} -> not (a ∈ b :: as) -> not (a ∈ as)
ninDown nin (ix , i) = nin (FS ix , i)

contains? : {A : Set} {n : nat} -> equality A -> (as : vect A n) (a : A) -> decide (a ∈ as)
contains? aeq []        a = No (λ { (() , _) })
contains? aeq (b :: as) a with aeq b a | contains? aeq as a
contains? aeq (b :: as) a | Yes eq     | in2          = Yes (FZ , eq)
contains? aeq (b :: as) a | No neq     | Yes (ix , i) = Yes (FS ix , i)
contains? aeq (b :: as) a | No neq     | No ni        = No (ninUp neq ni)

finite : Set -> Set
finite A = nat * (λ n -> vect A n * (λ vals -> (a : A) -> a ∈ vals)) 

inCons : {A : Set} {n : nat} {a a' : A} {as : vect A n} -> a ∈ as -> a ∈ (a' :: as)
inCons (i , mem) = FS i , mem

data isSet {A : Set} : {n : nat} -> vect A n -> Set where 
  EmptySet : isSet []
  Insert : {n : nat} {as : vect A n} (a : A) -> isSet as -> not (a ∈ as) -> isSet (a :: as)

union : {A : Set} {n m : nat} -> equality A -> vect A n -> vect A m -> nat * vect A
union aeq []        bs = _ , bs
union aeq (a :: as) bs with contains? aeq bs a | union aeq as bs
union aeq (a :: as) bs | Yes _ | un     = un
union aeq (a :: as) bs | No _  | n , un = Suc n , a :: un

-- lemmas

filterReduces : {A : Set} {n n' : nat} {p : A -> Set} (a : A) (as : vect A n) (as' : vect A n') (f : (a : A) -> decide (p a)) -> filter f as == (n' , as') -> 
  not (a ∈ as) -> not (a ∈ as')
filterReduces a []         .[]         f Refl nin (() , _)
filterReduces a (b :: as)  as'         f eq   nin (ix , i)    with f b | filter f as | inspect (filter f) as
filterReduces a (.a :: as) .(a :: as') f Refl nin (FZ , Refl) | Yes _  | n , as'     | [ pf ] = nin (FZ , Refl)
filterReduces a (b :: as)  .(b :: as') f Refl nin (FS ix , i) | Yes _  | n , as'     | [ pf ] = filterReduces a as as' f pf (ninDown nin) (ix , i)
filterReduces a (b :: as)  .as'        f Refl nin (ix , i)    | No _   | n , as'     | [ pf ] = filterReduces a as as' f pf (ninDown nin) (ix , i) 

filterRemainsSet : {A : Set} {n n' : nat} {p : A -> Set} (as : vect A n) (as' : vect A n') (f : (a : A) -> decide (p a)) -> filter f as == (n' , as') -> isSet as -> isSet as'
filterRemainsSet []        .[]         f Refl EmptySet         = EmptySet
filterRemainsSet (a :: as) as'         f eq   (Insert .a is x) with f a | filter f as | inspect (filter f) as
filterRemainsSet (a :: as) .(a :: as') f Refl (Insert .a is x) | Yes _  | n , as'     | [ pf ] = Insert a (filterRemainsSet as as' f pf is) (filterReduces a as as' f pf x)
filterRemainsSet (a :: as) .as'        f Refl (Insert .a is x) | No _   | n , as'     | [ pf ] = filterRemainsSet as as' f pf is

unionDoesNotAdd : {A : Set} {n m p : nat} (aeq : equality A) (a : A) (as : vect A n) (bs : vect A m) (cs : vect A p) -> not (a ∈ as) -> not (a ∈ bs) ->
  union aeq as bs == (p , cs) -> not (a ∈ cs)
unionDoesNotAdd aeq a []         bs .bs        nina ninb Refl (ix , i)    = ninb (ix , i)
unionDoesNotAdd aeq a (b :: as)  bs cs         nina ninb eq   (ix , i)    with contains? aeq bs b | union aeq as bs | inspect (union aeq as) bs 
unionDoesNotAdd aeq a (b :: as)  bs .cs        nina ninb Refl (ix , i)    | Yes mem | n , cs | [ pf ] = unionDoesNotAdd aeq a as bs cs (ninDown nina) ninb pf (ix , i)
unionDoesNotAdd aeq a (.a :: as) bs .(a :: cs) nina ninb Refl (FZ , Refl) | No nmem | n , cs | [ pf ] = nina (FZ , Refl)
unionDoesNotAdd aeq a (b :: as)  bs .(b :: cs) nina ninb Refl (FS ix , i) | No nmem | n , cs | [ pf ] = unionDoesNotAdd aeq a as bs cs (ninDown nina) ninb pf (ix , i)

unionPreserves2 : {A : Set} {n m p : nat} (aeq : equality A) (a : A) (as : vect A n) (bs : vect A m) (cs : vect A p) -> a ∈ bs -> union aeq as bs == (p , cs) -> a ∈ cs
unionPreserves2 aeq a []        bs .bs        (ix , i) Refl = ix , i
unionPreserves2 aeq a (b :: as) bs cs         (ix , i) eq   with contains? aeq bs b | union aeq as bs | inspect (union aeq as) bs
unionPreserves2 aeq a (b :: as) bs .cs        (ix , i) Refl | Yes _ | n , cs | [ pf ] = unionPreserves2 aeq a as bs cs (ix , i) pf
unionPreserves2 aeq a (b :: as) bs .(b :: cs) (ix , i) Refl | No _  | n , cs | [ pf ] with unionPreserves2 aeq a as bs cs (ix , i) pf
unionPreserves2 aeq a (b :: as) bs .(b :: cs) (ix , i) Refl | No _  | n , cs | [ pf ] | ix' , i' = FS ix' , i'

unionPreserves1 : {A : Set} {n m p : nat} (aeq : equality A) (a : A) (as : vect A n) (bs : vect A m) (cs : vect A p) -> a ∈ as -> union aeq as bs == (p , cs) -> a ∈ cs
unionPreserves1 aeq a []         bs .bs        (() , i)    Refl
unionPreserves1 aeq a (b :: as)  bs cs         (ix , i)    eq   with contains? aeq bs b | union aeq as bs | inspect (union aeq as) bs
unionPreserves1 aeq a (.a :: as) bs .cs        (FZ , Refl) Refl | Yes mem | n , cs | [ pf ] = unionPreserves2 aeq a as bs cs mem pf
unionPreserves1 aeq a (b :: as)  bs .cs        (FS ix , i) Refl | Yes mem | n , cs | [ pf ] = unionPreserves1 aeq a as bs cs (ix , i) pf
unionPreserves1 aeq a (.a :: as) bs .(a :: cs) (FZ , Refl) Refl | No _    | n , cs | [ pf ] = FZ , Refl
unionPreserves1 aeq a (b :: as)  bs .(b :: cs) (FS ix , i) Refl | No _    | n , cs | [ pf ] with unionPreserves1 aeq a as bs cs (ix , i) pf
unionPreserves1 aeq a (b :: as)  bs .(b :: cs) (FS ix , i) Refl | No _    | n , cs | [ pf ] | ix' , i' = FS ix' , i'

unionRemainsSet : {A : Set} {n m p : nat} (aeq : equality A) (as : vect A n) (bs : vect A m) (cs : vect A p) -> isSet as -> isSet bs -> union aeq as bs == (p , cs) -> isSet cs
unionRemainsSet aeq []        bs .bs        EmptySet         isB Refl = isB
unionRemainsSet aeq (a :: as) bs cs         (Insert .a is x) isB eq   with contains? aeq bs a | union aeq as bs | inspect (union aeq as) bs
unionRemainsSet aeq (a :: as) bs .cs        (Insert .a is x) isB Refl | Yes _  | n , cs | [ pf ] = unionRemainsSet aeq as bs cs is isB pf
unionRemainsSet aeq (a :: as) bs .(a :: cs) (Insert .a is x) isB Refl | No nin | n , cs | [ pf ] = 
  Insert a (unionRemainsSet aeq as bs cs is isB pf) (unionDoesNotAdd aeq a as bs cs x nin pf)
