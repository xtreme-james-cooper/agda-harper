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

difference : {A : Set} {n m : nat} -> equality A -> vect A n -> vect A m -> nat * vect A
difference aeq as bs = filter (λ a -> decideNot (contains? aeq bs a)) as

remove : {A : Set} {n : nat} -> equality A -> vect A n -> A -> nat * vect A
remove aeq as a = filter (λ a' -> decideNot (aeq a a')) as

-- lemmas

filterFilters : {A : Set} {n n' : nat} {p : A -> Set} (a : A) (as : vect A n) (as' : vect A n') (f : (a : A) -> decide (p a)) -> filter f as == (n' , as') -> a ∈ as' -> p a
filterFilters a []         .[]          f Refl (() , i)
filterFilters a (b :: as)  as'          f eq   (ix , i)    with f b | filter f as | inspect (filter f) as
filterFilters a (.a :: as) .(a :: as'') f Refl (FZ , Refl) | Yes pa | n' , as''   | [ pf ] = pa
filterFilters a (b :: as)  .(b :: as'') f Refl (FS ix , i) | Yes _  | n' , as''   | [ pf ] = filterFilters a as as'' f pf (ix , i)
filterFilters a (b :: as)  .as''        f Refl (ix , i)    | No _   | n' , as''   | [ pf ] = filterFilters a as as'' f pf (ix , i)

filterRetains : {A : Set} {n n' : nat} {p : A -> Set} (a : A) (as : vect A n) (as' : vect A n') (f : (a : A) -> decide (p a)) -> filter f as == (n' , as') -> p a ->
  a ∈ as -> a ∈ as'
filterRetains a []         .[]          f Refl pa (() , i)
filterRetains a (b :: as)  as'          f eq   pa (ix , i)    with f b | filter f as | inspect (filter f) as
filterRetains a (.a :: as) .(a :: as'') f Refl pa (FZ , Refl) | Yes _  | n' , as''   | [ pf ] = FZ , Refl
filterRetains a (b :: as)  .(b :: as'') f Refl pa (FS ix , i) | Yes _  | n' , as''   | [ pf ] with filterRetains a as as'' f pf pa (ix , i)
filterRetains a (b :: as)  .(b :: as'') f Refl pa (FS ix , i) | Yes _  | n' , as''   | [ pf ] | (ix' , i') = FS ix' , i'
filterRetains a (.a :: as) .as''        f Refl pa (FZ , Refl) | No nfa | n' , as''   | [ pf ] with nfa pa
filterRetains a (.a :: as) .as''        f Refl pa (FZ , Refl) | No nfa | n' , as''   | [ pf ] | ()
filterRetains a (b :: as)  .as''        f Refl pa (FS ix , i) | No _   | n' , as''   | [ pf ] = filterRetains a as as'' f pf pa (ix , i)

filterDoesNotAdd : {A : Set} {n n' : nat} {p : A -> Set} (a : A) (as : vect A n) (as' : vect A n') (f : (a : A) -> decide (p a)) -> filter f as == (n' , as') -> p a ->
  a ∈ as' -> a ∈ as
filterDoesNotAdd a []         .[]          f Refl pa (() , i)
filterDoesNotAdd a (b :: as)  as'          f eq   pa (ix , i)    with f b | filter f as | inspect (filter f) as
filterDoesNotAdd a (.a :: as) .(a :: as'') f Refl pa (FZ , Refl) | Yes _  | n' , as''   | [ pf ] = FZ , Refl
filterDoesNotAdd a (b :: as)  .(b :: as'') f Refl pa (FS ix , i) | Yes _  | n' , as''   | [ pf ] with filterDoesNotAdd a as as'' f pf pa (ix , i)
filterDoesNotAdd a (b :: as)  .(b :: as'') f Refl pa (FS ix , i) | Yes _  | n' , as''   | [ pf ] | (ix' , i') = FS ix' , i'
filterDoesNotAdd a (b :: as)  .as''        f Refl pa (ix , i)    | No nfa | n' , as''   | [ pf ] with filterDoesNotAdd a as as'' f pf pa (ix , i)
filterDoesNotAdd a (b :: as)  .as''        f Refl pa (ix , i)    | No nfa | n' , as''   | [ pf ] | (ix' , i') = FS ix' , i'

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

differenceRemoves : {A : Set} {n m n' : nat} {a : A} (as : vect A n) (bs : vect A m) (as' : vect A n') (aeq : equality A) -> difference aeq as bs == (n' , as') ->
  a ∈ bs -> not (a ∈ as')
differenceRemoves {A} {n} {m} {n'} {a} as bs as' aeq eq mem mem' = filterFilters a as as' (λ a -> decideNot (contains? aeq bs a)) eq mem' mem

differenceRetains : {A : Set} {n m n' : nat} {a : A} (as : vect A n) (bs : vect A m) (as' : vect A n') (aeq : equality A) -> difference aeq as bs == (n' , as') ->
  a ∈ as -> not (a ∈ bs) -> a ∈ as'
differenceRetains {A} {n} {m} {n'} {a} as bs as' aeq eq mem nmem = filterRetains a as as' (λ a -> decideNot (contains? aeq bs a)) eq nmem mem

differenceDoesNotAdd : {A : Set} {n m n' : nat} {a : A} (as : vect A n) (bs : vect A m) (as' : vect A n') (aeq : equality A) -> difference aeq as bs == (n' , as') ->
  a ∈ as' -> not (a ∈ bs) -> a ∈ as
differenceDoesNotAdd {A} {n} {m} {n'} {a} as bs as' aeq eq mem nmem = filterDoesNotAdd a as as' (λ a -> decideNot (contains? aeq bs a)) eq nmem mem

differenceRemainsSet : {A : Set} {n m n' : nat} {as : vect A n} {bs : vect A m} {as' : vect A n'} (aeq : equality A) -> difference aeq as bs == (n' , as') -> 
  isSet as -> isSet bs -> isSet as'
differenceRemainsSet {A} {n} {m} {n'} {as} {bs} {as'} aeq eq isa isb = filterRemainsSet as as' (λ a -> decideNot (contains? aeq bs a)) eq isa

removeRemoves : {A : Set} {n n' : nat} (as : vect A n) {a : A} (as' : vect A n') (aeq : equality A) -> remove aeq as a == (n' , as') -> not (a ∈ as')
removeRemoves {A} {n} {n'} as {a} as' aeq eq mem = filterFilters a as as' (λ a' -> decideNot (aeq a a')) eq mem Refl

removeRetains : {A : Set} {n n' : nat} (as : vect A n) (a b : A) (as' : vect A n') (aeq : equality A) -> remove aeq as a == (n' , as') -> not (a == b) -> b ∈ as -> b ∈ as'
removeRetains {A} {n} {n'} as a b as' aeq eq neq mem = filterRetains b as as' (λ a' -> decideNot (aeq a a')) eq neq mem

removeDoesNotAdd : {A : Set} {n n' : nat} (as : vect A n) (a b : A) (as' : vect A n') (aeq : equality A) -> remove aeq as a == (n' , as') -> not (a == b) -> b ∈ as' -> b ∈ as
removeDoesNotAdd {A} {n} {n'} as a b as' aeq eq neq mem = filterDoesNotAdd b as as' (λ a' -> decideNot (aeq a a')) eq neq mem 

removeRemainsSet : {A : Set} {n n' : nat} {as : vect A n} {a : A} {as' : vect A n'} (aeq : equality A) -> remove aeq as a == (n' , as') -> isSet as -> isSet as'
removeRemainsSet {A} {n} {n'} {as} {a} {as'} aeq eq isa = filterRemainsSet as as' (λ a' -> decideNot (aeq a a')) eq isa 

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
