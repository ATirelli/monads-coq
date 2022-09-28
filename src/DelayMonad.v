Add LoadPath "./" as Monads .
Require Import Monads.FunctorApplicativeMonad.

Require Import Relations.
Require Import Arith.
Require Import List.
Require Import Max.


Set Implicit Arguments.

CoInductive Partial A: Type :=
|  rtrn : A -> Partial A
| step : Partial A -> Partial A.

CoFixpoint partial_map  {a b} (f : a -> b) (r : Partial a): Partial b := 
match r with 
| rtrn x => rtrn (f x)
| step y => step (partial_map f y) end.


CoFixpoint partial_apply {a b} (f : Partial (a -> b)) (x : Partial a): Partial b := 
match x with 
 | rtrn y => match f with 
                              | rtrn g => rtrn (g y)
                              | step t => step (partial_apply t x) end
| step r => step (partial_apply f r) end.

CoFixpoint partial_bind {a b} (f: a -> Partial b) (x: Partial a): Partial b := 
match x with  
| rtrn y => f y 
| step t => step (partial_bind f t) end.

#[program]
Instance partial_Functor: Functor (Partial) :=
  { map := @partial_map  
  }.


Next Obligation. Admitted.
Next Obligation. Admitted.





















