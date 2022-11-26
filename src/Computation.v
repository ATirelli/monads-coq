(** * The [Computation] Datatype *)

(** In order to be able to write a _productive_ big-step operational semantics function
we need to use an alternative definition of the Partiality datatype, namely the 
[Computation] datatype *)

Require Import Monads.Delay.

CoInductive Computation (A: Type) : Type :=
| Return : A -> Computation A
| Bind : forall (B:Type), Computation B-> (B-> Computation A)-> Computation A.

Arguments Return {A}.
Arguments Bind {A B}.


(** We can retrieve the Step constructor as follows *)
Definition Step {A} (x: Computation A):= (Bind (Return tt) (fun (y: unit) => x)).

Notation "var <- c ; rest" :=
(Bind c (fun var => rest) )
(at level 60, right associativity).

(** Since [Bind] is a constructor a not a function, we need a way to [animate] terms 
of type [Computation A] and the (delayed) computations that they encode. One way to achieve is 
is by writing an _interpreter_ that maps objects of type [Computation A] to 
objects of type [Partial A]. *)

CoFixpoint interp {A: Type} (m: Computation A) : Partial A :=
  match m with
  | Return v => rtrn v
  | Bind (Return v) f => step (interp (f v))
  | Bind (Bind a f) g => step (interp (Bind a (fun v => Bind (f v) g))) end.
