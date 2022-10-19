Require Import Monads.Tactics.
Require Import Monads.Utils.
Require Import Monads.DelayMonad.
From Coq Require Import List Lia Arith.

CoInductive Computation (A:Type) : Type :=
| Return : A -> Computation A
| Bind : forall (B:Type), Computation B-> (B-> Computation A)-> Computation A.
Arguments Return {A}.
Arguments Bind {A B}.
Notation "c >>= f" := (Bind f c) (at level 20).
Notation "var <- c ; rest" :=
(Bind c (fun var => rest) )
(at level 60, right associativity).


Definition OptPartial (A: Type):= Partial (option A).
Definition fail {A: Type}:= rtrn (@None A).
Print fail.

Definition ret {A: Type}(x: A):= rtrn (Some x).
Print ret.

CoFixpoint bind {A B: Type}(x: OptPartial A) (f: A -> OptPartial B): OptPartial B :=
match x with 
| rtrn None => fail
| rtrn (Some x) => f x
| step y => step (bind y f) end.

Definition CompPartial (A: Type) := Computation (option A).
Parameter const: Type.

Inductive term: Type :=
  | Var: nat -> term
  | Const: const -> term
  | Fun: term -> term
  | App: term -> term -> term.

Inductive value: Type :=
  | Int: const -> value
  | Clos: term -> list value -> value.

Definition env := list value.
Definition Fail {A: Type}:= Return (@None A).


CoFixpoint bs (t: term) (e:env): (CompPartial value) :=
match t with 
 | Const i => Return (Some (Int i))
 | Var n => match (nth_error e n) with 
         | Some v => Return (Some v)
         | None => Fail end
 | Fun a => Return (Some (Clos a e)) 
 | App a b => v1 <- bs a e ; v2 <- bs b e ; match v1 with 
                                          | None => Fail
                                          | Some(Int r) => Fail
                                          | Some(Clos g s) => match v2 with 
                                                      | None => Fail 
                                                      | Some z => bs g (z::s) end end end .








