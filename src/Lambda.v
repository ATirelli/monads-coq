Require Import Monads.Tactics.
Require Import Monads.Utils.
Require Import Monads.DelayMonad.
From Coq Require Import List Lia.

Definition OptPartial (A: Type):= Partial(option A).
Definition fail {A: Type}:= rtrn (@None A).
Print fail.

Definition ret {A: Type}(x: A):= rtrn (Some x).
Print ret.

CoFixpoint bind {A B: Type}(x: OptPartial A) (f: A -> OptPartial B): OptPartial B :=
match x with 
| rtrn None => fail
| rtrn (Some x) => f x
| step y => step (bind y f) end.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

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

CoFixpoint bs (t: term) (e:env) : OptPartial(value):=
match t with 
 | Const i => ret (Int i)
 | Var n => match (nth_error e n) with 
         | Some v => ret v
         | None => fail end
 | Fun a => ret (Clos a e) 
 | App a b => v1 <- bs a e ;; v2 <- bs b e ;; match v1 with 
                                          | Int r => fail
                                          | Clos g s => bs g (v2::s) end end.








