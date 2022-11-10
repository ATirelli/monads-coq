From Coq Require Import List Lia Arith.
Require Import Monads.Computation.

(** * Untyped l-calculus with De Brujin indices *)
Definition const :=nat. 

Inductive term: Type :=
| Var: nat -> term
| Const: const -> term
| Fun: term -> term
| App: term -> term -> term.

Inductive value: Type :=
| Int: const -> value
| Clos: term -> list value -> value.

Definition env := list value.
Definition ret {A} (x:A) := Return (Some x).

(** * BSOS using [Computation] *)
(** The following [CoFixpoint] function [bs] implements the big-step operational semantics
for the untyped l-calculus with constants, where we can have three different scenarios: 
- successful computation
- stuck computation 
- non terminating computation 
By composing [Computation] with [option] (which is also a [Monad]) we can account for all these behaviours at once *)
CoFixpoint bs (t: term) (e:env): Computation (option value) :=
match t with 
 | Const i => ret (Int i)
 | Var n   => match (nth_error e n) with 
           | Some v => ret v
           | None   => Fail end
 | Fun a => ret (Clos a e)
 | App a b => v1 <- bs a e ; v2 <- bs b e ; match v1 with 
                                    | None            => Fail
                                    | Some (Int n)    => Fail 
                                    | Some (Clos x y) => match v2 with 
                                                          | None   => Fail 
                                                          | Some t => Step (bs x (t::y)) end end end .


(** * Examples*)
Lemma eqp_successful: forall e, Eqp ( bs (Const 2) e) (ret (Int 2)).
Proof. 
intros. eval_ (bs (Const 2) e). apply eqp_equal_ret.  Qed.

Lemma eqp_failure: forall e, Eqp (bs (App (Const 1) (Const 2)) e) Fail.
Proof. 
intros. eval_ (bs (App (Const 1) (Const 2)) e).
eval_ (bs (Const 1) e).
eval_ (bs (Const 2) e). rewrite Bind_On_Return. 
rewrite Bind_On_Return. apply eqp_equal_ret. Qed.

CoFixpoint Never := @Step (option value) Never.

Lemma eqp_never:  Eqp (Step Never) Never.
Proof. 
cofix CIH. rewrite frob_eq with (x:=Never). simpl.  constructor. now auto.
apply eqp_value with (a:=tt); constructor. assumption. Qed.

Definition delta := Fun (App (Var 0) (Var 0)).
Definition omega := App delta delta.

Lemma eqp_infinite: forall e, Eqp (bs omega e) Never.
Proof.  
intros. eval_ (bs omega e). 
eval_ (bs delta e). rewrite Bind_On_Return. 
rewrite Bind_On_Return. eval_ (Never). now auto.
apply eqp_value with (a:=tt); constructor. cofix CIH. 
eval_ (bs (App (Var 0) (Var 0)) (Clos (App (Var 0) (Var 0)) e :: e)). 
eval_ (bs (Var 0) (Clos (App (Var 0) (Var 0)) e :: e)). rewrite Bind_On_Return. 
rewrite Bind_On_Return. eval_ (Never). now auto.
apply eqp_value with (a:=tt); constructor. apply CIH. Qed.






