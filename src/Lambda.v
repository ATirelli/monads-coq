From Coq Require Import List Lia Arith.
Require Import Monads.Computation.
Require Import Monads.Delay.

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
Definition Fail {A} := Return (@None A).
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
Lemma successful_computation: forall e, Eqp (interp ( bs (Const 2) e)) (rtrn (Some (Int 2))).
Proof. intros. eval_ (interp (bs (Const 2) e)). Qed.

Definition fail {A} := rtrn (@None A).

Lemma interp_fail: forall {A}, (interp (@Fail A)) = @fail A.
Proof. intros. eval_ (interp (@Fail A)). reflexivity. Qed. 

Lemma stuck_computation: forall e, Eqp (interp (bs (App (Const 1) (Const 2)) e)) fail.
Proof. 
intros. eval_ (interp (bs (App (Const 1) (Const 2)) e)).
eval_ (interp (_ <- bs (Const 2) e; (@Fail value))).
rewrite interp_fail. apply eqp_value with (a:=None).
- constructor. constructor. constructor.
- constructor. Qed.


CoFixpoint Never := @step (option value) Never.

Definition delta := Fun (App (Var 0) (Var 0)).
Definition omega := App delta delta.

Lemma infinite_computation: forall e, Eqp (interp (bs omega e)) Never.
Proof.  
intros. eval_ (interp (bs omega e)). 
eval_ (interp
(v2 <- bs delta e;
 match v2 with
 | Some t => Step (bs (App (Var 0) (Var 0)) (t :: e))
 | None => Fail
 end)).
eval_ (Never). constructor. cofix CIH. 
eval_ (interp
(Step (bs (App (Var 0) (Var 0)) (Clos (App (Var 0) (Var 0)) e :: e)))).
eval_ (Never). constructor. 
eval_ (interp (bs (App (Var 0) (Var 0)) (Clos (App (Var 0) (Var 0)) e :: e))).
eval_ (interp
(v2 <- bs (Var 0) (Clos (App (Var 0) (Var 0)) e :: e);
 match v2 with
 | Some t => Step (bs (App (Var 0) (Var 0)) (t :: e))
 | None => Fail
 end)). eval_ (Never). eval_ (Never). repeat constructor. apply CIH. Qed.





