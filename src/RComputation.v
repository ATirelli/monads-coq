(** * The [Computation] Datatype *)

From Hammer Require Import Hammer.
Require Import JMeq.

(** In order to be abel to write a _productive_ big-step operational semantics function
we need to use an alternative definition of the Partiality datatype, namely the 
[Computation] datatype *)

CoInductive Computation (A: Type) : Type :=
| Return : A -> Computation A
| Bind : forall (B:Type), Computation B-> (B-> Computation A)-> Computation A.

Arguments Return {A}.
Arguments Bind {A B}.

(** We can retrieve the Step constructor as follows *)
Definition Step {A} (x: Computation A):= (Bind (Return tt) (fun (y: unit) => x)).
(** For later purposes, the following definition will also be handy *)
Definition Fail {A} := Return (@None A).

Notation "var <- c ; rest" :=
(Bind c (fun var => rest) )
(at level 60, right associativity).

(** In the proofs to follow, we will need a function 
to pull apart and reassemble a [Computation] in a way that provokes 
reduction of co-recursive calls, in the same way we did for [Partial]. *)
Definition frob {A}(x: Computation A) :=
match x with 
| Return y => Return y
| Bind y f => Bind y f end.

Lemma frob_eq {A}: forall (x: Computation A), x = frob x.
Proof. 
destruct x; reflexivity. Qed.
Ltac eval_ R :=  rewrite frob_eq with (x:=R); simpl; try (constructor).

(** * Equality for [Computation] *)
Inductive val {A}: Computation A -> A -> Prop :=
| value_return : forall a:A, val (Return a) a
| value_bind : forall (a: A) (B: Type) (b: B) (c: Computation B)
         (f: B -> Computation A), val c b -> val (f b) a -> val (Bind c f) a.

Lemma value_step {A}: forall (x:Computation A)(a:A), val x a -> val (Step x) a.
Proof. 
intros. induction H; sauto lq: on .
Qed.

Lemma val_determ: forall (A : Type) (ca :Computation A) a1, val ca a1 -> forall a2, val ca a2 -> a1 = a2.
intros A ca a1 H.
induction H;
 sauto lq: on dep: on.
 Qed.
 
(** A relation for animation of bind: *)
Inductive intR  { B: Type} : Computation B -> Computation B -> Prop := 
| bax1 (A : Type) (x: A) (f: A -> Computation B): 
     intR (Bind (Return x) f)  (f x)
| bax2 (A : Type) (f: A -> Computation B) (x: Computation A): 
    intR ( Bind (Step x) f)  (Step (Bind x f)).

(** how do we make in an equivalence relation? Just add constructor for reflex etc? *)

(*
 CoInductive Eqb {A} : Computation A -> Computation A -> Prop :=
| eqpr_value : forall (x y:Computation A)(a1 a2:A) , 
     intR a1 a2 -> val x a1 -> val y a1 -> (Eqb x y).
| eqpr_bind: forall (A: Type) (x y: Computation A) (f g: A -> Computation A) (b: A),
 EqpR R x y -> EqpR R (f b) (g b) -> EqpR R (Bind x f) (Bind y g).
*)




(* CoInductive EqpR {A} (R : A -> A -> Prop) : Computation A -> Computation A -> Prop :=
| eqpr_value : forall (x y:Computation A)(a1 a2:A) , 
     R a1 a2 -> val x a1 -> val y a1 -> (EqpR R x y)
| eqpr_bind: forall (A: Type) (x y: Computation A) (f g: A -> Computation A) (b: A),
 EqpR R x y -> EqpR R (f b) (g b) -> EqpR R (Bind x f) (Bind y g).
*)

 
CoInductive Eqp {A}: Computation A -> Computation A -> Prop :=
| eqp_value : forall (x y:Computation A)(a:A), val x a -> val y a -> (Eqp x y)
| eqp_bind: forall (B: Type) (x y: Computation B) (f g: B -> Computation A) (b: B),
Eqp x y ->  Eqp (f b) (g b) -> Eqp (Bind x f) (Bind y g).

Lemma eqp_step : forall {A} (x y:Computation A), Eqp x y -> Eqp (Step x) (Step y).
Proof.
sauto lq: on .
Qed.

Ltac apply_eqp_step := constructor; now auto;
apply eqp_value with (a:=tt); constructor.

Lemma eqp_equal_ret: forall {A} (x : A), Eqp (Return x) (Return x).
Proof. 
sauto lq: on .
Qed.

(** Since [bind] is now a constructor and _not_ a function, we need to find a way 
to _animate_ it: we use two axioms, which prescribe how [bind] work on a computation *)
Axiom Bind_On_Return: forall (A B: Type) (x: A) (f: A -> Computation B), 
Bind (Return x) f = f x.

Axiom Bind_On_Step: forall (A B: Type) (f: A -> Computation B) (x: Computation A), 
Bind (Step x) f = Step (Bind x f).

