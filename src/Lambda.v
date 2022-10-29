From Coq Require Import List Lia Arith.

CoInductive Computation (A: Type) : Type :=
| Return : A -> Computation A
| Bind : forall (B:Type), Computation B-> (B-> Computation A)-> Computation A.

Arguments Return {A}.
Arguments Bind {A B}.

Definition Fail {A} := Return (@None A).
Definition Step {A} (x: Computation A):= (Bind (Return tt) (fun (y: unit) => x)).

Axiom Bind_On_Return: forall (A B: Type) (x: A) (f: A -> Computation B), 
Bind (Return x) f = f x.

Axiom Bind_On_Step: forall (A B: Type) (f: A -> Computation B) (x: Computation A), 
Bind (Step x) f = Step (Bind x f).

Notation "var <- c ; rest" :=
(Bind c (fun var => rest) )
(at level 60, right associativity).

Definition frob {A}(x: Computation A) :=
match x with 
| Return y => Return y
| Bind y f => Bind y f end.

Lemma frob_eq {A}: forall (x: Computation A), x = frob x.
Proof. destruct x; reflexivity. Qed.

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
Definition CompFail (A: Type) := Computation (option A).

CoFixpoint bs (t: term) (e:env): (CompFail value) :=
match t with 
 | Const i => Return (Some (Int i))
 | Var n   => match (nth_error e n) with 
           | Some v => Return (Some v)
           | None   => Fail end
 | Fun a => Return (Some (Clos a e))
 | App a b => v1 <- bs a e ; v2 <- bs b e ; match v1 with 
                                    | None     => Fail
                                    | Some (Int n)    => Fail 
                                    | Some (Clos x y) => match v2 with 
                                                          | None => Fail 
                                                          | Some t => Step (bs x (t::y)) end

CoFixpoint never := @Step value never.

Inductive val {A}: Computation A -> A -> Prop :=
| value_return : forall a:A, val (Return a) a
| value_bind : forall (a: A) (B: Type) (b: B) (c: Computation B)
         (f: B -> Computation A), val c b -> val (f b) a -> val (Bind c f) a.

Lemma value_step {A}: forall (x:Computation A)(a:A), val x a -> val (Step x) a.
Proof. intros. induction H. 
- unfold Step. rewrite Bind_On_Return. constructor.
- unfold Step. rewrite Bind_On_Return. apply value_bind with (b:=b); assumption. Qed.


CoInductive Eqp {A}: Computation A -> Computation A -> Prop :=
| eqp_value : forall (x y:Computation A)(a:A), val x a -> val y a -> (Eqp x y)
| eqp_step : forall (x y:Computation A), Eqp x y -> Eqp (Step x) (Step y)
| eqp_equal: forall (x :Computation A), Eqp x x.


Definition ret {A} (x:A) := Return (Some x).

Lemma eqp_successful: forall e, Eqp ( bs (Const 2) e) (ret (Int 2)).
Proof. intros. rewrite frob_eq with (x:=bs (Const 2) e). simpl. constructor. Qed.

Lemma eqp_failure: forall e, Eqp (bs (App (Const 1) (Const 2)) e) Fail.
Proof. intros. rewrite frob_eq with (x:=bs (App (Const 1) (Const 2)) e). simpl.
rewrite frob_eq with (x:=bs (Const 1) e).
rewrite frob_eq with (x:=bs (Const 2) e). simpl. rewrite Bind_On_Return. rewrite Bind_On_Return. constructor. Qed.

CoFixpoint Never := @Step (option value) Never.

Lemma eqp_never:  Eqp (Step Never) Never.
Proof. cofix CIH. rewrite frob_eq with (x:=Never). simpl. constructor. assumption. Qed.

Definition delta := Fun (App (Var 0) (Var 0)).
Definition omega := App delta delta.

Lemma eqp_infinite: forall e, Eqp (bs omega e) Never.
Proof.  intros. rewrite frob_eq with (x:=bs omega e).  simpl. 
rewrite frob_eq with (x:=bs delta e). simpl. rewrite Bind_On_Return. 
rewrite Bind_On_Return. rewrite frob_eq with (x:=Never). simpl. constructor. cofix CIH. 
rewrite frob_eq with (x:=(bs (App (Var 0) (Var 0)) (Clos (App (Var 0) (Var 0)) e :: e))). simpl. 
rewrite frob_eq with (x:=bs (Var 0) (Clos (App (Var 0) (Var 0)) e :: e)). simpl. rewrite Bind_On_Return. 
rewrite Bind_On_Return.  rewrite frob_eq with (x:=Never). simpl. constructor. apply CIH. Qed.







