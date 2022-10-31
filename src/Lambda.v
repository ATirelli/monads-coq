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
Ltac eval_ R :=  rewrite frob_eq with (x:=R); simpl; try (constructor).

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
| eqp_bind: forall (B: Type) (x y: Computation B) (f g: B -> Computation A) (b: B),
Eqp x y ->  Eqp (f b) (g b) -> Eqp (Bind x f) (Bind y g).

Lemma eqp_step : forall {A} (x y:Computation A), Eqp x y -> Eqp (Step x) (Step y).
Proof. intros. eval_ (Step x). now auto. apply eqp_value with (a:=tt); constructor. assumption. Qed.

Lemma eqp_equal_ret: forall {A} (x : A), Eqp (Return x) (Return x).
Proof. intros. apply eqp_value with (a:=x); constructor. Qed.


Lemma eqp_equal: forall {A} (x :Computation A), Eqp x x.
Proof. cofix CIH. intros. destruct x.
- apply eqp_value with (a:=a); constructor.
- eapply eqp_bind. apply CIH. apply CIH. Guarded. Admitted. 

Lemma eqp_successful: forall e, Eqp ( bs (Const 2) e) (ret (Int 2)).
Proof. intros. eval_ (bs (Const 2) e). apply eqp_equal_ret.  Qed.

Lemma eqp_failure: forall e, Eqp (bs (App (Const 1) (Const 2)) e) Fail.
Proof. intros. eval_ (bs (App (Const 1) (Const 2)) e).
eval_ (bs (Const 1) e).
eval_ (bs (Const 2) e). rewrite Bind_On_Return. 
rewrite Bind_On_Return. apply eqp_equal_ret. Qed.

CoFixpoint Never := @Step (option value) Never.

Lemma eqp_never:  Eqp (Step Never) Never.
Proof. cofix CIH. rewrite frob_eq with (x:=Never). simpl. constructor. now auto.
apply eqp_value with (a:=tt); constructor. assumption. Qed.

Definition delta := Fun (App (Var 0) (Var 0)).
Definition omega := App delta delta.

Lemma eqp_infinite: forall e, Eqp (bs omega e) Never.
Proof.  intros. eval_ (bs omega e). 
eval_ (bs delta e). rewrite Bind_On_Return. 
rewrite Bind_On_Return. eval_ (Never). now auto.
apply eqp_value with (a:=tt); constructor. cofix CIH. 
eval_ (bs (App (Var 0) (Var 0)) (Clos (App (Var 0) (Var 0)) e :: e)). 
eval_ (bs (Var 0) (Clos (App (Var 0) (Var 0)) e :: e)). rewrite Bind_On_Return. 
rewrite Bind_On_Return. eval_ (Never). now auto.
apply eqp_value with (a:=tt); constructor. apply CIH. Qed.







