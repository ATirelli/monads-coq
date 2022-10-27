Require Import Monads.Tactics.
Require Import Monads.Utils.

From Coq Require Import List Lia Arith.

CoInductive Computation (A:Type) : Type :=
| Return : A -> Computation A
| Bind : forall (B:Type), Computation B-> (B-> Computation A)-> Computation A
| Fail
| Step : Computation A -> Computation A.
Arguments Return {A}.
Arguments Bind {A B}.
Arguments Step {A}.
Arguments Fail {A}.

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
| Bind y f => Bind y f
| Fail     => Fail
| Step t   => Step t end.

Lemma frob_eq {A}: forall (x: Computation A), x = frob x.
Proof. destruct x; reflexivity. Qed.

CoInductive bisim {A} : Computation A -> Computation A -> Prop :=
| BisimRtrn   : forall x, bisim (Return x) (Return x)
| BisimBind  : forall (B: Type) (f: B -> Computation A) x, bisim (Bind x f) (Bind x f)
| BisimStep : forall x y, bisim x y -> bisim (Step x) (Step y)
| BisimStepL : forall x y, bisim x y -> bisim (Step x) y
| BisimStepR : forall x y, bisim x y -> bisim  x (Step y)
| BisimFail: bisim Fail Fail.

Theorem bisim_refl {A}: forall (a: Computation A), bisim a a.
Proof. cofix CIH.  intros. destruct a; constructor; constructor; apply CIH. Qed.

Theorem bisim_symm {A}: forall (a b: Computation A), bisim a b -> bisim b a.
Proof. cofix CIH. intros. inversion H; subst; constructor.
-  inversion H; 
repeat (apply CIH in H0; assumption;
  apply CIH in H0; assumption).
- apply CIH in H0; assumption.
- apply CIH in H0; assumption. Qed.


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

CoFixpoint bs (t: term) (e:env): (Computation value) :=
match t with 
 | Const i => Return (Int i)
 | Var n   => match (nth_error e n) with 
           | Some v => Return v
           | None   => Fail end
 | Fun a => Return (Clos a e) 
 | App a b => v1 <- bs a e ; v2 <- bs b e ; match v1 with 
                                    | Int n    => Fail 
                                    | Clos x y => Step (bs x (v2::y))
                                                   end end.

CoFixpoint never := @Step value never.

Lemma bisim_successful: forall e, bisim ( bs (Const 2) e) (Return (Int 2)).
Proof. intros. rewrite frob_eq with (x:=bs (Const 2) e). simpl. constructor. Qed.

Lemma bisim_fail: forall e, bisim (bs (App (Const 1) (Const 2)) e) Fail.
Proof. intros. rewrite frob_eq with (x:=bs (App (Const 1) (Const 2)) e). simpl. 
rewrite frob_eq with (x:=bs (Const 1) e). rewrite frob_eq with (x:=bs (Const 2) e).
simpl. rewrite Bind_On_Return. rewrite Bind_On_Return. constructor. Qed.

Definition delta := Fun (App (Var 0) (Var 0)).
Definition omega := App delta delta.

Lemma bisim_infinite: forall e, bisim (bs omega e) never.
Proof.  intros. rewrite frob_eq with (x:=bs omega e).  simpl. 
rewrite frob_eq with (x:=bs delta e). simpl. rewrite Bind_On_Return. 
rewrite Bind_On_Return. constructor. cofix CIH. 
 rewrite frob_eq with (x:=(bs (App (Var 0) (Var 0)) (Clos (App (Var 0) (Var 0)) e :: e))). simpl. 
 rewrite frob_eq with (x:=bs (Var 0) (Clos (App (Var 0) (Var 0)) e :: e)). simpl. rewrite Bind_On_Return. 
rewrite Bind_On_Return. constructor. apply CIH. Qed.

Inductive val {A}: Computation A -> A -> Prop :=
 value_return : forall a:A, val (Return a) a
| value_step : forall (x:Computation A)(a:A), val x a -> val (Step x) a.


CoInductive Eqp {A}: Computation A -> Computation A -> Prop :=
 eqp_value : forall (x y:Computation A)(a:A), val x a -> val y a -> (Eqp x y)
| eqp_step : forall (x y:Computation A), Eqp x y -> Eqp (Step x) (Step y)
| eqp_fail: Eqp Fail Fail.


Theorem eqp_refl_return {A}: forall (x: A), Eqp (Return x) (Return x).
Proof.  intros. apply eqp_value with (a:=x).  constructor. constructor. Qed.

Lemma eqp_successful: forall e, Eqp ( bs (Const 2) e) (Return (Int 2)).
Proof. intros. rewrite frob_eq with (x:=bs (Const 2) e). simpl. apply eqp_refl_return. Qed.

Lemma eqp_failure: forall e, Eqp (bs (App (Const 1) (Const 2)) e) Fail.
Proof. intros. rewrite frob_eq with (x:=bs (App (Const 1) (Const 2)) e). simpl.
rewrite frob_eq with (x:=bs (Const 1) e).
rewrite frob_eq with (x:=bs (Const 2) e). simpl. rewrite Bind_On_Return. rewrite Bind_On_Return. constructor. Qed.

Lemma eqp_never:  Eqp (Step never) never.
Proof. cofix CIH. rewrite frob_eq with (x:=never). simpl. constructor. assumption. Qed.

Lemma eqp_infinite: forall e, Eqp (bs omega e) never.
Proof.  intros. rewrite frob_eq with (x:=bs omega e).  simpl. 
rewrite frob_eq with (x:=bs delta e). simpl. rewrite Bind_On_Return. 
rewrite Bind_On_Return. rewrite frob_eq with (x:=never). simpl. constructor. cofix CIH. 
 rewrite frob_eq with (x:=(bs (App (Var 0) (Var 0)) (Clos (App (Var 0) (Var 0)) e :: e))). simpl. 
 rewrite frob_eq with (x:=bs (Var 0) (Clos (App (Var 0) (Var 0)) e :: e)). simpl. rewrite Bind_On_Return. 
rewrite Bind_On_Return.  rewrite frob_eq with (x:=never). simpl. constructor. apply CIH. Qed.







