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
| BisimStepL : forall x y, bisim x y -> bisim (Step x) y
| BisimStepR : forall x y, bisim x y -> bisim  x (Step y)
| BisimFail: bisim Fail Fail.
Hint Resolve BisimRtrn : core.
(*Hint Resolve BisimBind : core.
Hint Resolve BisimStep : core.
Hint Resolve BisimStepL : core.
Hint Resolve BisimStepR : core.
Hint Resolve BisimFail : core.*)




(*Theorem bisim_refl {A}: forall (a: Computation A), bisim a a.
Proof. cofix CIH.  intros. destruct a; constructor; constructor; apply CIH. Qed.
Hint Resolve bisim_refl : core.
Theorem bisim_symm {A}: forall (a b: Computation A), bisim a b -> bisim b a.
Proof. cofix CIH. intros. inversion H; subst; constructor.
-  inversion H; 
repeat (apply CIH in H0; assumption;
  apply CIH in H0; assumption).
apply CIH in H0; assumption. apply CIH in H0; assumption. Qed.
Hint Resolve bisim_symm : core.*)

Theorem bisim_trans {A}: forall (a b c: Computation A), bisim a b -> bisim b c -> bisim a c.
Proof. cofix CIH. intros. inversion H. subst. inversion H0; subst.
- auto. 
- 
-     as []. inversion H0. inversion H H0; subst; inversion H0; subst.
- auto. 
- inversion H; subst.s
- inversion H; subst. auto. 
- 



 inversion H. subst. inversion H0. destruct H0. 
- auto.
- constructor. apply CIH with (b:=  y); auto. 
- constructor. apply CIH with (b:=  y); auto.
- inversion H. H0. 
-  destruct H0.

- constructor.  apply bisim_refl.
- apply bisim_refl.
- constructor; assumption.
- constructor; assumption.
- constructor; assumption.
- constructor.
- assumption.
- constructor. apply BisimStepR in H. apply CIH with (b:= Step y); assumption.
- constructor. apply CIH with (b:= y); assumption.  
(*- rewrite (frob_eq x) in *. rewrite (frob_eq c) in *. apply CIH with (b:= Step y). *)
-  destruct c. destruct x. constructor. inversion H0. subst.

inversion H0. subst. apply  apply CIH with (a:=x) in H0. assumption.  destruct c; destruct x. apply BisimStepR in H. apply CIH with (b:= Step y); assumption. Guarded.
+ 
 destruct H0. 
* inversion H0.

rewrite (frob_eq x) in *. apply BisimStepR in H. apply CIH with (b:= Step y); assumption. 
- assumption. Qed.

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

Lemma delta_sim: forall e, (bisim (bs omega e)  
(Step (bs (App (Var 0) (Var 0)) (Clos (App (Var 0) (Var 0)) e :: e)))).
Proof. Admitted.

Lemma bisim_infinite: forall e, bisim (bs omega e) never.
Proof. cofix CIH. intros. rewrite frob_eq with (x:=bs omega e). simpl. 
rewrite frob_eq with (x:=bs delta e). simpl. rewrite Bind_On_Return. 
rewrite Bind_On_Return. constructor. 
assert (bisim (bs omega e) (bs (App (Var 0) (Var 0))
     (Clos (App (Var 0) (Var 0)) e :: e))).
- rewrite frob_eq with (x:=bs omega e). simpl. rewrite frob_eq with (x:=bs delta e). simpl. rewrite Bind_On_Return. 
rewrite Bind_On_Return. constructor. apply bisim_refl.
- apply bisim_trans with (b:=(bs omega e)). apply bisim_symm in H. assumption. apply CIH.  Qed.








