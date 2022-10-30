Set Implicit Arguments.

Require Import Monads.Tactics.
Require Import Monads.FunctorApplicativeMonad.


CoInductive Partial A: Type :=
| rtrn : A -> Partial A
| step : Partial A -> Partial A.

CoFixpoint map  {a b} (f : a -> b) (x : Partial a): Partial b := 
match x with 
| rtrn y => rtrn (f y)
| step t => step (map f t) end.


CoFixpoint apply {a b} (f : Partial (a -> b)) (x : Partial a): Partial b := 
match x with 
 | rtrn y => match f with 
                              | rtrn g => rtrn (g y)
                              | step t => step (apply t x) end
| step r => step (apply f r) end.

CoFixpoint bind {a b} (f: a -> Partial b) (x: Partial a): Partial b := 
match x with  
| rtrn y => f y 
| step t => step (bind f t) end.

Definition ret {a} (x: a): Partial a := rtrn x.


CoInductive Diverge {A}: Partial A -> Prop :=
  diverge : forall x:Partial A, Diverge x -> Diverge (step x).


Definition frob {A}(x: Partial A) :=
match x with 
| rtrn y => rtrn y
| step t => step t end.

Lemma frob_eq {A}: forall (x: Partial A), x = frob x.
Proof. destruct x; reflexivity. Qed.


Inductive val {A}: Partial A -> A -> Prop :=
| value_return : forall a:A, val (rtrn a) a
| value_bind : forall (a: A) (x: Partial A), val x a -> val (step x) a.


CoInductive Eqp {A}: Partial A -> Partial A -> Prop :=
| eqp_value : forall (x y:Partial A)(a:A), val x a -> val y a -> (Eqp x y)
| eqp_step : forall (x y:Partial A), Eqp x y -> Eqp (step x) (step y).
Notation "^ a " := (rtrn a) (at level 0).
Notation "|> x" := (step x) (at level 0, right associativity).

Notation "x ~> a" := (val x a) (at level 71).
Notation "x ~^" := (Diverge x) (at level 71).

Notation "x [=] y" := (Eqp x y) (at level 70).

Lemma partial_basic_1 : forall {A} (x y:(Partial A))(a:A), x~>a -> y~>a -> x [=] y.
Proof. intros. apply eqp_value with (a:=a); assumption. Qed.

Lemma partial_basic_2 : forall {A} (x y:(Partial A)), x~^ -> y~^ -> x [=] y.
Proof.
cofix H.
intros  A x y Hx Hy.
inversion_clear Hx; inversion_clear Hy.
apply eqp_step.
apply H; assumption.
Qed.

Lemma partial_basic_5 : forall {A} (x:(Partial A))(a:A), x~>a -> x[=] ^a.
Proof.
intros; apply eqp_value with (a:=a); try assumption.
apply value_return.
Qed.

Lemma partial_basic_13 : forall {A} (a1 a2:A), ^a1~>a2 -> a1=a2.
Proof.
intros A a1 a2 H; inversion_clear H; trivial.
Qed.

Lemma partial_basic_6 : forall {A} (x:(Partial A))(a:A), x[=]^a -> x~>a.
Proof.
intros A x a H; inversion_clear H.
rewrite partial_basic_13 with (a1:=a) (a2:=a0); assumption.
Qed.

Lemma partial_basic_14 : forall {A} (x:Partial A), x [=] x.
Proof.
Admitted. 

Lemma eqp_symm : forall {A} (x y:Partial A), x [=] y -> y [=] x.
Proof.
Admitted. 

Lemma partial_basic_7 : forall {A} (x:(Partial A))(a:A), |>x~>a -> x~>a.
Proof.
intros A x a H; inversion_clear H; assumption.
Qed.

Lemma partial_basic_11 : forall {A} (x y:Partial A), x [=] y -> x [=] |>y.
Proof.
cofix H.
intros A x y Heq; inversion_clear Heq.
apply eqp_value with (a:=a); [idtac|apply value_bind]; assumption.
apply eqp_step; apply H; assumption.
Qed.

Lemma partial_basic_12 : forall {A} (x y:Partial A), |>x [=] y -> x[=]y.
Proof.
intros A x y Heq;inversion_clear Heq.
apply eqp_value with (a:=a); [apply partial_basic_7|idtac]; assumption.
apply partial_basic_11; assumption.
Qed.

Lemma partial_basic_3 : forall {A} (x y:(Partial A))(a:A), x~>a -> x [=] y -> y~>a.
Proof.
intros A x y a Hx; elim Hx.
intros a0 H0; apply partial_basic_6.
apply eqp_symm; assumption.

intros x0 a0 H0 IH Heq.
apply IH; apply partial_basic_12; assumption.
Qed.

(*Lemma partial_basic_8 : forall {A} (x:Partial A), |>x~^ -> x~^.
Proof.
intros A x Hx; inversion_clear Hx.
assumption.
Qed.

Lemma partial_basic_9 : forall {A} (x:(Partial A))(a:A), x~>a -> ~ x~^.
Proof.
intros  A x a H; elim H.
intros a0 H0; inversion H0.

intros x0 a0 H0 IH H1.
apply IH; apply partial_basic_8; assumption.
Qed.

Lemma partial_basic_4 : forall {A} (x y:Partial A), x~^ -> x [=] y -> y~^.
Proof.
cofix H.
intros A x y Hx Heq.
generalize Hx; inversion_clear Heq.
elim partial_basic_9 with (x:=x)(a:=a); assumption.
intro H1; apply diverge.
apply H with (x:=x0); [apply partial_basic_8|idtac]; assumption.
Qed.

Lemma partial_basic_10 : forall {A} (x y:(Partial A))(a:A), x~>a -> y~^ -> ~ x[=]y.
Proof.
intros A x y a H; elim H.
intros a0 H0 H1.
apply partial_basic_9 with (x:=y)(a:=a0).
apply partial_basic_6; apply eqp_symm; assumption.
assumption.

intros x0 a0 H0 IH H1 H2; apply IH.
assumption.
apply partial_basic_12; assumption.
Qed.
*)
Lemma eqp_trans : forall {A} (x y z:Partial A), x [=] y -> y [=] z -> x [=] z.
Proof.
cofix H.
intros A x y z Hxy; inversion_clear Hxy.
intro Hyz.
apply partial_basic_1 with (a:=a); [assumption|idtac].
apply partial_basic_3 with (x:=y); assumption.

intro Hyz; inversion_clear Hyz.
apply partial_basic_1 with (a:=a); [idtac|assumption].
apply partial_basic_3 with (x:=|>y0); [assumption|apply eqp_step].
apply eqp_symm; assumption.

apply eqp_step; apply H with (y:=y0); assumption.
Qed.

Lemma eqp_refl: forall {A} (x: Partial A), Eqp x x. 
Proof. cofix CIH. intros.  destruct x. 
apply eqp_value with (a:=a); constructor. constructor. apply CIH. Qed. 

Lemma eqp_sym: forall {A} (x y: Partial A), Eqp x y -> Eqp y x. 
Proof. cofix CIH. intros. inversion H. 
- apply eqp_value with (a:=a); assumption. 
- constructor. apply CIH in H0. assumption. Qed.

Lemma val_det: forall {A}  (a b: A) (x: Partial A), val x a -> val x b -> a = b. 
Proof. intros. induction H. 
- inversion H0. auto. 
- inversion H0. apply IHval in H2. assumption. Qed.  


Section park_principle.
Variable A : Type.
Variable P : Partial A -> Partial A -> Prop.

Hypothesis H : forall m1 m2, P m1 m2
-> (exists a, (val m1 a) /\ (val m2 a)) \/
   (exists x1, exists x2, (m1 = step x1) /\ (m2 = step x2) /\ (P x1 x2)) \/
   (m1 = m2).


Theorem park_principle : forall m1 m2, P m1 m2 -> Eqp m1 m2.
Proof. cofix CIH.
intros. destruct m1. destruct m2. 
apply H in H0.
destruct H0.
inversion H0. destruct  H1. inversion H1. inversion H2. auto. 
apply eqp_refl.
destruct H0. inversion H0. inversion H1.
destruct H2. destruct H3. inversion H2.
rewrite H0. apply eqp_refl.

apply H in H0. destruct H0. destruct H0. destruct H0. 
apply eqp_value with (a:=x); assumption.
destruct H0. destruct H0. destruct H0. destruct H0. inversion H0.
inversion H0.

apply H in H0. destruct H0. destruct H0. destruct H0. 
apply eqp_value with (a:=x); assumption.
destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
rewrite H0. rewrite H1. constructor. apply CIH. assumption. 

rewrite H0. apply eqp_refl. Qed.
End park_principle.

Theorem partial_eqp_frob : forall A (m1 m2 : Partial A),
  Eqp (frob m1) (frob m2) -> Eqp m1 m2.
Proof. intros. assert (frob m1 = m1). rewrite frob_eq. reflexivity.
assert (frob m2 = m2). rewrite frob_eq. reflexivity. 
rewrite <- H0. rewrite <- H1. assumption. Qed.

Ltac eval_ R :=  rewrite frob_eq with (x:=R); simpl; try (apply eqp_refl).
Ltac finish_with R := try constructor; try (apply eqp_refl); apply R.

(* Functor axioms *) 
Theorem map_id_eq: forall A (m: Partial A), Eqp (map id m) m.
cofix CIH.  destruct m. 
- eval_ (map id (rtrn a)).
- eval_ (map id (step m)). finish_with  CIH. Qed.

Theorem map_assoc: forall A B C (m: Partial A) (f: A -> B) (g: B -> C), 
Eqp (map (g <<< f) m) (map g (map f m)).
Proof. cofix CIH. destruct m. 
- intros. eval_(map (f >>> g) (rtrn a)).
eval_ (map g (map f (rtrn a))). 
- intros. rewrite frob_eq with (x:=map (f >>> g) (step m)).
eval_ (map g (map f (step m))). finish_with CIH. Qed.

Definition pure A (x: A):= rtrn x.
Lemma partial_applicative_identity: forall  {a} (v : Partial a), 
Eqp (apply (pure id) v) v.
Proof. cofix CIH. destruct v.
- intros. eval_ (apply (pure id) (rtrn a0)).
- intros. eval_ (apply (pure id) (step v)). finish_with CIH. Qed. 

Notation "f <*> g" := (apply f g) (at level 28, left associativity) .

Lemma partial_applicative_composition: forall {a b c}  (t : Partial (b -> c)) 
(v : Partial (a -> b)) (w : Partial a)
    , Eqp (pure compose <*> t <*> v <*> w)  ((t) <*> (v <*> w)).
Proof. cofix CIH. intros.
destruct w. destruct v. destruct t.
- eval_ (pure compose <*> rtrn c0 <*> rtrn b0 <*> rtrn a0).
eval_ (rtrn c0 <*> (rtrn b0 <*> rtrn a0)).
- eval_ (pure compose <*> step t <*> rtrn b0 <*> rtrn a0). 
eval_ (apply (step t) (apply (rtrn b0) (rtrn a0))). constructor.  finish_with CIH.
- eval_ (apply (apply (apply (pure compose) t) (step v)) (rtrn a0)).
 eval_ (apply t (apply (step v) (rtrn a0))). finish_with CIH. 
- eval_ (apply (apply (apply (pure compose) t) v) (step w)). 
eval_  (apply t (apply v (step w))).  finish_with CIH. Qed.

Lemma partial_applicative_homomorphism: forall {a b} (v : a -> b) (x : a),
   Eqp (apply (pure v) (pure x)) (pure (v x)).
Proof. cofix CIH. intros. eval_ (pure v <*> pure x). Qed.


Lemma partial_applicative_interchange: forall {a b}(u : Partial (a -> b)) (y : a)
  , Eqp (apply u (pure y)) (apply (pure (fun z : a -> b => z y)) u).
Proof. cofix CIH. intros. destruct u.
- eval_ (rtrn b0 <*> pure y). 
eval_ (pure (fun z : a -> b => z y) <*> rtrn b0).
- eval_ (pure (fun z : a -> b => z y) <*> step u). eval_ (apply (step u) (pure y)). 
finish_with CIH. Qed.

Lemma partial_applicative_pure_map: forall {a b} (g: a -> b) (x: Partial a),
Eqp (map g x) (apply (pure g) x).
Proof. cofix CIH.  intros. 
destruct x.
eval_ ((map g (rtrn a0))).
eval_ (apply (pure g) (rtrn a0)).
eval_ (map g (step x)). 
eval_ (apply (pure g) (step x)). finish_with CIH. Qed.

(* Some of the monad axioms *)
Theorem bindleft_identity : forall A B (a : A) (f : A -> Partial B),
  Eqp (bind f (rtrn a)) (f a).
Proof. 
intros. eval_ (bind f (rtrn a)). destruct (f a); apply eqp_refl. Qed.

Theorem bindright_identity : forall A (m : Partial A),
  Eqp (bind ret m) m.
Proof. cofix CIH.  intros.   
eval_ (bind ret m).  destruct m.  apply eqp_refl. finish_with CIH. Qed.

Theorem bind_assoc : forall A B C (m : Partial A) 
(f : A -> Partial B) (g : B -> Partial C),
  Eqp (bind g (bind  f m)) (bind (fun x => bind g (f x)) m).
Proof. cofix CIH.  
intros. destruct m. eval_ ((bind (fun x : A => bind g (f x))
     (rtrn a))).  eval_ (bind g (bind f (rtrn a))).
eval_ (bind g (bind f (step m))). eval_ (bind (fun x : A => bind g (f x))
     (step m)). constructor. finish_with CIH.  Qed.

Theorem partial_bind_map: forall {a b} (x : Partial a) (f : a -> b),
     Eqp (map f x)  (bind (fun y => pure (f y)) x).
Proof. cofix CIH.  
intros. eval_ (map f x);
eval_ (bind (fun y : a => pure (f y)) x). destruct x. 
eval_ (pure (f a0)). constructor.  finish_with CIH. Qed. 











 
