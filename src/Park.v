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
| eqp_step : forall (x y:Partial A), Eqp x y -> Eqp (step x) (step y)
| eqp_equal: forall (x :Partial A), Eqp x x.

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
inversion H0. destruct  H1. inversion H1. inversion H2.
constructor.
destruct H0. inversion H0. inversion H1.
destruct H2. destruct H3. inversion H2.
rewrite H0. constructor.

apply H in H0. destruct H0. destruct H0. destruct H0. 
apply eqp_value with (a:=x); assumption.
destruct H0. destruct H0. destruct H0. destruct H0. inversion H0.
inversion H0.

apply H in H0. destruct H0. destruct H0. destruct H0. 
apply eqp_value with (a:=x); assumption.
destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
rewrite H0. rewrite H1. constructor. apply CIH. assumption. 

rewrite H0. constructor. Qed.
End park_principle.

Theorem partial_eqp_frob : forall A (m1 m2 : Partial A),
  Eqp (frob m1) (frob m2) -> Eqp m1 m2.
Proof. intros. assert (frob m1 = m1). rewrite frob_eq. reflexivity.
assert (frob m2 = m2). rewrite frob_eq. reflexivity. 
rewrite <- H0. rewrite <- H1. assumption. Qed.

(* Functor axioms *) 
Theorem map_id: forall A (m: Partial A), Eqp (map id m) m.
intros. apply (park_principle (fun m1 m2 => m1 = map id m2)).
intros. rewrite H. right. right. destruct m2.
- rewrite frob_eq with (x:=rtrn a).  Admitted . 

