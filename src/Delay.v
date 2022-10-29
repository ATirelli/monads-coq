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

Lemma eqp_equal: forall {A} (x: Partial A), Eqp x x. 
Proof. cofix CIH. intros.  destruct x. 
apply eqp_value with (a:=a); constructor. constructor. apply CIH. Qed. 



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
apply eqp_equal.
destruct H0. inversion H0. inversion H1.
destruct H2. destruct H3. inversion H2.
rewrite H0. apply eqp_equal.

apply H in H0. destruct H0. destruct H0. destruct H0. 
apply eqp_value with (a:=x); assumption.
destruct H0. destruct H0. destruct H0. destruct H0. inversion H0.
inversion H0.

apply H in H0. destruct H0. destruct H0. destruct H0. 
apply eqp_value with (a:=x); assumption.
destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
rewrite H0. rewrite H1. constructor. apply CIH. assumption. 

rewrite H0. apply eqp_equal. Qed.
End park_principle.

Theorem partial_eqp_frob : forall A (m1 m2 : Partial A),
  Eqp (frob m1) (frob m2) -> Eqp m1 m2.
Proof. intros. assert (frob m1 = m1). rewrite frob_eq. reflexivity.
assert (frob m2 = m2). rewrite frob_eq. reflexivity. 
rewrite <- H0. rewrite <- H1. assumption. Qed.

Ltac eval_ R :=  rewrite frob_eq with (x:=R); simpl; try (apply eqp_equal).
Ltac finish_with R := try constructor; try (apply eqp_equal); apply R.

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
intros. eval_ (bind f (rtrn a)). destruct (f a); apply eqp_equal. Qed.

Theorem bindright_identity : forall A (m : Partial A),
  Eqp (bind ret m) m.
Proof. cofix CIH.  intros.   
eval_ (bind ret m).  destruct m.  apply eqp_equal. finish_with CIH. Qed.

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











 
