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

CoInductive bisim A : Partial A -> Partial A -> Prop :=
| BisimRtrn : forall x, bisim (rtrn x) (rtrn x)
| BisimStepL : forall m1 m2, bisim m1 m2 -> bisim (step m1) m2
| BisimStepR : forall m1 m2, bisim m1 m2 -> bisim m1 (step m2).

Section park_principle.
Variable A : Type.
Variable P : Partial A -> Partial A -> Prop.

Hypothesis H : forall m1 m2, P m1 m2
    -> match m1, m2 with
         | rtrn x1, rtrn x2 => x1 = x2
         | step m1', step m2' => P m1' m2'
         | step m1', _ => P m1' m2
         | _, step m2' => P m1 m2'
       end.

Theorem park_principle : forall m1 m2, P m1 m2 -> bisim m1 m2.
Proof. cofix CIH.
intros. destruct m1.
destruct m2.
apply H in H0. rewrite H0. constructor.
apply H in H0. apply CIH in H0. constructor. assumption.
destruct m2.
apply H in H0. apply CIH in H0. constructor. assumption.
constructor. constructor. apply H in H0. apply CIH in H0. assumption.
Qed.
End park_principle.

Theorem partial_bisim_frob : forall A (m1 m2 : Partial A),
  bisim (frob m1) (frob m2) -> bisim m1 m2.
Proof. intros. assert (frob m1 = m1). rewrite frob_eq. reflexivity.
assert (frob m2 = m2). rewrite frob_eq. reflexivity. rewrite <- H0. rewrite <- H1. assumption. Qed.

Theorem bisim_refl : forall A (m : Partial A), bisim m m.
Proof. intros. apply (park_principle (fun m1 m2 => m1 = m2)).
- destruct m1. 
    + destruct m2. 
     * intros. inversion H. reflexivity.
     * intros. inversion H.
    + destruct m2.
     * intros. inversion H.
     * intros. inversion H. reflexivity.
- reflexivity. Qed.


(* Functor axioms *) 
Theorem map_id: forall A (m: Partial A), bisim (map id m) m.
intros. apply (park_principle (fun m1 m2 => m1 = map id m2)).
intros. rewrite H.  destruct m2;  reflexivity; reflexivity. reflexivity. Qed.

Theorem map_assoc: forall A B C (m: Partial A) (f: A -> B) (g: B -> C), 
bisim (map (g <<< f) m) (map g (map f m)).
Proof.
intros. 
apply (park_principle (fun m1 m2 => (exists m,
    m1 = map (f>>>g) m 
 /\ m2 = (map g (map f m))
  \/ m1 = m2))).
intros. crush. destruct x.
- reflexivity.
- exists x. left. split; reflexivity.
- destruct m2. reflexivity. exists x. right; reflexivity.
- exists m. left. split; reflexivity. 
Qed.

Definition pure A (x: A):= rtrn x.
Lemma partial_applicative_identity: forall  {a} (v : Partial a), bisim (apply (pure id) v) v.
Proof. intros.
apply (park_principle (fun m1 m2 => (m1 = apply (pure id) m2))). crush.
intros. destruct m2. reflexivity. 
- reflexivity.
- reflexivity. Qed.
Notation "f <*> g" := (apply f g) (at level 28, left associativity) .


Lemma partial_applicative_composition {a b c}  (t : Partial (b -> c)) (v : Partial (a -> b)) (w : Partial a)
    : bisim (pure compose <*> t <*> v <*> w)  (t <*> (v <*> w)).
Proof. 
apply (park_principle (fun m1 m2 => (exists (m3:Partial (b -> c)) (m4:Partial (a -> b)) (m5: Partial a),
    m1 = (pure compose <*> m3 <*> m4 <*> m5)
 /\ m2 = (m3 <*> (m4 <*> m5))
  \/ m1 = m2))).
crush. destruct x1.  destruct x0. destruct x.
- auto.

-  exists x. exists (rtrn b0). exists (rtrn a0). auto.
- exists x. exists x0. exists (rtrn a0). left; auto.
- exists x. exists x0. exists x1. left; auto.
- destruct m2. auto. exists t. exists v. exists w. auto.
- exists t. exists v. exists w. left; auto. Qed. 

Lemma partial_applicative_homomorphism {a b} (v : a -> b) (x : a)
  : bisim (apply (pure v) (pure x)) (pure (v x)).
  Proof.
apply (park_principle (fun m1 m2 => (exists m,
    m1 = apply (pure v) (pure m)
 /\ m2 = pure (v m)
  \/ m1 = m2))). 
  crush. intros. destruct m2. - reflexivity.
  - exists x.  auto.
  - exists x. auto. Qed.
  
 Lemma partial_applicative_interchange {a b}(u : Partial (a -> b)) (y : a)
  : bisim (apply u (pure y)) (apply (pure (fun z : a -> b => z y)) u).
Proof. 
apply (park_principle (fun m1 m2 => (exists m,
    m1 = apply m (pure y)
 /\ m2 = apply (pure (fun z : a -> b => z y)) m
  \/ m1 = m2))).
crush. destruct x.
- reflexivity.
- exists x. left. split; auto.
- destruct m2. auto. exists x. right; auto.
- exists u; left; split; auto. Qed.

Lemma partial_applicative_pure_map {a b} (g: a -> b) (x: Partial a): 
bisim (map g x) (apply (pure g) x).
Proof. 
apply (park_principle (fun m1 m2 => (exists m,
    m1 = (map g m)
 /\ m2 = apply (pure g) m
  \/ m1 = m2))).
crush. destruct x0.
- reflexivity.
- exists x0. auto.
- destruct m2; auto. exists x0. auto.
- exists x. auto. Qed.

(* Some of the monad axioms *)
Theorem bindleft_identity : forall A B (a : A) (f : A -> Partial B),
  bisim (bind f (rtrn a)) (f a).
Proof. intros. apply partial_bisim_frob. simpl. destruct (f a); simpl; apply bisim_refl. Qed.

Theorem bindright_identity : forall A (m : Partial A),
  bisim (bind ret m) m.
Proof. intros. apply (park_principle (fun m1 m2 => m1 = bind ret m2)).
crush. destruct m2. crush. auto. auto.
Qed.


Theorem bind_assoc : forall A B C (m : Partial A) (f : A -> Partial B) (g : B -> Partial C),
  bisim (bind g (bind  f m)) (bind (fun x => bind g (f x)) m).
Proof. 
intros.
 apply (park_principle (fun m1 m2 => (exists m,
    m1 = bind g (bind f m)
    /\ m2 = bind (fun x => bind g (f x) ) m)
  \/ m1 = m2)).
intros. crush. destruct x. destruct (f a). crush. destruct (g b). auto. auto.
crush. eauto. destruct m2. auto. auto. eauto. 
Qed.

Theorem partial_bind_map {a b} (x : Partial a) (f : a -> b)
    : bisim (map f x)  (bind (fun y => pure (f y)) x).
Proof.
apply (park_principle (fun m1 m2 => (exists m,
    m1 = (map f m)
    /\ m2 = (bind (fun y : a => pure (f y)) m))
  \/ m1 = m2)).
crush. destruct x0. crush.
- left; eauto.
- destruct m2; repeat eauto.
- left; eauto. Qed.

